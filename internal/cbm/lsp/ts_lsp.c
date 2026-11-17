/*
 * ts_lsp.c — TypeScript / JavaScript / JSX / TSX hybrid LSP type resolver.
 *
 * Phase 2 v1.0 resolver. Covers:
 *   - Categories 1–4: param type inference, return type propagation, method chaining,
 *                     multi-return / destructuring.
 *   - Categories 7–10: object literal property typing, type aliases, class field/method
 *                      dispatch (including `this`/`super`), interface dispatch.
 *   - Category 11 (partial): explicit/implicit generic instantiation via TEMPLATE types.
 *   - Category 12 (partial): hand-curated stdlib seeds (Promise, Array, Map, Set, etc.).
 *   - Category 13: optional chaining `obj?.member()` propagates type through.
 *   - Category 14: `await p` unwraps `Promise<T>` → T.
 *   - Category 15 (partial): `typeof` narrowing inside `if`/ternary.
 *   - Category 16: union member access tries each branch.
 *   - Category 17: literal types (string/number/bool literal types map to BUILTIN).
 *   - Category 20: imports surface `module.symbol` resolution against the registry.
 *   - Category 25: emits unresolved-call diagnostics (confidence 0).
 *
 * Cross-file (Phase 3) merges defs project-wide before per-file resolution; see
 * cbm_batch_ts_lsp_cross.
 *
 * Conventions (mirrors c_lsp / go_lsp):
 *   - Persistent results use ctx->arena; temporary walk/index buffers use tracked allocations.
 *   - ts_emit_resolved_call requires a non-NULL enclosing_func_qn — calls outside any
 *     function (module top-level) are not emitted.
 *   - eval_depth caps at TS_LSP_MAX_EVAL_DEPTH to defend against pathological recursion.
 */

#include "ts_lsp.h"
#include "ts_proof.h"
#include "lsp_work.h"
#include "../../../src/foundation/platform.h"
#include "../helpers.h"
#include "../js_this.h"
#include "../../../src/foundation/log.h"
#include "../../../src/foundation/mem_core.h"
#include <limits.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* TEST HOOK: full per-file cross-registry builds (stdlib + every cross-file
 * def registered + finalized, per file). This is the sequential-mode quadratic
 * that ground an 81k-file TS corpus for hours — the shared-registry dispatch
 * must keep it at ZERO; any nonzero count means a resolve path regressed to
 * the per-file build. */
static _Atomic long g_ts_full_reg_builds;
long cbm_ts_full_registry_builds(void) {
    return atomic_load(&g_ts_full_reg_builds);
}
void cbm_ts_full_registry_builds_reset(void) {
    atomic_store(&g_ts_full_reg_builds, 0);
}

/* Dynamic work budget for parse_ts_type_text (thread-local, reset at every
 * per-file/per-build entry point). The type-text parser is self-recursive
 * over string SLICES and re-derives lengths per call, so an adversarial or
 * generated type text can cost far more than its bytes suggest. Instead of
 * a fixed depth cap, the total work SCALES WITH THE INPUT: budget =
 * 1M + 64 x source_len units, each call charging 1 + slice_len/16 — i.e.
 * total scanned bytes are bounded at ~1024x the source size, generous
 * enough that no real-world file ever hits it. CBM_TS_TYPE_BUDGET (absolute
 * units) overrides. On exhaustion: WARN once per window, then return
 * UNKNOWN — the same graceful degradation the parser already uses for
 * constructs it does not model. -1 = unlimited (no entry point armed it). */
static _Thread_local long g_ts_type_budget = -1;
static _Thread_local bool g_ts_type_budget_warned;
#ifdef CBM_ENABLE_TEST_SEAMS
static _Thread_local unsigned long g_ts_signature_lookup_work;
static _Thread_local int g_ts_max_member_lookup_steps;
static _Thread_local int g_ts_max_method_lookup_steps;
static _Thread_local int g_ts_max_walk_depth;
#endif

static void ts_type_budget_reset(size_t source_len) {
    const char *e = cbm_runtime_getenv("CBM_TS_TYPE_BUDGET");
    if (e && e[0]) {
        long v = atol(e);
        g_ts_type_budget = (v > 0) ? v : -1;
    } else {
        g_ts_type_budget = 1000000 + (long)source_len * 64;
    }
    g_ts_type_budget_warned = false;
}

/* Bumped on every degraded eval return (depth cap or budget exhaustion). An
 * evaluation whose subtree bumped this counter must NOT be memoized: its value
 * embeds the degradation, and first-eval-wins would freeze it for call sites
 * that could have evaluated the node fully. */
static _Thread_local unsigned long g_ts_eval_degraded;

/* Expression-type memo (per file): node.id -> evaluated CBMType.
 *
 * ts_signature_for_call re-evaluates a call's argument expressions while
 * resolving overloads, and boolean/spread chains re-enter the same
 * subexpression once per enclosing alternative — the TS suite's
 * objectSpreadRepeatedComplexity.js builds a union of 2^(n-1) members and
 * measured 11+ s for a 3.6 KB file while emitting the same 5-node graph
 * v0.9.0 emits in 0.14 s. Expression types are position-pure within a file
 * pass (one node = one scope path, and the per-file walk is single-threaded
 * and deterministic), so one eval per node is the correct semantics, not a
 * cache trade-off. Degraded results are never stored (see
 * g_ts_eval_degraded). Arena-backed, linear-probed, power-of-two capacity;
 * grows by rehash and dies with the file pass. */
typedef struct TsEvalMemo {
    const void **keys; /* TSNode.id; NULL = empty slot */
    const CBMType **vals;
    uint32_t cap;
    uint32_t count;
} TsEvalMemo;

static uint32_t ts_memo_slot(const TsEvalMemo *m, const void *id) {
    uint64_t x = (uint64_t)(uintptr_t)id;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    uint32_t i = (uint32_t)x & (m->cap - 1);
    while (m->keys[i] && m->keys[i] != id)
        i = (i + 1) & (m->cap - 1);
    return i;
}

static const CBMType *ts_memo_get(const TsEvalMemo *m, const void *id) {
    if (!m || !m->cap)
        return NULL;
    uint32_t i = ts_memo_slot(m, id);
    return m->keys[i] ? m->vals[i] : NULL;
}

static void ts_memo_put(TSLSPContext *ctx, const void *id, const CBMType *t) {
    TsEvalMemo *m = ctx->eval_memo;
    if (!m) {
        m = (TsEvalMemo *)cbm_arena_alloc(ctx->arena, sizeof(*m));
        if (!m)
            return;
        m->cap = 1024;
        m->count = 0;
        m->keys = (const void **)cbm_arena_alloc(ctx->arena, m->cap * sizeof(*m->keys));
        m->vals = (const CBMType **)cbm_arena_alloc(ctx->arena, m->cap * sizeof(*m->vals));
        if (!m->keys || !m->vals)
            return;
        memset(m->keys, 0, m->cap * sizeof(*m->keys));
        memset(m->vals, 0, m->cap * sizeof(*m->vals));
        ctx->eval_memo = m;
    }
    if (m->count * 10 >= m->cap * 7) { /* grow at 70% load */
        TsEvalMemo bigger = {0};
        bigger.cap = m->cap * 2;
        bigger.keys = (const void **)cbm_arena_alloc(ctx->arena, bigger.cap * sizeof(*bigger.keys));
        bigger.vals =
            (const CBMType **)cbm_arena_alloc(ctx->arena, bigger.cap * sizeof(*bigger.vals));
        if (!bigger.keys || !bigger.vals)
            return; /* keep serving from the full table; stores stop */
        memset(bigger.keys, 0, bigger.cap * sizeof(*bigger.keys));
        memset(bigger.vals, 0, bigger.cap * sizeof(*bigger.vals));
        for (uint32_t i = 0; i < m->cap; i++) {
            if (!m->keys[i])
                continue;
            uint32_t j = ts_memo_slot(&bigger, m->keys[i]);
            bigger.keys[j] = m->keys[i];
            bigger.vals[j] = m->vals[i];
        }
        bigger.count = m->count;
        *m = bigger; /* old arrays stay in the arena */
    }
    uint32_t i = ts_memo_slot(m, id);
    if (!m->keys[i]) {
        m->keys[i] = id;
        m->vals[i] = t;
        m->count++;
    }
}

#ifdef CBM_ENABLE_TEST_SEAMS
/* Complexity-regression seam: expose the thread's remaining eval budget and
 * the warned flag after a cbm_run_ts_lsp call. Budget units consumed are a
 * deterministic work counter — the memo turns the spread-bomb class from
 * O(2^n) evals into O(nodes), which tests assert without wall-clock. */
long cbm_ts_lsp_test_budget_remaining(void) {
    return g_ts_type_budget;
}
bool cbm_ts_lsp_test_budget_warned(void) {
    return g_ts_type_budget_warned;
}
unsigned long cbm_ts_lsp_test_signature_lookup_work(void) {
    return g_ts_signature_lookup_work;
}
int cbm_ts_lsp_test_max_walk_depth(void) {
    return g_ts_max_walk_depth;
}

int cbm_ts_lsp_test_max_member_lookup_steps(void) {
    return g_ts_max_member_lookup_steps;
}
int cbm_ts_lsp_test_max_method_lookup_steps(void) {
    return g_ts_max_method_lookup_steps;
}
#endif

#define TS_LSP_MAX_EVAL_DEPTH 64
#define TS_LSP_FIELD_LEN(s) ((uint32_t)(sizeof(s) - 1))

// Tree-sitter grammar entry points for the three TS dialects (compiled into the binary).
extern const TSLanguage *tree_sitter_typescript(void);
extern const TSLanguage *tree_sitter_tsx(void);
extern const TSLanguage *tree_sitter_javascript(void);

// ── Forward declarations ──────────────────────────────────────────────────────

static const CBMType *parse_ts_type_text(CBMArena *arena, const char *text, const char *module_qn);
static void process_node(TSLSPContext *ctx, TSNode node);
static void process_function_body(TSLSPContext *ctx, TSNode body, const char *func_qn,
                                  const char *class_qn);
static const CBMType *type_of_identifier(TSLSPContext *ctx, const char *name);

static const CBMType *lookup_member_type(TSLSPContext *ctx, const CBMType *recv, const char *name);
static const CBMRegisteredFunc *lookup_method(TSLSPContext *ctx, const CBMType *recv,
                                              const char *method_name);
typedef struct TSLookupState TSLookupState;
static const CBMRegisteredFunc *lookup_method_at(TSLSPContext *ctx, const CBMType *recv,
                                                 const char *method_name, int depth,
                                                 TSLookupState *state);
static char *node_text(TSLSPContext *ctx, TSNode node);

// Collect a node's children into an arena array via a single O(n) cursor pass.
// Returns NULL (and sets *out_n=0) for a childless node or on OOM. Use this in
// place of the `for (i=0; i<count; i++) ts_node_child(node, i)` idiom: in
// tree-sitter ts_node_child(node, i) is O(i), so that loop is O(n²) on a wide
// node — e.g. a program root holding hundreds of thousands of top-level nodes
// (the reallyLargeFile.ts fixture is 583K lines of comment markup → 583K
// children, which made the per-file LSP passes run for ~133 minutes).
static TSNode *collect_children(CBMArena *arena, TSNode node, uint32_t *out_n) {
    uint32_t nc = ts_node_child_count(node);
    *out_n = 0;
    if (nc == 0)
        return NULL;
    TSNode *kids = (TSNode *)cbm_arena_alloc(arena, (size_t)nc * sizeof(TSNode));
    if (!kids)
        return NULL;
    uint32_t kn = 0;
    TSTreeCursor cur = ts_tree_cursor_new(node);
    if (ts_tree_cursor_goto_first_child(&cur)) {
        do {
            kids[kn++] = ts_tree_cursor_current_node(&cur);
        } while (kn < nc && ts_tree_cursor_goto_next_sibling(&cur));
    }
    ts_tree_cursor_delete(&cur);
    *out_n = kn;
    return kids;
}
static const CBMType *simplify_type(TSLSPContext *ctx, const CBMType *t);
static const CBMType *unwrap_passthrough_template(const CBMType *t);

// ── Helpers ───────────────────────────────────────────────────────────────────

static char *node_text(TSLSPContext *ctx, TSNode node) {
    return cbm_node_text(ctx->arena, node, ctx->source);
}

static bool node_kind_is(TSNode node, const char *kind) {
    if (ts_node_is_null(node))
        return false;
    return strcmp(ts_node_type(node), kind) == 0;
}

static bool ts_is_function_declaration(TSNode node) {
    return node_kind_is(node, "function_declaration") ||
           node_kind_is(node, "generator_function_declaration");
}

static bool ts_is_function_value(TSNode node) {
    return node_kind_is(node, "arrow_function") || node_kind_is(node, "function_expression") ||
           node_kind_is(node, "function") || node_kind_is(node, "generator_function");
}

/* Record only syntactic module/namespace bindings, not members or callables
 * inside bodies. This keeps the registry's flat object-method names from
 * supplying a free function's target or return type. */
static void ts_collect_module_callables(TSLSPContext *ctx, TSNode node, const char *module_qn) {
    if (ts_node_is_null(node) || !module_qn)
        return;
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "program") == 0 ||
        (strcmp(kind, "statement_block") == 0 &&
         node_kind_is(ts_node_parent(node), "internal_module")) ||
        strcmp(kind, "export_statement") == 0 || strcmp(kind, "ambient_declaration") == 0 ||
        strcmp(kind, "lexical_declaration") == 0 || strcmp(kind, "variable_declaration") == 0) {
        TSTreeCursor cursor = ts_tree_cursor_new(node);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                ts_collect_module_callables(ctx, ts_tree_cursor_current_node(&cursor), module_qn);
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
        return;
    }
    if (strcmp(kind, "expression_statement") == 0) {
        TSNode child = ts_node_named_child(node, 0);
        if (node_kind_is(child, "internal_module"))
            ts_collect_module_callables(ctx, child, module_qn);
        return;
    }
    if (strcmp(kind, "internal_module") == 0) {
        TSNode name = ts_node_child_by_field_name(node, "name", TS_LSP_FIELD_LEN("name"));
        TSNode body = ts_node_child_by_field_name(node, "body", TS_LSP_FIELD_LEN("body"));
        if (!ts_node_is_null(name)) {
            const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", module_qn, node_text(ctx, name));
            ts_collect_module_callables(ctx, body, qn);
        }
        return;
    }
    if (strcmp(kind, "variable_declarator") == 0) {
        TSNode value = ts_node_child_by_field_name(node, "value", TS_LSP_FIELD_LEN("value"));
        if (!ts_is_function_value(value))
            return;
    } else if (!ts_is_function_declaration(node) &&
               strcmp(kind, "function_signature") != 0) {
        return;
    }
    TSNode name = ts_node_child_by_field_name(node, "name", TS_LSP_FIELD_LEN("name"));
    if (node_kind_is(name, "identifier")) {
        const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", module_qn, node_text(ctx, name));
        cbm_scope_bind(ctx->module_callables, qn, cbm_type_unknown());
    }
}

static void ts_prepare_module_callables(TSLSPContext *ctx, TSNode root) {
    if (!ctx->module_callables) {
        ctx->module_callables = cbm_scope_push(ctx->arena, NULL);
        ts_collect_module_callables(ctx, root, ctx->module_qn);
    }
}

static bool ts_is_module_callable(TSLSPContext *ctx, const char *name) {
    if (!ctx->module_qn || !ctx->module_callables || !name)
        return false;
    const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, name);
    return cbm_scope_lookup_local(ctx->module_callables, qn) != NULL;
}

/* Resolve the named class at the actual expression, rather than the class
 * whose body the walker entered. In particular a class expression inside a
 * method has its own `this`, even during early return-type inference. */
static const char *ts_class_qn(TSLSPContext *ctx, TSNode cls) {
    if (!ctx->module_qn || ts_node_is_null(cls) ||
        ts_node_is_null(ts_node_child_by_field_name(cls, "name", TS_LSP_FIELD_LEN("name"))))
        return NULL;
    const char *chain = NULL;
    for (TSNode cur = cls; !ts_node_is_null(cur); cur = ts_node_parent(cur)) {
        if (!node_kind_is(cur, "class_declaration") && !node_kind_is(cur, "class") &&
            !node_kind_is(cur, "abstract_class_declaration"))
            continue;
        TSNode name = ts_node_child_by_field_name(cur, "name", TS_LSP_FIELD_LEN("name"));
        char *text = ts_node_is_null(name) ? NULL : node_text(ctx, name);
        if (text && text[0])
            chain = chain ? cbm_arena_sprintf(ctx->arena, "%s.%s", text, chain) : text;
    }
    return chain ? cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, chain) : NULL;
}

static const CBMType *ts_this_type(TSLSPContext *ctx, TSNode node) {
    TSNode cls;
    CBMJsThis binding = cbm_js_this_binding(node, &cls);
    if (binding != CBM_JS_THIS_INSTANCE)
        return cbm_type_unknown();
    const char *qn = ts_class_qn(ctx, cls);
    return qn ? cbm_type_named(ctx->arena, qn) : cbm_type_unknown();
}

// Find the first named child of `node` whose kind matches one of the listed kinds.
static TSNode find_first_kind(TSNode node, const char *kind) {
    if (ts_node_is_null(node))
        return node;
    uint32_t nc = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode c = ts_node_named_child(node, i);
        if (!ts_node_is_null(c) && strcmp(ts_node_type(c), kind) == 0)
            return c;
    }
    TSNode null_node = {0};
    return null_node;
}

/* `reason` carries the name written at the site when it differs from the
 * callee's leaf (`bar()` through `import { foo as bar }`): the pipeline joins an
 * alias strategy by that name instead of by the callee QN's last segment. */
static void ts_emit_resolved_call_reason_at(TSLSPContext *ctx, const char *callee_qn,
                                            const char *strategy, float confidence,
                                            const char *reason, TSNode site) {
    if (!ctx || !ctx->resolved_calls || !callee_qn || !ctx->enclosing_func_qn)
        return;
    CBMResolvedCall rc = {0};
    rc.caller_qn = ctx->enclosing_func_qn;
    rc.callee_qn = callee_qn;
    rc.strategy = strategy ? strategy : "lsp_ts";
    rc.confidence = confidence;
    rc.reason = reason;
    rc.kind = CBM_RESOLVED_INVOCATION;
    if (!ts_node_is_null(site)) {
        rc.site_start_byte = ts_node_start_byte(site);
        rc.site_end_byte = ts_node_end_byte(site);
    }
    cbm_resolvedcall_push(ctx->resolved_calls, ctx->arena, rc);
}

static void ts_emit_resolved_call_at(TSLSPContext *ctx, const char *callee_qn, const char *strategy,
                                     float confidence, TSNode site) {
    ts_emit_resolved_call_reason_at(ctx, callee_qn, strategy, confidence, NULL, site);
}

static void ts_emit_resolved_reference_reason(TSLSPContext *ctx, const char *callee_qn,
                                              const char *strategy, float confidence,
                                              const char *reason, TSNode site) {
    if (!ctx || !ctx->resolved_calls || !callee_qn || !ctx->enclosing_func_qn ||
        ts_node_is_null(site)) {
        return;
    }
    CBMResolvedCall rc = {0};
    rc.caller_qn = ctx->enclosing_func_qn;
    rc.callee_qn = callee_qn;
    rc.strategy = strategy ? strategy : "lsp_ts_value_reference";
    rc.confidence = confidence;
    rc.reason = reason;
    rc.kind = CBM_RESOLVED_CALL_REFERENCE;
    rc.site_start_byte = ts_node_start_byte(site);
    rc.site_end_byte = ts_node_end_byte(site);
    cbm_resolvedcall_push(ctx->resolved_calls, ctx->arena, rc);
}

static void ts_emit_resolved_reference(TSLSPContext *ctx, const char *callee_qn,
                                       const char *strategy, float confidence, TSNode site) {
    ts_emit_resolved_reference_reason(ctx, callee_qn, strategy, confidence, NULL, site);
}

static void ts_emit_unresolved_call_at(TSLSPContext *ctx, const char *expr_text, const char *reason,
                                       TSNode site) {
    if (!ctx || !ctx->resolved_calls || !ctx->enclosing_func_qn)
        return;
    CBMResolvedCall rc = {0};
    rc.caller_qn = ctx->enclosing_func_qn;
    rc.callee_qn = expr_text ? expr_text : "?";
    rc.strategy = "lsp_unresolved";
    rc.confidence = 0.0f;
    rc.reason = reason;
    rc.kind = CBM_RESOLVED_INVOCATION;
    if (!ts_node_is_null(site)) {
        rc.site_start_byte = ts_node_start_byte(site);
        rc.site_end_byte = ts_node_end_byte(site);
    }
    cbm_resolvedcall_push(ctx->resolved_calls, ctx->arena, rc);
}

// Parse a textual TS type into a CBMType. Pragmatic v1: handle the common cases
// (identifier, qualified.identifier, T[], T<U,V>, Promise<T>, T | U, T & U, predefined).
// Anything more complex falls back to NAMED with the original text.
//
// Trims leading whitespace, leading ":" (TS type-annotation prefix produced by
// `cbm_node_text` on a `type_annotation` AST node), and trailing whitespace/`;`.
static const CBMType *parse_ts_type_text(CBMArena *arena, const char *text, const char *module_qn) {
    if (!text || !text[0])
        return cbm_type_unknown();

    // Strip leading whitespace, then a leading ':' (type annotation), then more whitespace.
    while (*text == ' ' || *text == '\t' || *text == '\n' || *text == '\r')
        text++;
    if (*text == ':')
        text++;
    while (*text == ' ' || *text == '\t' || *text == '\n' || *text == '\r')
        text++;

    size_t len = strlen(text);
    while (len > 0 && (text[len - 1] == ' ' || text[len - 1] == '\t' || text[len - 1] == '\n' ||
                       text[len - 1] == '\r' || text[len - 1] == ';' || text[len - 1] == ','))
        len--;
    if (len == 0)
        return cbm_type_unknown();

    /* Dynamic budget (see g_ts_type_budget): charge proportional to this
     * slice; on exhaustion degrade to UNKNOWN instead of grinding. */
    if (g_ts_type_budget >= 0) {
        g_ts_type_budget -= 1 + (long)(len / 16);
        if (g_ts_type_budget < 0) {
            if (!g_ts_type_budget_warned) {
                g_ts_type_budget_warned = true;
                fprintf(stderr,
                        "  [tslsp] type-text parse budget exhausted (module %s); "
                        "returning unknown\n",
                        module_qn ? module_qn : "?");
            }
            return cbm_type_unknown();
        }
    }

    // Function type `(params) => returnType` (TS function type literal).
    if (text[0] == '(') {
        int depth = 0;
        size_t close = (size_t)-1;
        for (size_t i = 0; i < len; i++) {
            if (text[i] == '(')
                depth++;
            else if (text[i] == ')') {
                depth--;
                if (depth == 0) {
                    close = i;
                    break;
                }
            }
        }
        if (close == (size_t)-1)
            return cbm_type_unknown();
        size_t after = close + 1;
        while (after < len && (text[after] == ' ' || text[after] == '\t'))
            after++;
        if (after + 2 <= len && text[after] == '=' && text[after + 1] == '>') {
            // Parse return type.
            const char *ret_text = text + after + 2;
            const CBMType *ret = parse_ts_type_text(arena, ret_text, module_qn);

            // Parse params: split by top-level commas, each "name: type" or just "type".
            const char *fn_param_names[16] = {0};
            const CBMType *fn_param_types[16] = {0};
            int pc = 0;
            const char *params_text = text + 1;
            size_t params_len = close - 1;
            if (params_len > 0) {
                size_t start = 0;
                int pdepth = 0;
                for (size_t i = 0; i <= params_len && pc < 15; i++) {
                    char c = (i < params_len) ? params_text[i] : ',';
                    if (c == '(' || c == '<' || c == '[')
                        pdepth++;
                    else if (c == ')' || c == '>' || c == ']')
                        pdepth--;
                    else if (c == ',' && pdepth == 0) {
                        if (i > start) {
                            char *part = cbm_arena_strndup(arena, params_text + start, i - start);
                            char *colon = strchr(part, ':');
                            if (colon) {
                                *colon = '\0';
                                const char *nm = part;
                                while (*nm == ' ' || *nm == '\t')
                                    nm++;
                                size_t nl = strlen(nm);
                                while (nl > 0 && (nm[nl - 1] == ' ' || nm[nl - 1] == '?'))
                                    nl--;
                                fn_param_names[pc] = cbm_arena_strndup(arena, nm, nl);
                                fn_param_types[pc] =
                                    parse_ts_type_text(arena, colon + 1, module_qn);
                            } else {
                                fn_param_names[pc] = cbm_arena_sprintf(arena, "_%d", pc);
                                fn_param_types[pc] = parse_ts_type_text(arena, part, module_qn);
                            }
                            pc++;
                        }
                        start = i + 1;
                    }
                }
            }
            fn_param_names[pc] = NULL;
            fn_param_types[pc] = NULL;
            const CBMType *rets[2] = {ret, NULL};
            return cbm_type_func(arena, fn_param_names, fn_param_types, rets);
        }
        // Parens without arrow → return UNKNOWN.
        return cbm_type_unknown();
    }

    // Object type literal `{...}` and other unhandled — return UNKNOWN.
    if (text[0] == '{')
        return cbm_type_unknown();

    // TS polymorphic `this` return type: emit a TYPE_PARAM("this") sentinel that
    // ts_eval_expr_type / lookup_method substitute back to the actual receiver at
    // call site. Used by fluent-builder patterns: `class C { a(): this { ... } }`.
    if (len == 4 && memcmp(text, "this", 4) == 0) {
        return cbm_type_type_param(arena, "this");
    }

    // Conditional type `T extends U ? X : Y` — split on top-level " extends "
    // (followed downstream by " ? " and " : "). Detection: must have all three
    // keywords at depth 0, in order.
    {
        int depth = 0;
        size_t ext_pos = (size_t)-1;
        size_t q_pos = (size_t)-1;
        size_t colon_pos = (size_t)-1;
        for (size_t i = 0; i < len; i++) {
            char c = text[i];
            if (c == '<' || c == '[' || c == '(')
                depth++;
            else if (c == '>' || c == ']' || c == ')')
                depth--;
            if (depth != 0)
                continue;
            if (ext_pos == (size_t)-1 && i > 0 && text[i] == ' ' && i + 9 <= len &&
                memcmp(text + i, " extends ", 9) == 0) {
                ext_pos = i;
                i += 8;
                continue;
            }
            if (ext_pos != (size_t)-1 && q_pos == (size_t)-1 && i + 3 <= len && text[i] == ' ' &&
                text[i + 1] == '?' && text[i + 2] == ' ') {
                q_pos = i;
                i += 2;
                continue;
            }
            if (q_pos != (size_t)-1 && colon_pos == (size_t)-1 && i + 3 <= len && text[i] == ' ' &&
                text[i + 1] == ':' && text[i + 2] == ' ') {
                colon_pos = i;
                break;
            }
        }
        if (ext_pos != (size_t)-1 && q_pos != (size_t)-1 && colon_pos != (size_t)-1) {
            char *check_text = cbm_arena_strndup(arena, text, ext_pos);
            char *extends_text =
                cbm_arena_strndup(arena, text + ext_pos + 9, q_pos - (ext_pos + 9));
            char *true_text = cbm_arena_strndup(arena, text + q_pos + 3, colon_pos - (q_pos + 3));
            char *false_text =
                cbm_arena_strndup(arena, text + colon_pos + 3, len - (colon_pos + 3));
            const CBMType *check = parse_ts_type_text(arena, check_text, module_qn);
            const CBMType *extends = parse_ts_type_text(arena, extends_text, module_qn);
            const CBMType *true_branch = parse_ts_type_text(arena, true_text, module_qn);
            const CBMType *false_branch = parse_ts_type_text(arena, false_text, module_qn);
            return cbm_type_conditional(arena, check, extends, true_branch, false_branch);
        }
    }

    // `infer X` — emit CBM_TYPE_INFER. Only meaningful inside conditional `extends`
    // patterns; emitted standalone here and matched later by eval_conditional.
    if (len > 6 && memcmp(text, "infer ", 6) == 0) {
        const char *rest = text + 6;
        while (*rest == ' ' || *rest == '\t')
            rest++;
        const char *end = rest;
        while (*end && *end != ' ' && *end != '\t')
            end++;
        char *name = cbm_arena_strndup(arena, rest, (size_t)(end - rest));
        return cbm_type_infer(arena, name);
    }

    // `keyof T` — emit CBM_TYPE_KEYOF for downstream evaluation.
    if (len > 6 && memcmp(text, "keyof ", 6) == 0) {
        const char *rest = text + 6;
        while (*rest == ' ' || *rest == '\t')
            rest++;
        char *rest_term = cbm_arena_strdup(arena, rest);
        const CBMType *operand = parse_ts_type_text(arena, rest_term, module_qn);
        return cbm_type_keyof(arena, operand);
    }

    // `typeof X` in type position — emit CBM_TYPE_TYPEOF_QUERY.
    if (len > 7 && memcmp(text, "typeof ", 7) == 0) {
        const char *rest = text + 7;
        while (*rest == ' ' || *rest == '\t')
            rest++;
        return cbm_type_typeof_query(
            arena, module_qn ? cbm_arena_sprintf(arena, "%s.%s", module_qn, rest) : rest);
    }

    // Tuple `[T, U]` — first char `[`, balanced. Build TUPLE.
    if (text[0] == '[' && len >= 2 && text[len - 1] == ']') {
        const char *inner_text = text + 1;
        size_t inner_len = len - 2;
        const CBMType *elems[16] = {0};
        int ec = 0;
        size_t start = 0;
        int depth = 0;
        for (size_t i = 0; i <= inner_len && ec < 15; i++) {
            char c = (i < inner_len) ? inner_text[i] : ',';
            if (c == '<' || c == '[')
                depth++;
            else if (c == '>' || c == ']')
                depth--;
            else if (c == ',' && depth == 0) {
                char *part = cbm_arena_strndup(arena, inner_text + start, i - start);
                elems[ec++] = parse_ts_type_text(arena, part, module_qn);
                start = i + 1;
            }
        }
        elems[ec] = NULL;
        return cbm_type_tuple(arena, elems, ec);
    }

    // Top-level UNION ` | ` or INTERSECTION ` & ` — split at depth 0 (outside <>, []).
    {
        int depth = 0;
        const CBMType *members[16] = {0};
        int mc = 0;
        size_t start = 0;
        bool is_union = false;
        bool is_inter = false;
        for (size_t i = 0; i < len; i++) {
            char c = text[i];
            if (c == '<' || c == '[')
                depth++;
            else if (c == '>' || c == ']')
                depth--;
            else if (depth == 0 && (c == '|' || c == '&') && i > 0 &&
                     (text[i - 1] == ' ' || text[i - 1] == '\t')) {
                if (mc < 15) {
                    char *part = cbm_arena_strndup(arena, text + start, i - start);
                    members[mc++] = parse_ts_type_text(arena, part, module_qn);
                }
                if (c == '|')
                    is_union = true;
                else
                    is_inter = true;
                start = i + 1;
            }
        }
        if (mc > 0 && (is_union || is_inter)) {
            // Cap mirrors the in-loop guard: members[16] holds at most 15
            // real entries + the trailing NULL sentinel. Without this guard,
            // a union/intersection with >=16 members overflows the array
            // (UBSan: index 16 out of bounds for 'const CBMType *[16]').
            if (mc < 15) {
                char *part = cbm_arena_strndup(arena, text + start, len - start);
                members[mc++] = parse_ts_type_text(arena, part, module_qn);
            }
            members[mc] = NULL;
            return is_union ? cbm_type_union(arena, members, mc)
                            : cbm_type_intersection(arena, members, mc);
        }
    }

    // Builtins / predefined type keywords.
    static const char *const builtins[] = {
        "string", "number", "boolean",   "bigint", "any",    "unknown", "void",
        "never",  "null",   "undefined", "object", "symbol", NULL,
    };
    for (int i = 0; builtins[i]; i++) {
        size_t bl = strlen(builtins[i]);
        if (len == bl && memcmp(text, builtins[i], bl) == 0) {
            return cbm_type_builtin(arena, builtins[i]);
        }
    }

    // Trailing `[]` → Array<elem>. Strip and recurse.
    if (len >= 2 && text[len - 1] == ']' && text[len - 2] == '[') {
        char *inner = cbm_arena_strndup(arena, text, len - 2);
        const CBMType *elem = parse_ts_type_text(arena, inner, module_qn);
        const CBMType *args[2] = {elem, NULL};
        return cbm_type_template(arena, "Array", args, 1);
    }

    // Generic instantiation `Foo<...>` — find balanced `<...>` at the end.
    if (len > 2 && text[len - 1] == '>') {
        int depth = 0;
        size_t open = (size_t)-1;
        for (size_t i = len; i-- > 0;) {
            char c = text[i];
            if (c == '>')
                depth++;
            else if (c == '<') {
                depth--;
                if (depth == 0) {
                    open = i;
                    break;
                }
            }
        }
        if (open != (size_t)-1 && open > 0) {
            char *base = cbm_arena_strndup(arena, text, open);
            const char *args_text = text + open + 1;
            size_t args_len = (len - 1) - (open + 1);
            // Split args by top-level commas.
            const CBMType *args[16] = {0};
            int arg_count = 0;
            size_t start = 0;
            int adepth = 0;
            for (size_t i = 0; i <= args_len && arg_count < 15; i++) {
                char c = (i < args_len) ? args_text[i] : ',';
                if (c == '<')
                    adepth++;
                else if (c == '>')
                    adepth--;
                else if (c == ',' && adepth == 0) {
                    char *part = cbm_arena_strndup(arena, args_text + start, i - start);
                    args[arg_count++] = parse_ts_type_text(arena, part, module_qn);
                    start = i + 1;
                }
            }
            args[arg_count] = NULL;
            // Qualify project-local generic bases against the current module so
            // `Container<number>` becomes TEMPLATE("test.main.Container", [number]).
            // Stdlib bases (Array, Promise, Map, Set, Object) stay bare so they match
            // the stdlib registration.
            const char *qualified_base = base;
            static const char *const stdlib_names[] = {
                "Array",
                "Promise",
                "Map",
                "Set",
                "WeakMap",
                "WeakSet",
                "ReadonlyArray",
                "Iterable",
                "Iterator",
                "Generator",
                "AsyncIterable",
                "AsyncIterator",
                "AsyncGenerator",
                "Object",
                "String",
                "Number",
                "Boolean",
                "BigInt",
                "Symbol",
                "Function",
                "Date",
                "RegExp",
                "Error",
                "Partial",
                "Required",
                "Readonly",
                "Pick",
                "Omit",
                "Record",
                "Exclude",
                "Extract",
                "NonNullable",
                "Parameters",
                "ReturnType",
                "Awaited",
                "ThisType",
                "InstanceType",
                "ConstructorParameters",
                "Uppercase",
                "Lowercase",
                "Capitalize",
                "Uncapitalize",
                "NodeList",
                "HTMLCollection",
                NULL,
            };
            bool is_stdlib = false;
            for (int sl = 0; stdlib_names[sl]; sl++) {
                if (strcmp(base, stdlib_names[sl]) == 0) {
                    is_stdlib = true;
                    break;
                }
            }
            if (!is_stdlib && module_qn && strchr(base, '.') == NULL && base[0] >= 'A' &&
                base[0] <= 'Z') {
                qualified_base = cbm_arena_sprintf(arena, "%s.%s", module_qn, base);
            }
            return cbm_type_template(arena, qualified_base, args, arg_count);
        }
    }

    // Qualified identifier (a.b.c) → NAMED with whatever text we have. Caller-side lookup
    // will check both the QN as-given and module-qualified variants.
    if (module_qn && strchr(text, '.') == NULL) {
        // Stdlib names stay bare so they match the stdlib registration QNs.
        static const char *const bare_stdlib_names[] = {
            "Array",
            "Promise",
            "Map",
            "Set",
            "WeakMap",
            "WeakSet",
            "ReadonlyArray",
            "Iterable",
            "Iterator",
            "Generator",
            "AsyncIterable",
            "AsyncIterator",
            "AsyncGenerator",
            "Object",
            "String",
            "Number",
            "Boolean",
            "BigInt",
            "Symbol",
            "Function",
            "Date",
            "RegExp",
            "Error",
            "Math",
            "JSON",
            "console",
            // DOM essentials
            "Element",
            "HTMLElement",
            "Document",
            "Window",
            "Node",
            "EventTarget",
            "Event",
            "Response",
            "Request",
            "Headers",
            "URL",
            "URLSearchParams",
            "FormData",
            "Blob",
            "File",
            "NodeList",
            "HTMLCollection",
            "JSX",
            NULL,
        };
        char *terminated = cbm_arena_strndup(arena, text, len);
        if (!terminated)
            return cbm_type_unknown();
        for (int i = 0; bare_stdlib_names[i]; i++) {
            if (strcmp(terminated, bare_stdlib_names[i]) == 0) {
                return cbm_type_named(arena, terminated);
            }
        }
        // Bare uppercase identifier — qualify against the current module if it looks
        // like a TypeIdent. Lower-case names are likely params/values, fall back.
        if ((terminated[0] >= 'A' && terminated[0] <= 'Z')) {
            const char *qn = cbm_arena_sprintf(arena, "%s.%s", module_qn, terminated);
            return cbm_type_named(arena, qn);
        }
        return cbm_type_named(arena, terminated);
    }
    return cbm_type_named(arena, cbm_arena_strndup(arena, text, len));
}

typedef struct {
    const char *module_qn;
} CBMTSLSPSignatureParserContext;

static const CBMType *cbm_ts_lsp_parse_signature_param_text(CBMArena *arena, const char *text,
                                                            void *parser_ctx) {
    const CBMTSLSPSignatureParserContext *ctx = (const CBMTSLSPSignatureParserContext *)parser_ctx;
    const char *module_qn = ctx && ctx->module_qn ? ctx->module_qn : "";
    return parse_ts_type_text(arena, text, module_qn);
}

// Return param-type CBMType array from a CBMDefinition's param_types text array.
static const CBMType **parse_param_types_array(CBMArena *arena, const char **texts,
                                               const char *module_qn) {
    if (!texts)
        return NULL;
    int count = 0;
    while (texts[count])
        count++;
    if (count == 0)
        return NULL;
    const CBMType **arr =
        (const CBMType **)cbm_arena_alloc(arena, (size_t)(count + 1) * sizeof(const CBMType *));
    if (!arr)
        return NULL;
    for (int i = 0; i < count; i++) {
        arr[i] = parse_ts_type_text(arena, texts[i], module_qn);
    }
    arr[count] = NULL;
    return arr;
}

// ── Partial structural subtyping (relater) ────────────────────────────────────
//
// Answers `is A assignable to B?` for the subset of TS types we support. Modeled
// loosely on typescript-go's `internal/checker/relater.go` but limited to the cases
// that matter for call-edge resolution. NOT a full type-checker — many edge cases
// return false rather than recursing into undecidable territory.
//
// Used by:
// - Conditional type evaluation (`T extends U ? X : Y`)
// - Generic constraint checks (`<T extends Animal>`)
// - Future overload-by-types refinement
//
// Rules implemented:
// - any/unknown/never on either side: liberal acceptance
// - NAMED == NAMED: equal QN OR walk the source's `embedded_types` (extends chain)
// - BUILTIN: identical name; LITERAL("string", X) ≤ BUILTIN("string"), etc.
// - TUPLE: same arity, element-wise
// - UNION source: every member assignable to target
// - UNION target: source assignable to any member
// - INTERSECTION source: any member assignable to target
// - INTERSECTION target: source assignable to all members
// - FUNC: param contravariance, return covariance, parameter-count tolerance
// - TEMPLATE: same name + each arg assignable
// - TYPE_PARAM: same name → true; otherwise check constraint when known
// - ALIAS: resolve and recurse
// - any UNKNOWN type: false
//
// Cycle/depth guard: max 64 nested calls. Pair-cache keyed on pointer identity
// (sufficient given arena-stable types within a single resolver pass).

#define TS_RELATER_MAX_DEPTH 64
#define TS_RELATER_CACHE_SIZE 256

typedef struct {
    const CBMType *a;
    const CBMType *b;
    int8_t result; // -1 = unknown, 0 = false, 1 = true
} TSRelaterCacheSlot;

static int ts_is_assignable_inner(TSLSPContext *ctx, const CBMType *a, const CBMType *b, int depth,
                                  TSRelaterCacheSlot *cache);

static const CBMType *ts_relater_unwrap(const CBMType *t) {
    if (!t)
        return t;
    if (t->kind == CBM_TYPE_ALIAS)
        return cbm_type_resolve_alias(t);
    return t;
}

static bool ts_builtin_compatible(const char *a, const char *b) {
    if (!a || !b)
        return false;
    if (strcmp(a, b) == 0)
        return true;
    // `any` and `unknown` accept anything (handled by caller before this).
    return false;
}

static bool ts_literal_promotes_to_builtin(const CBMType *lit, const CBMType *bi) {
    if (!lit || lit->kind != CBM_TYPE_TS_LITERAL || !lit->data.literal_ts.tag)
        return false;
    if (!bi || bi->kind != CBM_TYPE_BUILTIN || !bi->data.builtin.name)
        return false;
    return strcmp(lit->data.literal_ts.tag, bi->data.builtin.name) == 0;
}

static bool ts_class_extends(TSLSPContext *ctx, const char *sub_qn, const char *super_qn,
                             int depth) {
    if (!ctx || !sub_qn || !super_qn)
        return false;
    if (depth > TS_RELATER_MAX_DEPTH)
        return false;
    if (strcmp(sub_qn, super_qn) == 0)
        return true;
    const CBMRegisteredType *rt = cbm_registry_lookup_type(ctx->registry, sub_qn);
    if (!rt || !rt->embedded_types)
        return false;
    for (int i = 0; rt->embedded_types[i]; i++) {
        if (ts_class_extends(ctx, rt->embedded_types[i], super_qn, depth + 1))
            return true;
    }
    return false;
}

static int ts_is_assignable_inner(TSLSPContext *ctx, const CBMType *a, const CBMType *b, int depth,
                                  TSRelaterCacheSlot *cache) {
    if (depth > TS_RELATER_MAX_DEPTH)
        return 0;
    if (!a || !b)
        return 0;

    // Cache probe (pointer identity is sufficient — arena-stable within a resolver pass).
    int slot = (int)((((uintptr_t)a >> 4) ^ ((uintptr_t)b >> 4)) & (TS_RELATER_CACHE_SIZE - 1));
    if (cache[slot].a == a && cache[slot].b == b && cache[slot].result >= 0) {
        return cache[slot].result;
    }

    a = ts_relater_unwrap(a);
    b = ts_relater_unwrap(b);
    if (!a || !b)
        return 0;

    // any/unknown/never short-circuits.
    if (b->kind == CBM_TYPE_BUILTIN && b->data.builtin.name) {
        if (strcmp(b->data.builtin.name, "any") == 0 ||
            strcmp(b->data.builtin.name, "unknown") == 0)
            return 1;
    }
    if (a->kind == CBM_TYPE_BUILTIN && a->data.builtin.name) {
        if (strcmp(a->data.builtin.name, "any") == 0)
            return 1;
        if (strcmp(a->data.builtin.name, "never") == 0)
            return 1;
    }

    int result = 0;

    // Source unions: every member must be assignable to target.
    if (a->kind == CBM_TYPE_UNION && a->data.union_type.members) {
        result = 1;
        for (int i = 0; i < a->data.union_type.count; i++) {
            if (!ts_is_assignable_inner(ctx, a->data.union_type.members[i], b, depth + 1, cache)) {
                result = 0;
                break;
            }
        }
        goto done;
    }
    // Target unions: source assignable to any member.
    if (b->kind == CBM_TYPE_UNION && b->data.union_type.members) {
        for (int i = 0; i < b->data.union_type.count; i++) {
            if (ts_is_assignable_inner(ctx, a, b->data.union_type.members[i], depth + 1, cache)) {
                result = 1;
                break;
            }
        }
        goto done;
    }
    // Source intersection: any member assignable to target.
    if (a->kind == CBM_TYPE_INTERSECTION && a->data.union_type.members) {
        for (int i = 0; i < a->data.union_type.count; i++) {
            if (ts_is_assignable_inner(ctx, a->data.union_type.members[i], b, depth + 1, cache)) {
                result = 1;
                break;
            }
        }
        goto done;
    }
    // Target intersection: source assignable to all members.
    if (b->kind == CBM_TYPE_INTERSECTION && b->data.union_type.members) {
        result = 1;
        for (int i = 0; i < b->data.union_type.count; i++) {
            if (!ts_is_assignable_inner(ctx, a, b->data.union_type.members[i], depth + 1, cache)) {
                result = 0;
                break;
            }
        }
        goto done;
    }

    if (a->kind != b->kind) {
        // Cross-kind rules: LITERAL → BUILTIN, NAMED-class → NAMED-class via extends.
        if (a->kind == CBM_TYPE_TS_LITERAL && b->kind == CBM_TYPE_BUILTIN) {
            result = ts_literal_promotes_to_builtin(a, b) ? 1 : 0;
            goto done;
        }
        // TYPE_PARAM source: check constraint if known.
        if (a->kind == CBM_TYPE_TYPE_PARAM) {
            // Without registered constraint info available here, treat as "unknown" (fail).
            result = 0;
            goto done;
        }
        result = 0;
        goto done;
    }

    // Same-kind cases.
    switch (a->kind) {
    case CBM_TYPE_NAMED: {
        const char *aqn = a->data.named.qualified_name;
        const char *bqn = b->data.named.qualified_name;
        if (!aqn || !bqn) {
            result = 0;
            break;
        }
        if (strcmp(aqn, bqn) == 0) {
            result = 1;
            break;
        }
        // class hierarchy: A extends B?
        result = ts_class_extends(ctx, aqn, bqn, 0) ? 1 : 0;
        break;
    }
    case CBM_TYPE_BUILTIN:
        result = ts_builtin_compatible(a->data.builtin.name, b->data.builtin.name) ? 1 : 0;
        break;
    case CBM_TYPE_TS_LITERAL:
        if (a->data.literal_ts.tag && b->data.literal_ts.tag &&
            strcmp(a->data.literal_ts.tag, b->data.literal_ts.tag) == 0 &&
            a->data.literal_ts.value && b->data.literal_ts.value &&
            strcmp(a->data.literal_ts.value, b->data.literal_ts.value) == 0) {
            result = 1;
        } else {
            result = 0;
        }
        break;
    case CBM_TYPE_TUPLE: {
        int ac = a->data.tuple.count;
        int bc = b->data.tuple.count;
        if (ac != bc) {
            result = 0;
            break;
        }
        result = 1;
        for (int i = 0; i < ac; i++) {
            if (!ts_is_assignable_inner(ctx, a->data.tuple.elems[i], b->data.tuple.elems[i],
                                        depth + 1, cache)) {
                result = 0;
                break;
            }
        }
        break;
    }
    case CBM_TYPE_TEMPLATE: {
        const char *an = a->data.template_type.template_name;
        const char *bn = b->data.template_type.template_name;
        if (!an || !bn || strcmp(an, bn) != 0) {
            result = 0;
            break;
        }
        int ac = a->data.template_type.arg_count;
        int bcount = b->data.template_type.arg_count;
        if (ac != bcount) {
            result = 0;
            break;
        }
        result = 1;
        for (int i = 0; i < ac; i++) {
            if (!ts_is_assignable_inner(ctx, a->data.template_type.template_args[i],
                                        b->data.template_type.template_args[i], depth + 1, cache)) {
                result = 0;
                break;
            }
        }
        break;
    }
    case CBM_TYPE_FUNC: {
        // Return covariance.
        const CBMType *aret = (a->data.func.return_types && a->data.func.return_types[0])
                                  ? a->data.func.return_types[0]
                                  : NULL;
        const CBMType *bret = (b->data.func.return_types && b->data.func.return_types[0])
                                  ? b->data.func.return_types[0]
                                  : NULL;
        if (aret && bret && !ts_is_assignable_inner(ctx, aret, bret, depth + 1, cache)) {
            result = 0;
            break;
        }
        // Param contravariance + arity tolerance.
        int ap = 0, bp = 0;
        if (a->data.func.param_types)
            while (a->data.func.param_types[ap])
                ap++;
        if (b->data.func.param_types)
            while (b->data.func.param_types[bp])
                bp++;
        if (ap > bp) {
            result = 0;
            break;
        } // source needs more params than target supplies
        result = 1;
        for (int i = 0; i < ap; i++) {
            if (!ts_is_assignable_inner(ctx, b->data.func.param_types[i],
                                        a->data.func.param_types[i], depth + 1, cache)) {
                result = 0;
                break;
            }
        }
        break;
    }
    case CBM_TYPE_TYPE_PARAM: {
        const char *an = a->data.type_param.name;
        const char *bn = b->data.type_param.name;
        result = (an && bn && strcmp(an, bn) == 0) ? 1 : 0;
        break;
    }
    default:
        result = 0;
        break;
    }

done:
    cache[slot].a = a;
    cache[slot].b = b;
    cache[slot].result = (int8_t)result;
    return result;
}

// Public entry point. Allocates a small per-call cache on the stack.
static bool ts_is_assignable(TSLSPContext *ctx, const CBMType *a, const CBMType *b) {
    if (!ctx || !a || !b)
        return false;
    TSRelaterCacheSlot cache[TS_RELATER_CACHE_SIZE];
    for (int i = 0; i < TS_RELATER_CACHE_SIZE; i++) {
        cache[i].a = NULL;
        cache[i].b = NULL;
        cache[i].result = -1;
    }
    return ts_is_assignable_inner(ctx, a, b, 0, cache) ? true : false;
}

// ── Type evaluation ───────────────────────────────────────────────────────────

// `infer X` constraint solver — pattern-matches `source` against `pattern` (which
// may contain CBM_TYPE_INFER nodes) and records bindings into a small fixed-size
// table. Returns true on full match, false otherwise. Bindings table is OWNED by
// caller (typically stack-allocated).
typedef struct {
    const char *name;
    const CBMType *binding;
} TSInferBinding;

#define TS_INFER_MAX 8

static bool match_with_infer(TSLSPContext *ctx, const CBMType *source, const CBMType *pattern,
                             TSInferBinding *binds, int *bind_count, int depth) {
    if (depth > 16 || !source || !pattern)
        return false;

    // Pattern is `infer X`: bind X to source.
    if (pattern->kind == CBM_TYPE_INFER) {
        if (*bind_count >= TS_INFER_MAX)
            return false;
        const char *nm = pattern->data.infer.name;
        if (!nm)
            return false;
        // Re-bind same name → require identical existing binding (else fail).
        for (int i = 0; i < *bind_count; i++) {
            if (binds[i].name && strcmp(binds[i].name, nm) == 0) {
                return ts_is_assignable(ctx, source, binds[i].binding) &&
                       ts_is_assignable(ctx, binds[i].binding, source);
            }
        }
        binds[*bind_count].name = nm;
        binds[*bind_count].binding = source;
        (*bind_count)++;
        return true;
    }

    // Same kind required for structural recursion.
    if (source->kind != pattern->kind) {
        // Non-INFER pattern with different kind: fall back to assignability.
        return ts_is_assignable(ctx, source, pattern);
    }

    switch (pattern->kind) {
    case CBM_TYPE_TEMPLATE: {
        const char *sn = source->data.template_type.template_name;
        const char *pn = pattern->data.template_type.template_name;
        if (!sn || !pn || strcmp(sn, pn) != 0)
            return false;
        int sc = source->data.template_type.arg_count;
        int pc = pattern->data.template_type.arg_count;
        if (sc != pc)
            return false;
        for (int i = 0; i < pc; i++) {
            if (!match_with_infer(ctx, source->data.template_type.template_args[i],
                                  pattern->data.template_type.template_args[i], binds, bind_count,
                                  depth + 1))
                return false;
        }
        return true;
    }
    case CBM_TYPE_TUPLE: {
        int sc = source->data.tuple.count;
        int pc = pattern->data.tuple.count;
        if (sc != pc)
            return false;
        for (int i = 0; i < pc; i++) {
            if (!match_with_infer(ctx, source->data.tuple.elems[i], pattern->data.tuple.elems[i],
                                  binds, bind_count, depth + 1))
                return false;
        }
        return true;
    }
    case CBM_TYPE_FUNC: {
        const CBMType *sret =
            source->data.func.return_types ? source->data.func.return_types[0] : NULL;
        const CBMType *pret =
            pattern->data.func.return_types ? pattern->data.func.return_types[0] : NULL;
        if (sret && pret && !match_with_infer(ctx, sret, pret, binds, bind_count, depth + 1))
            return false;
        // Param-by-param match (positionally).
        int sp = 0, pp = 0;
        if (source->data.func.param_types)
            while (source->data.func.param_types[sp])
                sp++;
        if (pattern->data.func.param_types)
            while (pattern->data.func.param_types[pp])
                pp++;
        if (sp != pp)
            return sp >= pp; // tolerate source having more params than pattern
        for (int i = 0; i < pp; i++) {
            if (!match_with_infer(ctx, source->data.func.param_types[i],
                                  pattern->data.func.param_types[i], binds, bind_count, depth + 1))
                return false;
        }
        return true;
    }
    default:
        return ts_is_assignable(ctx, source, pattern);
    }
}

// Substitute `infer X` bindings into a type tree (recursive).
static const CBMType *subst_infer_bindings(TSLSPContext *ctx, const CBMType *t,
                                           const TSInferBinding *binds, int bind_count, int depth) {
    if (!t || depth > 16 || bind_count == 0)
        return t;
    // TYPE_PARAM matching the bound name → replace with binding's type.
    if (t->kind == CBM_TYPE_TYPE_PARAM && t->data.type_param.name) {
        for (int i = 0; i < bind_count; i++) {
            if (binds[i].name && strcmp(binds[i].name, t->data.type_param.name) == 0) {
                return binds[i].binding;
            }
        }
        return t;
    }
    // NAMED matching the bound name (the parser may module-qualify single-letter
    // names like `U` to `module.U` since it doesn't know about active infer binds).
    // Match on the bare short name.
    if (t->kind == CBM_TYPE_NAMED && t->data.named.qualified_name) {
        const char *qn = t->data.named.qualified_name;
        const char *dot = strrchr(qn, '.');
        const char *bare = dot ? dot + 1 : qn;
        for (int i = 0; i < bind_count; i++) {
            if (binds[i].name && strcmp(binds[i].name, bare) == 0) {
                return binds[i].binding;
            }
        }
        return t;
    }
    if (t->kind == CBM_TYPE_TEMPLATE && t->data.template_type.template_args &&
        t->data.template_type.arg_count > 0) {
        int ac = t->data.template_type.arg_count;
        const CBMType **new_args = (const CBMType **)cbm_arena_alloc(
            ctx->arena, (size_t)(ac + 1) * sizeof(const CBMType *));
        if (!new_args)
            return t;
        for (int i = 0; i < ac; i++) {
            new_args[i] = subst_infer_bindings(ctx, t->data.template_type.template_args[i], binds,
                                               bind_count, depth + 1);
        }
        new_args[ac] = NULL;
        return cbm_type_template(ctx->arena, t->data.template_type.template_name, new_args, ac);
    }
    if (t->kind == CBM_TYPE_TUPLE && t->data.tuple.count > 0) {
        int n = t->data.tuple.count;
        const CBMType **new_elems = (const CBMType **)cbm_arena_alloc(
            ctx->arena, (size_t)(n + 1) * sizeof(const CBMType *));
        if (!new_elems)
            return t;
        for (int i = 0; i < n; i++) {
            new_elems[i] =
                subst_infer_bindings(ctx, t->data.tuple.elems[i], binds, bind_count, depth + 1);
        }
        new_elems[n] = NULL;
        return cbm_type_tuple(ctx->arena, new_elems, n);
    }
    return t;
}

// Walk a type tree to detect any CBM_TYPE_INFER nodes.
static bool contains_infer(const CBMType *t, int depth) {
    if (!t || depth > 32)
        return false;
    if (t->kind == CBM_TYPE_INFER)
        return true;
    if (t->kind == CBM_TYPE_TEMPLATE && t->data.template_type.template_args) {
        for (int i = 0; i < t->data.template_type.arg_count; i++) {
            if (contains_infer(t->data.template_type.template_args[i], depth + 1))
                return true;
        }
    }
    if (t->kind == CBM_TYPE_TUPLE && t->data.tuple.elems) {
        for (int i = 0; i < t->data.tuple.count; i++) {
            if (contains_infer(t->data.tuple.elems[i], depth + 1))
                return true;
        }
    }
    if (t->kind == CBM_TYPE_FUNC) {
        if (t->data.func.return_types) {
            for (int i = 0; t->data.func.return_types[i]; i++) {
                if (contains_infer(t->data.func.return_types[i], depth + 1))
                    return true;
            }
        }
        if (t->data.func.param_types) {
            for (int i = 0; t->data.func.param_types[i]; i++) {
                if (contains_infer(t->data.func.param_types[i], depth + 1))
                    return true;
            }
        }
    }
    return false;
}

// Evaluate a CBM_TYPE_CONDITIONAL `T extends U ? X : Y`. With distribution: when T is
// a UNION, evaluate per member and union the results. Uses the partial relater for
// the extends check.
static const CBMType *eval_conditional(TSLSPContext *ctx, const CBMType *t, int depth) {
    if (!t || t->kind != CBM_TYPE_CONDITIONAL || depth > 16)
        return t;
    const CBMType *check = t->data.conditional.check;
    const CBMType *extends = t->data.conditional.extends;
    const CBMType *tb = t->data.conditional.true_branch;
    const CBMType *fb = t->data.conditional.false_branch;
    if (!check || !extends)
        return t;

    // Distribution: when check is a UNION, evaluate per member and union results.
    if (check->kind == CBM_TYPE_UNION && check->data.union_type.members &&
        check->data.union_type.count > 0) {
        const CBMType **results = (const CBMType **)cbm_arena_alloc(
            ctx->arena, (size_t)(check->data.union_type.count + 1) * sizeof(const CBMType *));
        if (!results)
            return t;
        int n = 0;
        for (int i = 0; i < check->data.union_type.count; i++) {
            const CBMType *member = check->data.union_type.members[i];
            const CBMType *sub = cbm_type_conditional(ctx->arena, member, extends, tb, fb);
            results[n++] = eval_conditional(ctx, sub, depth + 1);
        }
        results[n] = NULL;
        if (n == 1)
            return results[0];
        return cbm_type_union(ctx->arena, results, n);
    }

    // `infer X` in extends pattern: pattern-match check against extends, capturing
    // bindings, then substitute them in the true_branch.
    if (contains_infer(extends, 0)) {
        TSInferBinding binds[TS_INFER_MAX] = {{0}};
        int bind_count = 0;
        if (match_with_infer(ctx, check, extends, binds, &bind_count, 0)) {
            return subst_infer_bindings(ctx, tb, binds, bind_count, 0);
        }
        return fb;
    }

    // Non-distributive: single resolution.
    bool yes = ts_is_assignable(ctx, check, extends);
    return yes ? tb : fb;
}

// Resolve a CBMType against the registry's alias chain when it's a NAMED type that's a
// pure alias (`type Foo = Bar`). Also evaluates inline conditional types.
static const CBMType *ts_awaited_type_at(TSLSPContext *ctx, const CBMType *value, int depth);

static const CBMType *simplify_type_at(TSLSPContext *ctx, const CBMType *t, int depth) {
    if (!t || !ctx || !ctx->registry)
        return t;
    if (depth >= 32)
        return cbm_type_unknown();
    if (t->kind == CBM_TYPE_TYPEOF_QUERY) {
        const char *name = t->data.typeof_query.expr;
        if (name && ctx->module_qn) {
            size_t n = strlen(ctx->module_qn);
            if (strncmp(name, ctx->module_qn, n) == 0 && name[n] == '.')
                name += n + 1;
        }
        /* A bare value follows the same lexical/import binding as a call.
         * Qualified expressions need their own proof; a leaf-name fallback
         * could bind an unrelated function. */
        if (!name || !name[0] ||
            strspn(name, "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$") !=
                strlen(name))
            return cbm_type_unknown();
        return simplify_type_at(ctx, type_of_identifier(ctx, name), depth + 1);
    }
    if (t->kind == CBM_TYPE_TEMPLATE && t->data.template_type.template_name &&
        t->data.template_type.arg_count == 1 && t->data.template_type.template_args) {
        const char *name = t->data.template_type.template_name;
        if (strcmp(name, "ReturnType") == 0) {
            const CBMType *fn =
                simplify_type_at(ctx, t->data.template_type.template_args[0], depth + 1);
            if (!fn || fn->kind != CBM_TYPE_FUNC || !fn->data.func.return_types ||
                !fn->data.func.return_types[0] || fn->data.func.return_types[1])
                return cbm_type_unknown();
            return simplify_type_at(ctx, fn->data.func.return_types[0], depth + 1);
        }
        if (strcmp(name, "Awaited") == 0)
            return ts_awaited_type_at(ctx, t->data.template_type.template_args[0], depth + 1);
    }
    if (t->kind == CBM_TYPE_CONDITIONAL) {
        const CBMType *evaluated = eval_conditional(ctx, t, 0);
        if (evaluated && evaluated != t)
            return simplify_type_at(ctx, evaluated, depth + 1);
        return t;
    }
    if (t->kind == CBM_TYPE_ALIAS)
        return cbm_type_resolve_alias(t);
    if (t->kind != CBM_TYPE_NAMED)
        return t;
    for (int i = 0; i < 16; i++) {
        if (!t || t->kind != CBM_TYPE_NAMED)
            return t;
        const CBMRegisteredType *rt =
            cbm_registry_lookup_type(ctx->registry, t->data.named.qualified_name);
        if (!rt || !rt->alias_of)
            return t;
        t = cbm_type_named(ctx->arena, rt->alias_of);
    }
    return t;
}

/* Await and async return adoption share the same bounded recursive unwrap. */
static const CBMType *ts_awaited_type_at(TSLSPContext *ctx, const CBMType *value, int depth) {
    value = simplify_type_at(ctx, value, depth + 1);
    while (value && value->kind == CBM_TYPE_TEMPLATE && value->data.template_type.template_name &&
           strcmp(value->data.template_type.template_name, "Promise") == 0 &&
           value->data.template_type.arg_count == 1 && value->data.template_type.template_args) {
        if (++depth >= 32)
            return cbm_type_unknown();
        value = simplify_type_at(ctx, value->data.template_type.template_args[0], depth);
    }
    return value;
}

static const CBMType *simplify_type(TSLSPContext *ctx, const CBMType *t) {
    return simplify_type_at(ctx, t, 0);
}

/* cbm_scope_lookup intentionally collapses an absent binding and an UNKNOWN
 * binding to the same type. Reference resolution needs the stronger question:
 * even an untyped local/parameter shadows an import and must block promotion. */
static const CBMScope *ts_scope_binding_owner(const CBMScope *scope, const char *name) {
    if (!name) {
        return NULL;
    }
    for (const CBMScope *s = scope; s; s = s->parent) {
        if (cbm_scope_lookup_local(s, name)) {
            return s;
        }
    }
    return NULL;
}

static bool ts_scope_has_binding(const CBMScope *scope, const char *name) {
    return ts_scope_binding_owner(scope, name) != NULL;
}

/* ── Reassigned locals ─────────────────────────────────────────────────
 *
 * A `let`, a `var` or a parameter can hold another object after an
 * assignment. One walk of the file records each name that an assignment
 * writes, with the function that holds the write. A binding whose name a
 * nested function writes is fixed to its annotation or a type proved by every
 * write (else unknown): the closure can run at any time. A binding written only in its own function
 * is a flow binding. The statement walk replaces its type at a straight-line assignment, makes it
 * unknown at any other write and at a loop that writes it, and a nested function or a pass outside
 * the walk reads its annotation (or unknown). A `const` is never a flow binding. */
typedef struct {
    const char *name;
    uint32_t start;
    uint32_t fn_start;
    uint32_t fn_end;
    TSNode value; /* exact simple-write RHS; null for an unproven pattern/update */
} TsAssignSite;

struct TsAssignSites {
    TsAssignSite *by_name;   /* sorted by (name, start) */
    TsAssignSite **by_start; /* the same sites, sorted by start */
    int count;
    bool complete; /* false: a write may be missing, so every write is a closure write */
    /* Every name a `var` declares, by the function it hoists to, sorted by
     * (fn_start, fn_end, start). */
    TsAssignSite *hoisted;
    int hoisted_count;
    TSNode root;
    TsAssignSite *shadows;
    int shadow_count;
    bool shadows_ready;
    bool shadows_complete;
};

typedef struct {
    const CBMVarBinding *binding; /* NULL: empty slot */
    const CBMType *declared;      /* annotation or uniform-write proof, or NULL */
    bool fixed;                   /* a closure writes it: the walk never updates it */
} TsFlowBinding;

struct TsFlowBindings {
    TsFlowBinding *slots;
    uint32_t cap; /* power of two */
    uint32_t count;
};

static bool ts_is_flow_function(TSNode node) {
    return ts_is_function_declaration(node) || ts_is_function_value(node) ||
           node_kind_is(node, "method_definition") || node_kind_is(node, "class_static_block") ||
           node_kind_is(node, "internal_module");
}

typedef struct {
    TsAssignSite *items;
    int count;
    int cap;
    bool failed;
} TsSiteVec;

static bool ts_write_wrapper(TSNode node) {
    return node_kind_is(node, "parenthesized_expression") ||
           node_kind_is(node, "non_null_expression") || node_kind_is(node, "as_expression") ||
           node_kind_is(node, "satisfies_expression") || node_kind_is(node, "type_assertion");
}

static TSNode ts_write_operand(TSNode node) {
    uint32_t count = ts_node_named_child_count(node);
    return count ? ts_node_named_child(node, node_kind_is(node, "type_assertion") ? count - 1 : 0)
                 : (TSNode){0};
}

static void ts_site_push(TSLSPContext *ctx, TsSiteVec *v, TSNode name, uint32_t fs, uint32_t fe) {
    if (v->failed)
        return;
    if (v->count == v->cap) {
        int cap = v->cap ? v->cap * 2 : 64;
        TsAssignSite *items =
            (TsAssignSite *)cbm_arena_alloc(ctx->arena, (size_t)cap * sizeof(*items));
        if (!items) {
            v->failed = true;
            return;
        }
        if (v->count)
            memcpy(items, v->items, (size_t)v->count * sizeof(*items));
        v->items = items;
        v->cap = cap;
    }
    char *text = node_text(ctx, name);
    if (!text) {
        v->failed = true;
        return;
    }
    TSNode target = name, parent = ts_node_parent(name), value = {0};
    while (ts_write_wrapper(parent) && ts_node_eq(ts_write_operand(parent), target)) {
        target = parent;
        parent = ts_node_parent(parent);
    }
    if (node_kind_is(parent, "assignment_expression") &&
        ts_node_eq(ts_node_child_by_field_name(parent, "left", 4), target))
        value = ts_node_child_by_field_name(parent, "right", 5);
    else if (node_kind_is(parent, "variable_declarator"))
        value = ts_node_child_by_field_name(parent, "value", 5);
    v->items[v->count++] = (TsAssignSite){.name = text,
                                          .start = ts_node_start_byte(name),
                                          .fn_start = fs,
                                          .fn_end = fe,
                                          .value = value};
}

/* Every identifier a destructuring target writes. Nesting past 64 levels
 * marks the set incomplete, which fails closed. */
static void ts_site_push_pattern(TSLSPContext *ctx, TsSiteVec *v, TSNode pattern, uint32_t fs,
                                 uint32_t fe, int depth) {
    while (ts_write_wrapper(pattern))
        pattern = ts_write_operand(pattern);
    if (ts_node_is_null(pattern))
        return;
    if (depth > 64) {
        v->failed = true;
        return;
    }
    const char *kind = ts_node_type(pattern);
    if (strcmp(kind, "identifier") == 0 ||
        strcmp(kind, "shorthand_property_identifier_pattern") == 0) {
        ts_site_push(ctx, v, pattern, fs, fe);
    } else if (strcmp(kind, "pair_pattern") == 0) {
        TSNode value = ts_node_child_by_field_name(pattern, "value", TS_LSP_FIELD_LEN("value"));
        ts_site_push_pattern(ctx, v, value, fs, fe, depth + 1);
    } else if (strcmp(kind, "assignment_pattern") == 0 ||
               strcmp(kind, "object_assignment_pattern") == 0) {
        ts_site_push_pattern(ctx, v,
                             ts_node_child_by_field_name(pattern, "left", TS_LSP_FIELD_LEN("left")),
                             fs, fe, depth + 1);
    } else if (strcmp(kind, "object_pattern") == 0 || strcmp(kind, "array_pattern") == 0 ||
               strcmp(kind, "rest_pattern") == 0 || strcmp(kind, "parenthesized_expression") == 0 ||
               strcmp(kind, "non_null_expression") == 0) {
        uint32_t count = ts_node_named_child_count(pattern);
        for (uint32_t i = 0; i < count; i++)
            ts_site_push_pattern(ctx, v, ts_node_named_child(pattern, i), fs, fe, depth + 1);
    }
}

/* Every var initializer writes its hoisted binding, including a repeated
 * declaration in the module or function body. An empty var adds no write. */
static void ts_site_visit_var(TSLSPContext *ctx, TsSiteVec *v, TsSiteVec *hoist,
                              const TSTreeCursor *cursor, TSNode node, uint32_t fs, uint32_t fe) {
    uint32_t count = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < count; i++) {
        TSNode decl = ts_node_named_child(node, i);
        if (!node_kind_is(decl, "variable_declarator"))
            continue;
        TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
        ts_site_push_pattern(ctx, hoist, name, fs, fe, 0);
        TSNode value = ts_node_child_by_field_name(decl, "value", TS_LSP_FIELD_LEN("value"));
        if (!ts_node_is_null(value))
            ts_site_push_pattern(ctx, v, name, fs, fe, 0);
    }
}

static void ts_site_visit(TSLSPContext *ctx, TsSiteVec *v, TsSiteVec *hoist,
                          const TSTreeCursor *cursor, TSNode node, uint32_t fs, uint32_t fe) {
    const char *kind = ts_node_type(node);
    if (kind[0] == 'v' && strcmp(kind, "variable_declaration") == 0) {
        ts_site_visit_var(ctx, v, hoist, cursor, node, fs, fe);
        return;
    }
    if (kind[0] == 'a' && (strcmp(kind, "assignment_expression") == 0 ||
                           strcmp(kind, "augmented_assignment_expression") == 0)) {
        ts_site_push_pattern(ctx, v,
                             ts_node_child_by_field_name(node, "left", TS_LSP_FIELD_LEN("left")),
                             fs, fe, 0);
    } else if (strcmp(kind, "update_expression") == 0) {
        ts_site_push_pattern(ctx, v, ts_node_named_child(node, 0), fs, fe, 0);
    } else if (kind[0] == 'f' && strcmp(kind, "for_in_statement") == 0) {
        /* `for (x of xs)` writes an existing binding. A header with a
         * `kind` (`for (const x of xs)`) declares x instead. */
        TSNode left = ts_node_child_by_field_name(node, "left", TS_LSP_FIELD_LEN("left"));
        TSNode decl_kind = ts_node_child_by_field_name(node, "kind", TS_LSP_FIELD_LEN("kind"));
        if (ts_node_is_null(decl_kind) && !node_kind_is(left, "lexical_declaration") &&
            !node_kind_is(left, "variable_declaration"))
            ts_site_push_pattern(ctx, v, left, fs, fe, 0);
        /* `for (var x of xs)` declares x in the function and writes it. */
        if (!ts_node_is_null(decl_kind) && node_kind_is(decl_kind, "var")) {
            ts_site_push_pattern(ctx, hoist, left, fs, fe, 0);
            ts_site_push_pattern(ctx, v, left, fs, fe, 0);
        }
    }
}

static int ts_site_fn_cmp(const void *pa, const void *pb) {
    const TsAssignSite *a = (const TsAssignSite *)pa;
    const TsAssignSite *b = (const TsAssignSite *)pb;
    if (a->fn_start != b->fn_start)
        return (a->fn_start > b->fn_start) - (a->fn_start < b->fn_start);
    if (a->fn_end != b->fn_end)
        return (a->fn_end > b->fn_end) - (a->fn_end < b->fn_end);
    return (a->start > b->start) - (a->start < b->start);
}

static int ts_site_name_cmp(const void *pa, const void *pb) {
    const TsAssignSite *a = (const TsAssignSite *)pa;
    const TsAssignSite *b = (const TsAssignSite *)pb;
    int by_name = strcmp(a->name, b->name);
    if (by_name)
        return by_name;
    return (a->start > b->start) - (a->start < b->start);
}

static int ts_site_start_cmp(const void *pa, const void *pb) {
    const TsAssignSite *a = *(const TsAssignSite *const *)pa;
    const TsAssignSite *b = *(const TsAssignSite *const *)pb;
    return (a->start > b->start) - (a->start < b->start);
}

/* One cursor walk of the file; no recursion over the tree. */
static void ts_collect_assign_sites(TSLSPContext *ctx, TSNode root) {
    if (ctx->assign_sites || !ctx->arena || ts_node_is_null(root))
        return;
    struct TsAssignSites *sites =
        (struct TsAssignSites *)cbm_arena_alloc(ctx->arena, sizeof(*sites));
    if (!sites)
        return;
    memset(sites, 0, sizeof(*sites));
    ctx->assign_sites = sites;
    sites->root = root;

    TsSiteVec v = {0};
    TsSiteVec hoist = {0};
    uint32_t inline_fns[2 * 32];
    uint32_t *fns = inline_fns;
    int fn_cap = 32;
    int fn_top = 0;
    fns[0] = 0;
    fns[1] = UINT32_MAX;
    fn_top = 1;
    TSTreeCursor cursor = ts_tree_cursor_new(root);
    for (bool done = false; !done && !v.failed;) {
        TSNode node = ts_tree_cursor_current_node(&cursor);
        TSNode called = node_kind_is(node, "call_expression")
                            ? ts_node_child_by_field_name(node, "function", 8)
                            : (TSNode){0};
        if (node_kind_is(node, "with_statement") ||
            (node_kind_is(node, "call_expression") && node_kind_is(called, "identifier") &&
             ts_node_end_byte(called) - ts_node_start_byte(called) == 4 &&
             memcmp(ctx->source + ts_node_start_byte(called), "eval", 4) == 0)) {
            v.failed = true;
            break;
        }
        ts_site_visit(ctx, &v, &hoist, &cursor, node, fns[2 * fn_top - 2], fns[2 * fn_top - 1]);
        bool fn = ts_is_flow_function(node);
        if (fn) {
            if (fn_top == fn_cap) {
                uint32_t *grown = (uint32_t *)cbm_arena_alloc(
                    ctx->arena, (size_t)fn_cap * 4 * sizeof(*grown));
                if (!grown) {
                    v.failed = true;
                    break;
                }
                memcpy(grown, fns, (size_t)fn_cap * 2 * sizeof(*fns));
                fns = grown;
                fn_cap *= 2;
            }
            fns[2 * fn_top] = ts_node_start_byte(node);
            fns[2 * fn_top + 1] = ts_node_end_byte(node);
            fn_top++;
        }
        if (ts_tree_cursor_goto_first_child(&cursor))
            continue;
        if (fn)
            fn_top--;
        for (;;) {
            if (ts_tree_cursor_goto_next_sibling(&cursor))
                break;
            if (!ts_tree_cursor_goto_parent(&cursor)) {
                done = true;
                break;
            }
            if (ts_is_flow_function(ts_tree_cursor_current_node(&cursor)))
                fn_top--;
        }
    }
    ts_tree_cursor_delete(&cursor);
    if (!v.failed && !hoist.failed && hoist.count) {
        qsort(hoist.items, (size_t)hoist.count, sizeof(*hoist.items), ts_site_fn_cmp);
        sites->hoisted = hoist.items;
        sites->hoisted_count = hoist.count;
    }
    if (v.failed)
        return; /* complete stays false: every writable binding is fixed */

    TsAssignSite **by_start = NULL;
    if (v.count) {
        qsort(v.items, (size_t)v.count, sizeof(*v.items), ts_site_name_cmp);
        by_start =
            (TsAssignSite **)cbm_arena_alloc(ctx->arena, (size_t)v.count * sizeof(*by_start));
        if (!by_start)
            return;
        for (int i = 0; i < v.count; i++)
            by_start[i] = &v.items[i];
        qsort(by_start, (size_t)v.count, sizeof(*by_start), ts_site_start_cmp);
    }
    sites->by_name = v.items;
    sites->by_start = by_start;
    sites->count = v.count;
    sites->complete = true;
}

/* 0: nothing writes name in the function being walked; 1: only that function
 * writes it; 2: a nested function writes it (or the site set is incomplete). */
static int ts_assign_writes(const TSLSPContext *ctx, const char *name) {
    const struct TsAssignSites *sites = ctx->assign_sites;
    if (!sites || !name)
        return 0;
    if (!sites->complete)
        return 2;
    int lo = 0;
    int hi = sites->count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        const TsAssignSite *s = &sites->by_name[mid];
        int c = strcmp(s->name, name);
        if (c < 0 || (c == 0 && s->start < ctx->fn_start))
            lo = mid + 1;
        else
            hi = mid;
    }
    int writes = 0;
    for (int i = lo; i < sites->count; i++) {
        const TsAssignSite *s = &sites->by_name[i];
        if (strcmp(s->name, name) != 0 || s->start >= ctx->fn_end)
            break;
        if (s->fn_start != ctx->fn_start || s->fn_end != ctx->fn_end)
            return 2;
        writes = 1;
    }
    return writes;
}

static uint32_t ts_flow_slot(const struct TsFlowBindings *set, const CBMVarBinding *b) {
    uint64_t x = (uint64_t)(uintptr_t)b;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    uint32_t i = (uint32_t)x & (set->cap - 1);
    while (set->slots[i].binding && set->slots[i].binding != b)
        i = (i + 1) & (set->cap - 1);
    return i;
}

static const TsFlowBinding *ts_flow_find(const TSLSPContext *ctx, const CBMVarBinding *b) {
    const struct TsFlowBindings *set = ctx->flow_bindings;
    if (!set || !set->cap || !b)
        return NULL;
    const TsFlowBinding *slot = &set->slots[ts_flow_slot(set, b)];
    return slot->binding ? slot : NULL;
}

static bool ts_flow_put(TSLSPContext *ctx, const CBMVarBinding *b, const CBMType *declared,
                        bool fixed) {
    struct TsFlowBindings *set = ctx->flow_bindings;
    if (!set) {
        set = (struct TsFlowBindings *)cbm_arena_alloc(ctx->arena, sizeof(*set));
        if (!set)
            return false;
        memset(set, 0, sizeof(*set));
        ctx->flow_bindings = set;
    }
    if (!set->cap || (set->count + 1) * 10 >= set->cap * 7) {
        uint32_t cap = set->cap ? set->cap * 2 : 64;
        TsFlowBinding *slots =
            (TsFlowBinding *)cbm_arena_alloc(ctx->arena, (size_t)cap * sizeof(*slots));
        if (!slots)
            return false;
        memset(slots, 0, (size_t)cap * sizeof(*slots));
        struct TsFlowBindings grown = {.slots = slots, .cap = cap, .count = set->count};
        for (uint32_t i = 0; i < set->cap; i++) {
            if (set->slots[i].binding)
                grown.slots[ts_flow_slot(&grown, set->slots[i].binding)] = set->slots[i];
        }
        *set = grown;
    }
    TsFlowBinding *slot = &set->slots[ts_flow_slot(set, b)];
    if (!slot->binding)
        set->count++;
    *slot = (TsFlowBinding){.binding = b, .declared = declared, .fixed = fixed};
    return true;
}

/* Bind name as a flow binding; one that cannot be recorded fails closed. */
static void ts_bind_flow(TSLSPContext *ctx, CBMScope *frame, const char *name,
                         const CBMType *type, const CBMType *declared, bool fixed) {
    const CBMType *floor = declared ? declared : cbm_type_unknown();
    cbm_scope_bind(frame, name, fixed ? floor : type);
    const CBMVarBinding *b = cbm_scope_lookup_local(frame, name);
    if (!b || !ts_flow_put(ctx, b, declared, fixed))
        cbm_scope_bind(frame, name, floor);
}

/* Bind one declared name in frame. `writable` is false for a `const`. */
static void ts_bind_local(TSLSPContext *ctx, CBMScope *frame, const char *name,
                          const CBMType *type, const CBMType *declared, bool writable) {
    if (!ctx || !frame || !name)
        return;
    if (!type)
        type = cbm_type_unknown();
    if (declared && cbm_type_is_unknown(declared))
        declared = NULL;
    int writes = writable ? ts_assign_writes(ctx, name) : 0;
    if (writes == 0) {
        cbm_scope_bind(frame, name, type);
        return;
    }
    ts_bind_flow(ctx, frame, name, type, declared, writes == 2);
}

/* True when owner is a frame of the function being walked. */
static bool ts_scope_in_function(const TSLSPContext *ctx, const CBMScope *owner) {
    for (const CBMScope *s = ctx->current_scope; s; s = s->parent) {
        if (s == owner)
            return true;
        if (s == ctx->fn_scope)
            return false;
    }
    return false;
}

/* The type a binding has at this point of the walk (see TsAssignSites). */
static const CBMType *ts_binding_type(TSLSPContext *ctx, const CBMScope *owner,
                                      const CBMVarBinding *b) {
    const CBMType *t = b->type ? b->type : cbm_type_unknown();
    const TsFlowBinding *flow = ts_flow_find(ctx, b);
    if (!flow || flow->fixed)
        return t;
    ctx->flow_reads++;
    if (ctx->flow_walk && ts_scope_in_function(ctx, owner))
        return t;
    return flow->declared ? flow->declared : cbm_type_unknown();
}

/* The nearest binding's type, or NULL when name is unbound. */
static const CBMType *ts_lookup_binding_type(TSLSPContext *ctx, const char *name) {
    if (!name)
        return NULL;
    for (const CBMScope *s = ctx->current_scope; s; s = s->parent) {
        const CBMVarBinding *b = cbm_scope_lookup_local(s, name);
        if (b)
            return ts_binding_type(ctx, s, b);
    }
    return NULL;
}

/* A write to an existing binding. A straight-line write in the frame that
 * owns the binding replaces its type. Any other write leaves the owner with
 * its annotation (or unknown); a straight-line write in a nearer frame also
 * binds the new type there, for the rest of that block. */
static void ts_flow_write(TSLSPContext *ctx, const char *name, const CBMType *value,
                          bool straight) {
    CBMScope *owner = (CBMScope *)ts_scope_binding_owner(ctx->current_scope, name);
    if (!owner)
        return; /* an import, a module callable or a global */
    const CBMVarBinding *b = cbm_scope_lookup_local(owner, name);
    const TsFlowBinding *flow = ts_flow_find(ctx, b);
    if (!flow) {
        /* Bound without a write check (a catch or loop variable, a reserved
         * name): a write from a nested function fixes it now. */
        int writes = ts_scope_in_function(ctx, owner) ? ts_assign_writes(ctx, name) : 2;
        if (writes == 2) {
            cbm_scope_bind(owner, name, cbm_type_unknown());
            b = cbm_scope_lookup_local(owner, name);
            if (b)
                (void)ts_flow_put(ctx, b, NULL, true);
            return;
        }
    }
    if (flow && flow->fixed)
        return;
    const CBMType *declared = flow ? flow->declared : NULL;
    const CBMType *floor = declared ? declared : cbm_type_unknown();
    const CBMType *next = (straight && value && !cbm_type_is_unknown(value)) ? value : floor;
    if (straight && owner == ctx->current_scope) {
        cbm_scope_bind(owner, name, next);
        if (!flow && !ts_flow_put(ctx, b, NULL, false))
            cbm_scope_bind(owner, name, floor);
        return;
    }
    cbm_scope_bind(owner, name, floor);
    if (straight)
        ts_bind_flow(ctx, ctx->current_scope, name, next, declared, false);
}

/* Every name a destructuring write targets loses its proof. */
static void ts_flow_write_pattern(TSLSPContext *ctx, TSNode pattern, int depth) {
    while (ts_write_wrapper(pattern))
        pattern = ts_write_operand(pattern);
    if (ts_node_is_null(pattern) || depth > 64)
        return;
    const char *kind = ts_node_type(pattern);
    if (strcmp(kind, "identifier") == 0 ||
        strcmp(kind, "shorthand_property_identifier_pattern") == 0) {
        ts_flow_write(ctx, node_text(ctx, pattern), NULL, false);
    } else if (strcmp(kind, "pair_pattern") == 0) {
        ts_flow_write_pattern(
            ctx, ts_node_child_by_field_name(pattern, "value", TS_LSP_FIELD_LEN("value")),
            depth + 1);
    } else if (strcmp(kind, "assignment_pattern") == 0 ||
               strcmp(kind, "object_assignment_pattern") == 0) {
        ts_flow_write_pattern(
            ctx, ts_node_child_by_field_name(pattern, "left", TS_LSP_FIELD_LEN("left")),
            depth + 1);
    } else if (strcmp(kind, "object_pattern") == 0 || strcmp(kind, "array_pattern") == 0 ||
               strcmp(kind, "rest_pattern") == 0 ||
               strcmp(kind, "parenthesized_expression") == 0) {
        uint32_t count = ts_node_named_child_count(pattern);
        for (uint32_t i = 0; i < count; i++)
            ts_flow_write_pattern(ctx, ts_node_named_child(pattern, i), depth + 1);
    }
}

/* Before a loop: a name the loop writes holds no single type in it. */
static void ts_flow_enter_loop(TSLSPContext *ctx, TSNode loop) {
    const struct TsAssignSites *sites = ctx->assign_sites;
    if (!sites || !sites->count)
        return;
    uint32_t start = ts_node_start_byte(loop);
    uint32_t end = ts_node_end_byte(loop);
    int lo = 0;
    int hi = sites->count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (sites->by_start[mid]->start < start)
            lo = mid + 1;
        else
            hi = mid;
    }
    for (int i = lo; i < sites->count && sites->by_start[i]->start < end; i++)
        ts_flow_write(ctx, sites->by_start[i]->name, NULL, false);
}

/* Bind each name a `var` of the function being entered declares, in the
 * function's frame and as unknown, before the walk reaches any block. */
static void ts_hoist_vars(TSLSPContext *ctx) {
    const struct TsAssignSites *sites = ctx->assign_sites;
    if (!sites || !sites->hoisted_count || !ctx->fn_scope)
        return;
    int lo = 0;
    int hi = sites->hoisted_count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        const TsAssignSite *h = &sites->hoisted[mid];
        if (h->fn_start < ctx->fn_start ||
            (h->fn_start == ctx->fn_start && h->fn_end < ctx->fn_end))
            lo = mid + 1;
        else
            hi = mid;
    }
    for (int i = lo; i < sites->hoisted_count; i++) {
        const TsAssignSite *h = &sites->hoisted[i];
        if (h->fn_start != ctx->fn_start || h->fn_end != ctx->fn_end)
            break;
        cbm_scope_bind(ctx->fn_scope, h->name, cbm_type_unknown());
    }
}

/* ── Functions by QN ──────────────────────────────────────────────────
 *
 * The per-file registry has no hash index, so cbm_registry_lookup_func scans
 * it, and the resolver looks up each function of the file at least twice
 * (its implicit return, its body): a file of n functions cost n * n.
 * TsFuncOrder is a sorted copy of the registry's QNs, first registered
 * first, so a search finds the function the scan finds. Functions added
 * after the copy are scanned until they are many enough to copy again. */
typedef struct {
    const char *qn;
    int index;
} TsFuncSlot;

struct TsFuncOrder {
    const CBMTypeRegistry *reg;
    TsFuncSlot *slots;
    int count;   /* slots in use */
    int covered; /* reg->funcs[0, covered) are in the copy */
};

enum { TS_FUNC_ORDER_MIN = 64 };

static int ts_func_slot_cmp(const void *pa, const void *pb) {
    const TsFuncSlot *a = (const TsFuncSlot *)pa;
    const TsFuncSlot *b = (const TsFuncSlot *)pb;
    int by_qn = strcmp(a->qn, b->qn);
    return by_qn != 0 ? by_qn : (a->index > b->index) - (a->index < b->index);
}

/* The sorted copy of reg's QNs, made again when reg is another registry or
 * grew by more than half since the copy. NULL for a small registry or when
 * the arena is out of memory: the caller scans. */
static const struct TsFuncOrder *ts_func_order(TSLSPContext *ctx, const CBMTypeRegistry *reg) {
    if (!ctx->arena || reg->func_count < TS_FUNC_ORDER_MIN) {
        return NULL;
    }
    struct TsFuncOrder *order = ctx->func_order;
    if (order && order->reg == reg && order->covered <= reg->func_count &&
        reg->func_count - order->covered <= order->covered / 2) {
        return order;
    }
    if (!order) {
        order = (struct TsFuncOrder *)cbm_arena_alloc(ctx->arena, sizeof(*order));
        if (!order) {
            return NULL;
        }
        memset(order, 0, sizeof(*order));
        ctx->func_order = order;
    }
    TsFuncSlot *slots =
        (TsFuncSlot *)cbm_arena_alloc(ctx->arena, (size_t)reg->func_count * sizeof(*slots));
    if (!slots) {
        order->reg = NULL;
        return NULL;
    }
    int n = 0;
    for (int i = 0; i < reg->func_count; i++) {
        if (reg->funcs[i].qualified_name) {
            slots[n].qn = reg->funcs[i].qualified_name;
            slots[n].index = i;
            n++;
        }
    }
    qsort(slots, (size_t)n, sizeof(*slots), ts_func_slot_cmp);
    order->reg = reg;
    order->slots = slots;
    order->count = n;
    order->covered = reg->func_count;
    return order;
}

/* The first function of reg itself (not of its fallback) whose QN is `qn`:
 * the one a scan of reg->funcs meets first. */
static const CBMRegisteredFunc *ts_own_func(TSLSPContext *ctx, const CBMTypeRegistry *reg,
                                            const char *qn) {
    const struct TsFuncOrder *order = ts_func_order(ctx, reg);
    int tail = 0;
    if (order) {
        int lo = 0;
        int hi = order->count;
        while (lo < hi) {
            int mid = lo + (hi - lo) / 2;
            if (strcmp(order->slots[mid].qn, qn) < 0) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if (lo < order->count && strcmp(order->slots[lo].qn, qn) == 0) {
            return &reg->funcs[order->slots[lo].index];
        }
        tail = order->covered;
    }
    for (int i = tail; i < reg->func_count; i++) {
        if (reg->funcs[i].qualified_name && strcmp(reg->funcs[i].qualified_name, qn) == 0) {
            return &reg->funcs[i];
        }
    }
    return NULL;
}

/* cbm_registry_lookup_func with a search in place of its scan of a registry
 * that has no hash index. Same answer. */
static const CBMRegisteredFunc *ts_lookup_func(TSLSPContext *ctx, const CBMTypeRegistry *reg,
                                               const char *qn) {
    if (!reg || !qn) {
        return NULL;
    }
    if (!ctx || (reg->func_qn_buckets && reg->func_qn_bucket_count > 0)) {
        return cbm_registry_lookup_func(reg, qn);
    }
    const CBMRegisteredFunc *own = ts_own_func(ctx, reg, qn);
    if (!own && reg->fallback) {
        return cbm_registry_lookup_func(reg->fallback, qn);
    }
    return own;
}

/* Values and types have separate namespaces in TS (`interface Port` may
 * coexist with `const Port`). Reuse the scope's indexed value table without
 * registering a value as a nominal type or mutating the shared fallback. */
static const CBMVarBinding *ts_registry_value(TSLSPContext *ctx, const char *qn) {
    for (const CBMTypeRegistry *reg = ctx->registry; reg; reg = reg->fallback) {
        const CBMVarBinding *value = cbm_scope_lookup_local(reg->ts_values, qn);
        if (value) {
            /* A class expression can also have a Variable row. Its class
             * registration proves the constructor; interfaces and aliases
             * do not make the runtime value a constructor. */
            const CBMRegisteredType *type = cbm_registry_lookup_type(ctx->registry, qn);
            if (type && !type->is_interface && !type->alias_of)
                return NULL;
            return value;
        }
    }
    return NULL;
}

/* The member an import binding names in its module: the exported name of a
 * renamed named import (`foo` for `import { foo as bar }`, #2297), else the
 * binding itself. Callers have already matched `local` to an import binding. */
static const char *ts_import_export_name(const TSLSPContext *ctx, const char *local) {
    if (!ctx || !local)
        return local;
    for (int i = 0; i < ctx->import_alias_count; i++) {
        if (strcmp(ctx->import_alias_locals[i], local) == 0)
            return ctx->import_alias_exports[i];
    }
    return local;
}

/* Full QN of an imported symbol. An import value is normally the module QN
 * (symbol = module + "." + name), but may already be the symbol QN. When the
 * module QN ends in ".name" the spelling is ambiguous: `Foo.ts` exporting
 * `Foo` (module `x.Foo`, symbol `x.Foo.Foo`) looks exactly like an
 * already-qualified value. Treating it as the symbol typed every imported
 * same-name class as its module (#1354), so the registry decides: a
 * registered `module.name` wins, else the value is the symbol. Two hashed
 * lookups on a finalized/sealed registry, only in the ambiguous case. */
static const char *ts_import_symbol_qn(TSLSPContext *ctx, const char *module_qn, const char *name) {
    if (!ctx || !module_qn || !name) {
        return NULL;
    }
    if (strcmp(name, "default") == 0) {
        const char *default_qn = cbm_arena_sprintf(ctx->arena, "%s.default", module_qn);
        const CBMVarBinding *alias = ts_registry_value(ctx, default_qn);
        if (alias && alias->type && alias->type->kind == CBM_TYPE_NAMED) {
            const char *target = alias->type->data.named.qualified_name;
            if (ts_lookup_func(ctx, ctx->registry, target) ||
                cbm_registry_lookup_type(ctx->registry, target))
                return target;
        }
        if (ts_lookup_func(ctx, ctx->registry, module_qn) ||
            cbm_registry_lookup_type(ctx->registry, module_qn) || ts_registry_value(ctx, module_qn))
            return module_qn;
    }
    const char *appended = cbm_arena_sprintf(ctx->arena, "%s.%s", module_qn, name);
    size_t module_len = strlen(module_qn);
    size_t name_len = strlen(name);
    if (module_len > name_len + 1 && module_qn[module_len - name_len - 1] == '.' &&
        strcmp(module_qn + module_len - name_len, name) == 0) {
        if (appended &&
            (cbm_registry_lookup_type(ctx->registry, appended) ||
             ts_lookup_func(ctx, ctx->registry, appended) || ts_registry_value(ctx, appended))) {
            return appended;
        }
        return module_qn;
    }
    return appended;
}

/* Same-file function values use only the exact current-module QN. No short-name,
 * suffix, overload-arity, or project-wide uniqueness fallback is admissible. */
static const CBMRegisteredFunc *ts_exact_same_module_function(TSLSPContext *ctx, const char *name) {
    if (!ctx || !ctx->registry || !ctx->module_qn || !name ||
        ts_scope_has_binding(ctx->current_scope, name) || !ts_is_module_callable(ctx, name)) {
        return NULL;
    }
    const char *full_qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, name);
    return full_qn ? ts_lookup_func(ctx, ctx->registry, full_qn) : NULL;
}

/* Return a function only when the local import binding maps to one unambiguous
 * module and that module contains the exact QN of the member the binding names
 * (the exported name for `import { foo as bar }`). A renamed import of a name
 * the module does not export fails closed and remains USAGE. */
static const CBMRegisteredFunc *ts_exact_imported_function(TSLSPContext *ctx, const char *name) {
    if (!ctx || !ctx->registry || !name || ts_scope_has_binding(ctx->current_scope, name)) {
        return NULL;
    }
    const char *matched_module = NULL;
    for (int i = 0; i < ctx->import_count; i++) {
        const char *local = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
        const char *module_qn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
        if (!local || !module_qn || strcmp(local, name) != 0) {
            continue;
        }
        if (matched_module && strcmp(matched_module, module_qn) != 0) {
            return NULL;
        }
        matched_module = module_qn;
    }
    if (!matched_module) {
        return NULL;
    }
    const char *full_qn =
        ts_import_symbol_qn(ctx, matched_module, ts_import_export_name(ctx, name));
    return full_qn ? ts_lookup_func(ctx, ctx->registry, full_qn) : NULL;
}

static void ts_block_shadowed_reference_usage(TSLSPContext *ctx, const char *name, TSNode site) {
    if (!ctx || !ctx->usages || !name || !ctx->enclosing_func_qn || ts_node_is_null(site)) {
        return;
    }
    const CBMScope *binding_scope = ts_scope_binding_owner(ctx->current_scope, name);
    if (!binding_scope) {
        return;
    }
    uint32_t start = ts_node_start_byte(site);
    uint32_t end = ts_node_end_byte(site);
    for (int i = 0; i < ctx->usages->count; i++) {
        CBMUsage *usage = &ctx->usages->items[i];
        if (usage->kind == CBM_USAGE_VALUE && usage->may_be_call_reference && usage->ref_name &&
            usage->enclosing_func_qn && strcmp(usage->ref_name, name) == 0 &&
            strcmp(usage->enclosing_func_qn, ctx->enclosing_func_qn) == 0 &&
            usage->site_start_byte == start && usage->site_end_byte == end) {
            usage->semantic_reference_blocked = true;
            usage->semantic_reference_local_shadow = binding_scope->parent != NULL;
            return;
        }
    }
}

static const CBMType *type_of_identifier(TSLSPContext *ctx, const char *name) {
    if (!ctx || !name)
        return cbm_type_unknown();

    // Scope lookup (params, locals), with reassigned locals at this point.
    const CBMType *bound = ts_lookup_binding_type(ctx, name);
    if (bound)
        return bound;

    // Imports: bare identifier matching an import binding. Compute the full symbol QN
    // and look it up in the registry. If it's a registered func, return its signature;
    // if it's a registered type, return NAMED. Falls back to NAMED(module_qn) for
    // namespace-style imports where no specific symbol matches.
    for (int i = 0; i < ctx->import_count; i++) {
        const char *local = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
        const char *mqn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
        if (!local || !mqn || strcmp(local, name) != 0)
            continue;

        // Construct the full symbol QN using the same convention as exact
        // imported function-value resolution.
        const char *full_qn = ts_import_symbol_qn(ctx, mqn, ts_import_export_name(ctx, name));

        if (ts_scope_has_binding(ctx->named_imports, name)) {
            const CBMVarBinding *value = ts_registry_value(ctx, full_qn);
            if (value)
                return value->type;
        }

        // Try the symbol lookup precedence: registered func, then registered type.
        const CBMRegisteredFunc *f = ts_lookup_func(ctx, ctx->registry, full_qn);
        if (f && f->signature)
            return f->signature;
        const CBMRegisteredType *rt = cbm_registry_lookup_type(ctx->registry, full_qn);
        if (rt)
            return rt->ts_value_binding_written ? cbm_type_unknown()
                                                : cbm_type_named(ctx->arena, full_qn);

        // No specific match — fall back to NAMED(module_qn), which is correct for
        // namespace-style imports (`import * as foo from './foo'`).
        return cbm_type_named(ctx->arena, mqn);
    }

    // Module-local function or class.
    if (ctx->module_qn) {
        const char *candidate = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, name);
        const CBMRegisteredType *rt = cbm_registry_lookup_type(ctx->registry, candidate);
        if (rt)
            return rt->ts_value_binding_written ? cbm_type_unknown()
                                                : cbm_type_named(ctx->arena, candidate);
        const CBMRegisteredFunc *f = ts_lookup_func(ctx, ctx->registry, candidate);
        if (f && f->signature && ts_is_module_callable(ctx, name))
            return f->signature;
    }

    // Global / stdlib bare-name lookup (Promise, Array, Map, Set, console, JSON, Object, ...).
    // The TS stdlib registers these with QN equal to the bare name.
    {
        const CBMRegisteredType *rt = cbm_registry_lookup_type(ctx->registry, name);
        if (rt)
            return cbm_type_named(ctx->arena, name);
        const CBMRegisteredFunc *f = ts_lookup_func(ctx, ctx->registry, name);
        if (f && f->signature)
            return f->signature;
    }

    return cbm_type_unknown();
}

// Map BUILTIN type names to their wrapper class for method dispatch.
// `"x".split(...)` works because TS treats string primitives as having String prototype.
static const char *builtin_wrapper_class(const char *builtin_name) {
    if (!builtin_name)
        return NULL;
    if (strcmp(builtin_name, "string") == 0)
        return "String";
    if (strcmp(builtin_name, "number") == 0)
        return "Number";
    if (strcmp(builtin_name, "boolean") == 0)
        return "Boolean";
    if (strcmp(builtin_name, "bigint") == 0)
        return "BigInt";
    if (strcmp(builtin_name, "symbol") == 0)
        return "Symbol";
    return NULL;
}

// Look up a property `name` on a receiver type. Returns the property type or UNKNOWN.
#define TS_LSP_MAX_MEMBER_DEPTH 64
#define TS_LSP_INLINE_VISITED_TYPES 16

typedef struct {
    const char *qn;
    int depth;
} TSVisitedType;

struct TSLookupState {
    TSVisitedType inline_visited[TS_LSP_INLINE_VISITED_TYPES];
    TSVisitedType *visited;
    int visited_count;
    int visited_capacity;
#ifdef CBM_ENABLE_TEST_SEAMS
    int steps;
#endif
};

/* A named type needs another visit only when reached along a shallower path.
 * Grow the visited table rather than silently dropping entries at a fixed cap:
 * the depth bound then limits each named type to at most 64 admitted visits. */
static bool ts_lookup_visit_named(CBMArena *arena, TSLookupState *state, const char *qn,
                                  int depth) {
    for (int i = 0; i < state->visited_count; i++) {
        if (strcmp(state->visited[i].qn, qn) == 0) {
            if (state->visited[i].depth <= depth)
                return false;
            state->visited[i].depth = depth;
            return true;
        }
    }
    if (!state->visited) {
        state->visited = state->inline_visited;
        state->visited_capacity = TS_LSP_INLINE_VISITED_TYPES;
    } else if (state->visited_count == state->visited_capacity) {
        int capacity = state->visited_capacity * 2;
        TSVisitedType *larger =
            (TSVisitedType *)cbm_arena_alloc(arena, (size_t)capacity * sizeof(*larger));
        if (!larger) {
            fprintf(stderr, "[tslsp] lookup visited allocation failed\n");
            return false;
        }
        memcpy(larger, state->visited, (size_t)state->visited_count * sizeof(*larger));
        state->visited = larger;
        state->visited_capacity = capacity;
    }
    state->visited[state->visited_count++] = (TSVisitedType){.qn = qn, .depth = depth};
    return true;
}

/* null, undefined, void and never hold no object, so a call never reaches
 * them through a union. */
static bool ts_type_is_empty_value(const CBMType *t) {
    if (!t || t->kind != CBM_TYPE_BUILTIN || !t->data.builtin.name)
        return false;
    const char *name = t->data.builtin.name;
    return strcmp(name, "null") == 0 || strcmp(name, "undefined") == 0 ||
           strcmp(name, "void") == 0 || strcmp(name, "never") == 0;
}

static bool ts_same_func(const CBMRegisteredFunc *a, const CBMRegisteredFunc *b) {
    return a == b || (a->qualified_name && b->qualified_name &&
                      strcmp(a->qualified_name, b->qualified_name) == 0);
}

static const CBMType *lookup_member_type_at(TSLSPContext *ctx, const CBMType *recv,
                                            const char *name, int depth, TSLookupState *state);

/* Depth and shallower-only named-type visits bound work on cyclic inheritance. */
static const CBMType *lookup_member_type(TSLSPContext *ctx, const CBMType *recv, const char *name) {
    TSLookupState state = {0};
    const CBMType *result = lookup_member_type_at(ctx, recv, name, 0, &state);
#ifdef CBM_ENABLE_TEST_SEAMS
    if (state.steps > g_ts_max_member_lookup_steps)
        g_ts_max_member_lookup_steps = state.steps;
#endif
    return result;
}

static const CBMType *lookup_member_type_at(TSLSPContext *ctx, const CBMType *recv,
                                            const char *name, int depth, TSLookupState *state) {
#ifdef CBM_ENABLE_TEST_SEAMS
    if (state)
        state->steps++;
#endif
    if (!ctx || !recv || !name || !state || depth >= TS_LSP_MAX_MEMBER_DEPTH)
        return cbm_type_unknown();
    const CBMType *base = simplify_type(ctx, recv);
    if (!base)
        return cbm_type_unknown();
    base = unwrap_passthrough_template(base);
    if (!base)
        return cbm_type_unknown();

    // BUILTIN primitives delegate to their wrapper class (e.g. string → String).
    if (base->kind == CBM_TYPE_BUILTIN) {
        const char *wrap = builtin_wrapper_class(base->data.builtin.name);
        if (wrap) {
            const CBMType *wrapped = cbm_type_named(ctx->arena, wrap);
            return lookup_member_type_at(ctx, wrapped, name, depth + 1, state);
        }
        return cbm_type_unknown();
    }

    if (base->kind == CBM_TYPE_TEMPLATE) {
        // Look up on the template name (e.g., "Array", "Promise"); generic params are
        // applied via cbm_type_substitute when we know the registered type's params.
        const CBMRegisteredType *rt =
            cbm_registry_lookup_type(ctx->registry, base->data.template_type.template_name);
        if (rt) {
            // Field?
            if (rt->field_names && rt->field_types) {
                for (int i = 0; rt->field_names[i]; i++) {
                    if (strcmp(rt->field_names[i], name) == 0) {
                        return cbm_type_substitute(ctx->arena, rt->field_types[i],
                                                   rt->type_param_names,
                                                   base->data.template_type.template_args);
                    }
                }
            }
            // Method?
            if (rt->method_qns && rt->method_names) {
                for (int i = 0; rt->method_names[i]; i++) {
                    if (strcmp(rt->method_names[i], name) == 0) {
                        const CBMRegisteredFunc *f =
                            ts_lookup_func(ctx, ctx->registry, rt->method_qns[i]);
                        if (f && f->signature) {
                            return cbm_type_substitute(ctx->arena, f->signature,
                                                       rt->type_param_names,
                                                       base->data.template_type.template_args);
                        }
                    }
                }
            }
        }
        return cbm_type_unknown();
    }

    if (base->kind == CBM_TYPE_OBJECT_LIT) {
        if (base->data.object_lit.prop_names && base->data.object_lit.prop_types) {
            for (int i = 0; base->data.object_lit.prop_names[i]; i++) {
                if (strcmp(base->data.object_lit.prop_names[i], name) == 0) {
                    return base->data.object_lit.prop_types[i];
                }
            }
        }
        return cbm_type_unknown();
    }

    /* The member of a union is the union of each branch's member: one type
     * when the branches agree, and unknown when a branch does not prove one.
     * A call on it then needs one target from every branch. */
    if (base->kind == CBM_TYPE_UNION) {
        int count = base->data.union_type.count;
        if (!base->data.union_type.members || count <= 0 ||
            depth + 1 >= TS_LSP_MAX_MEMBER_DEPTH)
            return cbm_type_unknown();
        const CBMType **found =
            (const CBMType **)cbm_arena_alloc(ctx->arena, (size_t)count * sizeof(*found));
        if (!found)
            return cbm_type_unknown();
        int n = 0;
        int visited_mark = state->visited_count;
        for (int i = 0; i < count; i++) {
            const CBMType *member = base->data.union_type.members[i];
            if (ts_type_is_empty_value(member))
                continue;
            state->visited_count = visited_mark;
            const CBMType *m = lookup_member_type_at(ctx, member, name, depth + 1, state);
            if (!m || cbm_type_is_unknown(m))
                return cbm_type_unknown();
            found[n++] = m;
        }
        if (n == 0)
            return cbm_type_unknown();
        return n == 1 ? found[0] : cbm_type_union(ctx->arena, found, n);
    }

    if (base->kind == CBM_TYPE_INTERSECTION) {
        if (base->data.union_type.members) {
            for (int i = 0; i < base->data.union_type.count; i++) {
                if (depth + 1 >= TS_LSP_MAX_MEMBER_DEPTH)
                    break;
                const CBMType *m = lookup_member_type_at(ctx, base->data.union_type.members[i],
                                                         name, depth + 1, state);
                if (!cbm_type_is_unknown(m))
                    return m;
            }
        }
        return cbm_type_unknown();
    }

    if (base->kind != CBM_TYPE_NAMED)
        return cbm_type_unknown();

    const char *recv_qn = base->data.named.qualified_name;
    if (!recv_qn)
        return cbm_type_unknown();
    if (!ts_lookup_visit_named(ctx->arena, state, recv_qn, depth))
        return cbm_type_unknown();
    const CBMRegisteredType *rt = cbm_registry_resolve_alias(ctx->registry, recv_qn);
    if (!rt) {
        rt = cbm_registry_lookup_type(ctx->registry, recv_qn);
        if (!rt)
            return cbm_type_unknown();
    }

    // Direct field lookup.
    if (rt->field_names && rt->field_types) {
        for (int i = 0; rt->field_names[i]; i++) {
            if (strcmp(rt->field_names[i], name) == 0)
                return rt->field_types[i];
        }
    }
    // Method lookup → return the method's FUNC type.
    if (rt->method_qns && rt->method_names) {
        for (int i = 0; rt->method_names[i]; i++) {
            if (strcmp(rt->method_names[i], name) == 0) {
                const CBMRegisteredFunc *f = ts_lookup_func(ctx, ctx->registry, rt->method_qns[i]);
                if (f && f->signature)
                    return f->signature;
                return cbm_type_unknown();
            }
        }
    }
    // Walk extends/implements.
    if (rt->embedded_types) {
        for (int i = 0; rt->embedded_types[i]; i++) {
            if (depth + 1 >= TS_LSP_MAX_MEMBER_DEPTH)
                break;
            const CBMType *parent = cbm_type_named(ctx->arena, rt->embedded_types[i]);
            const CBMType *m = lookup_member_type_at(ctx, parent, name, depth + 1, state);
            if (!cbm_type_is_unknown(m))
                return m;
        }
    }
    return cbm_type_unknown();
}

// TS utility types like Partial<T>, Readonly<T>, Required<T> are essentially
// transformations on T's properties — for call-edge resolution they pass through
// to T's own method/property surface. NonNullable<T> also unwraps to T.
static const CBMType *unwrap_passthrough_template(const CBMType *t) {
    if (!t || t->kind != CBM_TYPE_TEMPLATE)
        return t;
    const char *name = t->data.template_type.template_name;
    if (!name || !t->data.template_type.template_args || t->data.template_type.arg_count < 1)
        return t;
    // Single-arg utility types pass through to T's surface for method dispatch.
    if (strcmp(name, "Partial") == 0 || strcmp(name, "Required") == 0 ||
        strcmp(name, "Readonly") == 0 || strcmp(name, "NonNullable") == 0 ||
        strcmp(name, "Pick") == 0 || strcmp(name, "Omit") == 0 || strcmp(name, "Awaited") == 0) {
        return t->data.template_type.template_args[0];
    }
    // ReturnType<F>: when F is FUNC, surface F's return type for method dispatch.
    if (strcmp(name, "ReturnType") == 0) {
        const CBMType *f = t->data.template_type.template_args[0];
        if (f && f->kind == CBM_TYPE_FUNC && f->data.func.return_types &&
            f->data.func.return_types[0]) {
            return f->data.func.return_types[0];
        }
        return t;
    }
    // Exclude<T, U> / Extract<T, U>: T is a union; for method dispatch we treat the
    // result as T itself (any member's common methods still resolve via union dispatch).
    if (strcmp(name, "Exclude") == 0 || strcmp(name, "Extract") == 0) {
        return t->data.template_type.template_args[0];
    }
    // Promise<T> intentionally NOT unwrapped — methods (then/catch/finally) live on
    // the Promise registration. await-expression unwraps via ts_eval_expr_type.
    return t;
}

// Build a UNION of LITERAL string types representing keyof T, where T is a registered
// class/interface. Returns UNKNOWN if T has no fields or isn't registered.
static const CBMType *eval_keyof(TSLSPContext *ctx, const CBMType *operand) {
    if (!ctx || !operand)
        return cbm_type_unknown();
    const CBMType *base = simplify_type(ctx, operand);
    if (!base || base->kind != CBM_TYPE_NAMED)
        return cbm_type_unknown();
    const CBMRegisteredType *rt =
        cbm_registry_lookup_type(ctx->registry, base->data.named.qualified_name);
    if (!rt || !rt->field_names || !rt->field_names[0])
        return cbm_type_unknown();
    int fc = 0;
    while (rt->field_names[fc])
        fc++;
    const CBMType *members[64];
    int mc = 0;
    for (int i = 0; i < fc && mc < 63; i++) {
        members[mc++] = cbm_type_ts_literal(ctx->arena, "string", rt->field_names[i]);
    }
    members[mc] = NULL;
    if (mc == 0)
        return cbm_type_unknown();
    if (mc == 1)
        return members[0];
    return cbm_type_union(ctx->arena, members, mc);
}

// Evaluate T[K]: when K is a string literal, look up that field on T. When K is a
// type parameter (or `keyof T` itself), return UNKNOWN — pragmatic v1.
static const CBMType *eval_indexed_access(TSLSPContext *ctx, const CBMType *obj,
                                          const CBMType *key) {
    if (!ctx || !obj || !key)
        return cbm_type_unknown();
    if (key->kind == CBM_TYPE_TS_LITERAL && key->data.literal_ts.value &&
        key->data.literal_ts.tag && strcmp(key->data.literal_ts.tag, "string") == 0) {
        return lookup_member_type(ctx, obj, key->data.literal_ts.value);
    }
    return cbm_type_unknown();
}

/* Depth-guarded entry, same contract as lookup_member_type: the method walk
 * recurses through wrapper classes, union members and the extends/implements
 * chain. A cyclic chain (#1743: the Effect idiom `class Service extends
 * Context.Service<Service, I>()(...)` whose base resolved to the class itself)
 * recursed without bound and overflowed the resolver thread's stack. Past the
 * cap the method is simply not found. */
static const CBMRegisteredFunc *lookup_method(TSLSPContext *ctx, const CBMType *recv,
                                              const char *method_name) {
    TSLookupState state = {0};
    const CBMRegisteredFunc *result = lookup_method_at(ctx, recv, method_name, 0, &state);
#ifdef CBM_ENABLE_TEST_SEAMS
    if (state.steps > g_ts_max_method_lookup_steps)
        g_ts_max_method_lookup_steps = state.steps;
#endif
    return result;
}

/* Depth and shallower-only named-type visits bound cyclic inheritance work. */
static const CBMRegisteredFunc *lookup_method_at(TSLSPContext *ctx, const CBMType *recv,
                                                 const char *method_name, int depth,
                                                 TSLookupState *state) {
#ifdef CBM_ENABLE_TEST_SEAMS
    if (state)
        state->steps++;
#endif
    if (!ctx || !recv || !method_name || !state || depth >= TS_LSP_MAX_MEMBER_DEPTH)
        return NULL;
    const CBMType *base = simplify_type(ctx, recv);
    if (!base)
        return NULL;
    base = unwrap_passthrough_template(base);
    if (!base)
        return NULL;

    // BUILTIN primitives → look up via the wrapper class (string → String, etc.).
    if (base->kind == CBM_TYPE_BUILTIN) {
        const char *wrap = builtin_wrapper_class(base->data.builtin.name);
        if (wrap) {
            const CBMType *wrapped = cbm_type_named(ctx->arena, wrap);
            return lookup_method_at(ctx, wrapped, method_name, depth + 1, state);
        }
        return NULL;
    }

    if (ctx->debug) {
        const char *base_qn = (base->kind == CBM_TYPE_NAMED) ? base->data.named.qualified_name
                              : (base->kind == CBM_TYPE_TEMPLATE)
                                  ? base->data.template_type.template_name
                                  : "<other>";
        fprintf(stderr, "[ts_lsp] lookup_method: recv_kind=%d recv_qn=%s method=%s\n",
                (int)base->kind, base_qn ? base_qn : "(null)", method_name);
    }

    if (base->kind == CBM_TYPE_TEMPLATE) {
        const CBMRegisteredType *rt =
            cbm_registry_lookup_type(ctx->registry, base->data.template_type.template_name);
        /* There is no type proof for an unregistered generic receiver.
         * In a per-file registry, a speculative method lookup would also
         * scan every function for every unknown call. */
        if (!rt)
            return NULL;
        if (rt->method_qns && rt->method_names) {
            for (int i = 0; rt->method_names[i]; i++) {
                if (strcmp(rt->method_names[i], method_name) == 0) {
                    return ts_lookup_func(ctx, ctx->registry, rt->method_qns[i]);
                }
            }
        }
        /* Cross-file registries keep methods by their exact receiver QN,
         * without a per-type method-name list. Use that same named-type
         * lookup for a generic instance; its arguments remain on the caller
         * for return-type substitution. */
        const CBMType *named = cbm_type_named(ctx->arena, base->data.template_type.template_name);
        return lookup_method_at(ctx, named, method_name, depth + 1, state);
    }

    /* A union proves a target only when every member that can hold a value
     * resolves the method to the same declaration. An intersection needs
     * the members that hold the method to agree. */
    if (base->kind == CBM_TYPE_UNION || base->kind == CBM_TYPE_INTERSECTION) {
        bool every = base->kind == CBM_TYPE_UNION;
        const CBMRegisteredFunc *agreed = NULL;
        if (!base->data.union_type.members || depth + 1 >= TS_LSP_MAX_MEMBER_DEPTH)
            return NULL;
        /* Each member walks from the same visited types (the ancestors), so a
         * base two members share is not refused to the second one. */
        int visited_mark = state->visited_count;
        for (int i = 0; i < base->data.union_type.count; i++) {
            const CBMType *member = base->data.union_type.members[i];
            state->visited_count = visited_mark;
            if (every && ts_type_is_empty_value(member))
                continue;
            const CBMRegisteredFunc *f =
                lookup_method_at(ctx, member, method_name, depth + 1, state);
            if (!f) {
                if (every)
                    return NULL;
                continue;
            }
            if (agreed && !ts_same_func(agreed, f))
                return NULL;
            agreed = f;
        }
        return agreed;
    }

    if (base->kind != CBM_TYPE_NAMED)
        return NULL;
    const char *recv_qn = base->data.named.qualified_name;
    if (!recv_qn)
        return NULL;

    if (!ts_lookup_visit_named(ctx->arena, state, recv_qn, depth))
        return NULL;

    const CBMRegisteredFunc *f =
        cbm_registry_lookup_method_aliased(ctx->registry, recv_qn, method_name);
    if (f)
        return f;

    // Walk extends/implements via the registered type.
    const CBMRegisteredType *rt = cbm_registry_lookup_type(ctx->registry, recv_qn);
    if (rt && rt->embedded_types) {
        for (int i = 0; rt->embedded_types[i]; i++) {
            if (depth + 1 >= TS_LSP_MAX_MEMBER_DEPTH)
                break;
            const CBMType *parent = cbm_type_named(ctx->arena, rt->embedded_types[i]);
            const CBMRegisteredFunc *pf =
                lookup_method_at(ctx, parent, method_name, depth + 1, state);
            if (pf)
                return pf;
        }
    }
    return NULL;
}

/* Select one overload for both edge emission and call-expression return
 * typing.  The first lookup preserves wrapper/alias/inheritance/template/union
 * traversal; its receiver identifies the concrete overload set. */
static const CBMRegisteredFunc *ts_lookup_method_for_call(TSLSPContext *ctx, const CBMType *recv,
                                                          const char *method_name, TSNode args) {
    const CBMRegisteredFunc *fallback = lookup_method(ctx, recv, method_name);
    if (!fallback || !fallback->receiver_type)
        return fallback;

    int arg_count = ts_node_is_null(args) ? 0 : (int)ts_node_named_child_count(args);
    const CBMRegisteredFunc *selected = NULL;
    if (arg_count > 0 && arg_count <= 16) {
        const CBMType *arg_types[16] = {0};
        for (int i = 0; i < arg_count; i++) {
            arg_types[i] = ts_eval_expr_type(ctx, ts_node_named_child(args, (uint32_t)i));
        }
        selected = cbm_registry_lookup_method_by_types(ctx->registry, fallback->receiver_type,
                                                       method_name, arg_types, arg_count);
    } else {
        selected = cbm_registry_lookup_method_by_args(ctx->registry, fallback->receiver_type,
                                                      method_name, arg_count);
    }
    return selected ? selected : fallback;
}

/* Select a free function/namespace export by the same ordered argument types
 * used for method overloads.  Edge emission and expression return typing must
 * share this decision; otherwise the graph can point at one overload while a
 * chained call is typed from another. */
static const CBMRegisteredFunc *ts_lookup_symbol_for_call(TSLSPContext *ctx, const char *module_qn,
                                                          const char *symbol_name, TSNode args) {
    if (!ctx || !ctx->registry || !module_qn || !symbol_name)
        return NULL;

    if (strcmp(symbol_name, "default") == 0) {
        const char *qn = ts_import_symbol_qn(ctx, module_qn, symbol_name);
        const char *dot = qn ? strrchr(qn, '.') : NULL;
        if (!dot)
            return NULL;
        module_qn = qn;
        symbol_name = dot + 1;
    }

    /* Import maps may carry either a module QN or an already-qualified symbol
     * QN.  The registry overload APIs accept the former, so strip one exact
     * trailing `.symbol` before lookup instead of producing x.symbol.symbol. */
    const char *lookup_module = module_qn;
    size_t module_len = strlen(module_qn);
    size_t symbol_len = strlen(symbol_name);
    if (module_len > symbol_len + 1 && module_qn[module_len - symbol_len - 1] == '.' &&
        strcmp(module_qn + module_len - symbol_len, symbol_name) == 0) {
        lookup_module = cbm_arena_strndup(ctx->arena, module_qn, module_len - symbol_len - 1);
    }

    int arg_count = ts_node_is_null(args) ? 0 : (int)ts_node_named_child_count(args);
    const CBMRegisteredFunc *selected = NULL;
    if (arg_count > 0 && arg_count <= 16) {
        const CBMType *arg_types[16] = {0};
        for (int i = 0; i < arg_count; i++)
            arg_types[i] = ts_eval_expr_type(ctx, ts_node_named_child(args, (uint32_t)i));
        selected = cbm_registry_lookup_symbol_by_types(ctx->registry, lookup_module, symbol_name,
                                                       arg_types, arg_count);
    }
    if (!selected) {
        selected = cbm_registry_lookup_symbol_by_args(ctx->registry, lookup_module, symbol_name,
                                                      arg_count);
    }
    return selected;
}

/* Map one local import binding to its module.  Duplicate bindings from
 * different modules are ambiguous and deliberately fail closed. */
static const char *ts_import_module_for_local(const TSLSPContext *ctx, const char *local_name,
                                              bool *out_matched) {
    if (out_matched)
        *out_matched = false;
    if (!ctx || !local_name)
        return NULL;
    const char *matched = NULL;
    for (int i = 0; i < ctx->import_count; i++) {
        const char *local = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
        const char *module_qn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
        if (!local || !module_qn || strcmp(local, local_name) != 0)
            continue;
        if (out_matched)
            *out_matched = true;
        if (matched && strcmp(matched, module_qn) != 0)
            return NULL;
        matched = module_qn;
    }
    return matched;
}

/* Type of `new C()` for a bare class name, in TS scoping order: a class
 * declared in this module, else the class an unambiguous import binding
 * names, else the historical current-module spelling. Without the import
 * step (#1354) `new ImportedClass()` was typed as a phantom current-module
 * class, so every method call on the instance missed the registry and the
 * cross-file edge was lost while the same code in the class's own file
 * resolved. One hashed type lookup; the registry is only read. */
static bool ts_proof_name(TSLSPContext *ctx, TSNode node, const char *name);

static const CBMType *ts_new_bare_class_type(TSLSPContext *ctx, const char *cname) {
    if (ctx->assign_sites && !ts_proof_name(ctx, (TSNode){0}, cname))
        return cbm_type_unknown();
    if (ts_scope_has_binding(ctx->current_scope, cname))
        return cbm_type_unknown();
    if (!ctx->module_qn)
        return cbm_type_named(ctx->arena, cname);
    const char *local_qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, cname);
    if (ts_registry_value(ctx, local_qn))
        return cbm_type_unknown();
    const CBMRegisteredType *local_type = cbm_registry_lookup_type(ctx->registry, local_qn);
    if (local_type &&
        (local_type->is_interface || local_type->alias_of || local_type->ts_value_binding_written))
        return cbm_type_unknown();
    if (local_type)
        return cbm_type_named(ctx->arena, local_qn);
    bool import_matched = false;
    const char *import_module = ts_import_module_for_local(ctx, cname, &import_matched);
    if (import_module) {
        const char *qn = ts_import_symbol_qn(ctx, import_module, ts_import_export_name(ctx, cname));
        const CBMRegisteredType *type = cbm_registry_lookup_type(ctx->registry, qn);
        return ts_registry_value(ctx, qn) || (type && (type->is_interface || type->alias_of ||
                                                       type->ts_value_binding_written))
                   ? cbm_type_unknown()
                   : cbm_type_named(ctx->arena, qn);
    }
    return cbm_type_named(ctx->arena, local_qn);
}

/* Type of a `new_expression`: a bare constructor name follows TS scoping
 * (ts_new_bare_class_type), a dotted one is taken as spelled. NULL when the
 * node carries no constructor. Shared by expression evaluation and by the
 * field-initializer inference in ast_sweep_shapes, so `const t = new C()`
 * and `private t = new C()` type the instance identically. */
static const CBMType *ts_new_expression_type(TSLSPContext *ctx, TSNode node) {
    TSNode ctor = ts_node_child_by_field_name(node, "constructor", TS_LSP_FIELD_LEN("constructor"));
    if (ts_node_is_null(ctor))
        return NULL;
    char *cname = node_text(ctx, ctor);
    if (!cname)
        return NULL;
    return strchr(cname, '.') == NULL ? ts_new_bare_class_type(ctx, cname)
                                      : cbm_type_named(ctx->arena, cname);
}

static bool ts_import_is_instance(TSLSPContext *ctx, const char *name) {
    if (ts_scope_has_binding(ctx->current_scope, name) ||
        !ts_scope_has_binding(ctx->named_imports, name))
        return false;
    bool matched = false;
    const char *module = ts_import_module_for_local(ctx, name, &matched);
    if (!module)
        return false;
    const char *qn = ts_import_symbol_qn(ctx, module, ts_import_export_name(ctx, name));
    const CBMRegisteredType *runtime = cbm_registry_lookup_type(ctx->registry, qn);
    if (runtime && runtime->ts_value_binding_written)
        return true;
    const CBMVarBinding *value = ts_registry_value(ctx, qn);
    return value && (!value->type || value->type->kind != CBM_TYPE_OBJECT_LIT);
}

static const CBMRegisteredFunc *ts_lookup_namespace_call(TSLSPContext *ctx, const char *object_name,
                                                         const char *method_name, TSNode args,
                                                         bool *out_is_import) {
    if (out_is_import)
        *out_is_import = false;
    bool import_matched = false;
    const char *import_module = ts_import_module_for_local(ctx, object_name, &import_matched);
    if (out_is_import)
        *out_is_import = import_matched;
    if (import_matched) {
        /* An import binding lexically shadows a same-named local namespace.
         * Ambiguous imports and missing imported symbols both fail closed. */
        if (!import_module)
            return NULL;
        if (ts_scope_has_binding(ctx->named_imports, object_name)) {
            const char *qn =
                ts_import_symbol_qn(ctx, import_module, ts_import_export_name(ctx, object_name));
            if (strcmp(ts_import_export_name(ctx, object_name), "default") == 0)
                import_module = qn;
            const CBMRegisteredType *constructor = cbm_registry_lookup_type(ctx->registry, qn);
            if (strcmp(ts_import_export_name(ctx, object_name), "default") == 0 && constructor &&
                !constructor->is_interface && !constructor->alias_of) {
                const CBMRegisteredFunc *method = ts_lookup_method_for_call(
                    ctx, cbm_type_named(ctx->arena, qn), method_name, args);
                return method && (method->flags & CBM_FUNC_FLAG_STATICMETHOD) ? method : NULL;
            }
            const CBMVarBinding *value = ts_registry_value(ctx, qn);
            if (value) {
                const CBMType *type = value->type;
                if (!type || type->kind != CBM_TYPE_OBJECT_LIT)
                    return NULL;
                for (int i = 0;
                     type->data.object_lit.prop_names && type->data.object_lit.prop_names[i]; i++) {
                    if (strcmp(type->data.object_lit.prop_names[i], method_name) == 0) {
                        const CBMType *member = type->data.object_lit.prop_types[i];
                        return member && member->kind == CBM_TYPE_NAMED
                                   ? ts_lookup_func(ctx, ctx->registry,
                                                    member->data.named.qualified_name)
                                   : NULL;
                    }
                }
                return NULL;
            }
        }
        return ts_lookup_symbol_for_call(ctx, import_module, method_name, args);
    }
    /* TypeScript namespaces are module-like lexical scopes. Inside `namespace
     * App`, `Utils.fn()` addresses App.Utils.fn, not a typed instance named
     * Utils. Require an exact registered function so ordinary unknown objects
     * still fall through to receiver-type dispatch. */
    if (ctx && ctx->module_qn && object_name) {
        const char *local_module =
            cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, object_name);
        return local_module ? ts_lookup_symbol_for_call(ctx, local_module, method_name, args)
                            : NULL;
    }
    return NULL;
}

/* Preserve the generic receiver substitution historically performed by
 * lookup_member_type().  Only substitute when the selected method belongs to
 * that template owner; inherited methods may declare unrelated type params. */
static const CBMType *ts_method_signature_for_receiver(TSLSPContext *ctx, const CBMType *recv,
                                                       const CBMRegisteredFunc *method) {
    if (!method || !method->signature)
        return NULL;
    const CBMType *base = simplify_type(ctx, recv);
    base = base ? unwrap_passthrough_template(base) : NULL;
    if (!base || base->kind != CBM_TYPE_TEMPLATE || !base->data.template_type.template_args) {
        return method->signature;
    }

    const CBMRegisteredType *registered =
        cbm_registry_lookup_type(ctx->registry, base->data.template_type.template_name);
    if (!registered || !registered->qualified_name || !registered->type_param_names ||
        !method->receiver_type || strcmp(registered->qualified_name, method->receiver_type) != 0) {
        return method->signature;
    }
    const CBMType *substituted =
        cbm_type_substitute(ctx->arena, method->signature, registered->type_param_names,
                            base->data.template_type.template_args);
    return substituted ? substituted : method->signature;
}

/* Return the function signature selected at this call site.  This is the
 * single boundary shared by chained return typing and contextual callback
 * typing; both must observe the same overload as edge resolution. */
static const CBMType *ts_signature_for_call(TSLSPContext *ctx, TSNode function, TSNode args) {
    if (!ctx || ts_node_is_null(function))
        return NULL;

    if (node_kind_is(function, "member_expression")) {
        TSNode object = ts_node_child_by_field_name(function, "object", TS_LSP_FIELD_LEN("object"));
        TSNode property =
            ts_node_child_by_field_name(function, "property", TS_LSP_FIELD_LEN("property"));
        if (ts_node_is_null(object) || ts_node_is_null(property))
            return NULL;

        char *method_name = node_text(ctx, property);
        if (!method_name)
            return NULL;

        if (node_kind_is(object, "identifier")) {
            char *object_name = node_text(ctx, object);
            if (!ts_scope_has_binding(ctx->current_scope, object_name) &&
                !ts_import_is_instance(ctx, object_name)) {
                bool is_import = false;
                const CBMRegisteredFunc *namespace_func =
                    ts_lookup_namespace_call(ctx, object_name, method_name, args, &is_import);
                if (namespace_func || is_import)
                    return namespace_func ? namespace_func->signature : NULL;
            }
        }

        const CBMType *recv = ts_eval_expr_type(ctx, object);
        const CBMRegisteredFunc *method = ts_lookup_method_for_call(ctx, recv, method_name, args);
        const CBMType *signature = ts_method_signature_for_receiver(ctx, recv, method);
        /* Callable fields still use ordinary member typing. Reuse the receiver
         * already evaluated above so deep fluent chains remain linear. */
        return signature ? signature : lookup_member_type(ctx, recv, method_name);
    }

    if (node_kind_is(function, "identifier")) {
        char *name = node_text(ctx, function);
        if (name && ts_scope_has_binding(ctx->current_scope, name))
            return type_of_identifier(ctx, name);
        if (name) {
            /* An explicit import binding wins over a flattened same-file
             * member name, in return typing just as in call resolution. */
            bool imported = false;
            const char *module_qn = ts_import_module_for_local(ctx, name, &imported);
            if (imported) {
                const CBMRegisteredFunc *registered = module_qn
                    ? ts_lookup_symbol_for_call(ctx, module_qn, ts_import_export_name(ctx, name), args)
                    : NULL;
                return registered ? registered->signature : NULL;
            }
            if (!ts_is_module_callable(ctx, name))
                return ts_eval_expr_type(ctx, function);
            const CBMRegisteredFunc *registered =
                ts_lookup_symbol_for_call(ctx, ctx->module_qn, name, args);
            return registered ? registered->signature : NULL;
        }
    }

    return ts_eval_expr_type(ctx, function);
}

// Pull the underlying return type out of a FUNC signature, collapsing single-element
// return arrays to that element.
static const CBMType *return_type_of(CBMArena *arena, const CBMType *sig) {
    if (!sig || sig->kind != CBM_TYPE_FUNC)
        return cbm_type_unknown();
    if (!sig->data.func.return_types || !sig->data.func.return_types[0])
        return cbm_type_unknown();
    if (!sig->data.func.return_types[1])
        return sig->data.func.return_types[0];
    int count = 0;
    while (sig->data.func.return_types[count])
        count++;
    // Multi-return → build a tuple. Needs a real arena: passing NULL here
    // crashed in cbm_arena_alloc when the cross-resolve path evaluated a
    // multi-return signature (only reachable once the per-file LSP O(n²) was
    // fixed and the resolve phase actually ran).
    return cbm_type_tuple(arena, sig->data.func.return_types, count);
}

const CBMType *ts_eval_expr_type(TSLSPContext *ctx, TSNode node) {
    if (!ctx || ts_node_is_null(node))
        return cbm_type_unknown();
    /* Memo hit: O(1), charges no budget, ignores depth — the value came from a
     * completed, non-degraded evaluation of this exact node. */
    {
        const CBMType *memo = ts_memo_get(ctx->eval_memo, node.id);
        if (memo)
            return memo;
    }
    if (ctx->eval_depth > TS_LSP_MAX_EVAL_DEPTH) {
        g_ts_eval_degraded++;
        return cbm_type_unknown();
    }
    /* Depth alone does not bound WORK: crafted expressions (e.g. the TS test
     * suite's repeated object spreads) stay under the depth cap while fanning
     * out exponentially — one 3.6 KB baseline file measured 11 s here. Charge
     * the same per-file budget the type-text parser uses and degrade to
     * UNKNOWN on exhaustion, exactly like that path. */
    if (g_ts_type_budget >= 0) {
        /* An eval entry does ~two orders of magnitude more work than one
         * text-parse unit (allocations, lookups, recursion bookkeeping), so it
         * charges accordingly — otherwise the default per-file budget still
         * permits ~12 s of evaluation on a crafted file. Normal files run
         * hundreds-to-thousands of entries, far under any budget. */
        g_ts_type_budget -= 16;
        if (g_ts_type_budget < 0) {
            if (!g_ts_type_budget_warned) {
                g_ts_type_budget_warned = true;
                fprintf(stderr, "  [tslsp] expression-eval budget exhausted; degrading to "
                                "unknown\n");
            }
            g_ts_eval_degraded++;
            return cbm_type_unknown();
        }
    }
    ctx->eval_depth++;
    /* Snapshot for the memo-store guard: any degraded return in this subtree
     * bumps the counter and blocks the store below. A read of a reassigned
     * local depends on the point of the walk, not on the node alone. */
    unsigned long degraded_before = g_ts_eval_degraded;
    unsigned long flow_before = ctx->flow_reads;

    const CBMType *result = cbm_type_unknown();
    const char *kind = ts_node_type(node);

    if (strcmp(kind, "identifier") == 0 || strcmp(kind, "shorthand_property_identifier") == 0) {
        char *name = node_text(ctx, node);
        if (name)
            result = type_of_identifier(ctx, name);
    } else if (strcmp(kind, "this") == 0) {
        /* The registry resolves static `this` from the same binding facts.
         * A class value must never be typed as an instance here. */
        result = ts_this_type(ctx, node);
    } else if (strcmp(kind, "super") == 0) {
        if (ctx->enclosing_class_qn) {
            const CBMRegisteredType *rt =
                cbm_registry_lookup_type(ctx->registry, ctx->enclosing_class_qn);
            if (rt && rt->embedded_types && rt->embedded_types[0]) {
                result = cbm_type_named(ctx->arena, rt->embedded_types[0]);
            }
        }
    } else if (strcmp(kind, "parenthesized_expression") == 0) {
        TSNode inner = ts_node_named_child(node, 0);
        result = ts_eval_expr_type(ctx, inner);
    } else if (strcmp(kind, "non_null_expression") == 0) {
        // `expr!` — strip the assertion, type unchanged.
        TSNode inner = ts_node_named_child(node, 0);
        result = ts_eval_expr_type(ctx, inner);
    } else if (strcmp(kind, "as_expression") == 0 || strcmp(kind, "satisfies_expression") == 0 ||
               strcmp(kind, "type_assertion") == 0) {
        // `expr as T` / `<T>expr` / `expr satisfies T`: type-position field gives the type.
        // For satisfies, we keep the asserted-type (TS narrows it but for resolution that's fine).
        TSNode type_node = ts_node_child_by_field_name(node, "type", TS_LSP_FIELD_LEN("type"));
        if (!ts_node_is_null(type_node)) {
            char *text = node_text(ctx, type_node);
            result = parse_ts_type_text(ctx->arena, text, ctx->module_qn);
        } else {
            // Last named child is the type for older grammars.
            uint32_t nc = ts_node_named_child_count(node);
            if (nc >= 2) {
                TSNode tn = ts_node_named_child(node, nc - 1);
                char *text = node_text(ctx, tn);
                result = parse_ts_type_text(ctx->arena, text, ctx->module_qn);
            }
        }
    } else if (strcmp(kind, "member_expression") == 0 ||
               strcmp(kind, "subscript_expression") == 0) {
        TSNode obj = ts_node_child_by_field_name(node, "object", TS_LSP_FIELD_LEN("object"));
        TSNode prop = ts_node_child_by_field_name(node, "property", TS_LSP_FIELD_LEN("property"));
        if (!ts_node_is_null(obj) && !ts_node_is_null(prop)) {
            const CBMType *recv = ts_eval_expr_type(ctx, obj);
            char *pname = node_text(ctx, prop);
            if (pname)
                result = lookup_member_type(ctx, recv, pname);
        }
    } else if (strcmp(kind, "new_expression") == 0) {
        const CBMType *nt = ts_new_expression_type(ctx, node);
        if (nt)
            result = nt;
    } else if (strcmp(kind, "call_expression") == 0) {
        TSNode fn = ts_node_child_by_field_name(node, "function", TS_LSP_FIELD_LEN("function"));
        if (!ts_node_is_null(fn)) {
            TSNode call_args =
                ts_node_child_by_field_name(node, "arguments", TS_LSP_FIELD_LEN("arguments"));
            const CBMType *fn_type = ts_signature_for_call(ctx, fn, call_args);
            if (ctx->debug) {
                fprintf(stderr, "[ts_lsp] eval call_expression: fn_kind=%s fn_type_kind=%d\n",
                        ts_node_type(fn), fn_type ? (int)fn_type->kind : -1);
            }
            if (fn_type && fn_type->kind == CBM_TYPE_FUNC) {
                result = return_type_of(ctx->arena, fn_type);

                // Polymorphic `this` return type: when the registered signature uses
                // `this` (TYPE_PARAM "this"), substitute the actual receiver type
                // from the call site (fn is a member_expression — its `object` is
                // the receiver). Powers fluent-builder patterns.
                if (result && result->kind == CBM_TYPE_TYPE_PARAM && result->data.type_param.name &&
                    strcmp(result->data.type_param.name, "this") == 0 &&
                    strcmp(ts_node_type(fn), "member_expression") == 0) {
                    TSNode obj =
                        ts_node_child_by_field_name(fn, "object", TS_LSP_FIELD_LEN("object"));
                    if (!ts_node_is_null(obj)) {
                        const CBMType *recv = ts_eval_expr_type(ctx, obj);
                        if (recv && !cbm_type_is_unknown(recv))
                            result = recv;
                    }
                }

                // Generic inference at call site: if the function has type parameters
                // referenced in return / param types, infer T from concrete arg types
                // and substitute. This is the simplest form of typescript-go's
                // inferTypeArguments — single-pass, argument-driven.
                if (result && result->kind == CBM_TYPE_TYPE_PARAM &&
                    fn_type->data.func.param_types) {
                    TSNode args = call_args;
                    if (!ts_node_is_null(args)) {
                        // Build a list of inferred type-param names + arg types.
                        const char *inf_names[8] = {0};
                        const CBMType *inf_args[8] = {0};
                        int ic = 0;
                        uint32_t pc = 0;
                        while (fn_type->data.func.param_types[pc])
                            pc++;
                        uint32_t argc = ts_node_named_child_count(args);
                        for (uint32_t i = 0; i < pc && i < argc && ic < 7; i++) {
                            const CBMType *pt = fn_type->data.func.param_types[i];
                            if (!pt || pt->kind != CBM_TYPE_TYPE_PARAM)
                                continue;
                            TSNode arg = ts_node_named_child(args, i);
                            if (ts_node_is_null(arg))
                                continue;
                            const CBMType *at = ts_eval_expr_type(ctx, arg);
                            if (cbm_type_is_unknown(at))
                                continue;
                            inf_names[ic] = pt->data.type_param.name;
                            inf_args[ic] = at;
                            ic++;
                        }
                        if (ic > 0) {
                            inf_names[ic] = NULL;
                            inf_args[ic] = NULL;
                            const CBMType *sub =
                                cbm_type_substitute(ctx->arena, result, inf_names, inf_args);
                            if (sub && !cbm_type_is_unknown(sub))
                                result = sub;
                        }
                    }
                }

                if (ctx->debug) {
                    const char *res_qn = (result && result->kind == CBM_TYPE_NAMED)
                                             ? result->data.named.qualified_name
                                             : "<other>";
                    fprintf(stderr, "[ts_lsp]   returns kind=%d qn=%s\n",
                            result ? (int)result->kind : -1, res_qn ? res_qn : "(null)");
                }
            }
        }
    } else if (strcmp(kind, "await_expression") == 0) {
        TSNode inner = ts_node_named_child(node, 0);
        const CBMType *t = ts_eval_expr_type(ctx, inner);
        result = ts_awaited_type_at(ctx, t, 0);
    } else if (strcmp(kind, "string") == 0 || strcmp(kind, "template_string") == 0) {
        result = cbm_type_builtin(ctx->arena, "string");
    } else if (strcmp(kind, "number") == 0) {
        result = cbm_type_builtin(ctx->arena, "number");
    } else if (strcmp(kind, "true") == 0 || strcmp(kind, "false") == 0) {
        result = cbm_type_builtin(ctx->arena, "boolean");
    } else if (strcmp(kind, "null") == 0) {
        result = cbm_type_builtin(ctx->arena, "null");
    } else if (strcmp(kind, "undefined") == 0) {
        result = cbm_type_builtin(ctx->arena, "undefined");
    } else if (strcmp(kind, "array") == 0) {
        // Use first element's type as Array<T> argument.
        const CBMType *elem = cbm_type_unknown();
        uint32_t nc = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < nc; i++) {
            TSNode c = ts_node_named_child(node, i);
            if (!ts_node_is_null(c)) {
                elem = ts_eval_expr_type(ctx, c);
                if (!cbm_type_is_unknown(elem))
                    break;
            }
        }
        const CBMType *args[2] = {elem, NULL};
        result = cbm_type_template(ctx->arena, "Array", args, 1);
    } else if (strcmp(kind, "object") == 0) {
        // Object literal — capture string-keyed property types.
        uint32_t nc = ts_node_named_child_count(node);
        const char *names[32] = {0};
        const CBMType *types[32] = {0};
        int count = 0;
        for (uint32_t i = 0; i < nc && count < 31; i++) {
            TSNode c = ts_node_named_child(node, i);
            if (ts_node_is_null(c))
                continue;
            const char *ck = ts_node_type(c);
            if (strcmp(ck, "pair") == 0) {
                TSNode key = ts_node_child_by_field_name(c, "key", TS_LSP_FIELD_LEN("key"));
                TSNode val = ts_node_child_by_field_name(c, "value", TS_LSP_FIELD_LEN("value"));
                if (!ts_node_is_null(key) && !ts_node_is_null(val)) {
                    char *k = node_text(ctx, key);
                    if (k) {
                        // Strip surrounding quotes if string key.
                        size_t kl = strlen(k);
                        if (kl >= 2 && (k[0] == '"' || k[0] == '\'') && k[kl - 1] == k[0]) {
                            k[kl - 1] = '\0';
                            k++;
                        }
                        names[count] = k;
                        types[count] = ts_eval_expr_type(ctx, val);
                        count++;
                    }
                }
            } else if (strcmp(ck, "shorthand_property_identifier") == 0) {
                char *k = node_text(ctx, c);
                if (k) {
                    names[count] = k;
                    types[count] = type_of_identifier(ctx, k);
                    count++;
                }
            }
        }
        names[count] = NULL;
        types[count] = NULL;
        result = cbm_type_object_lit(ctx->arena, names, types, NULL, NULL);
    } else if (strcmp(kind, "ternary_expression") == 0) {
        TSNode cons =
            ts_node_child_by_field_name(node, "consequence", TS_LSP_FIELD_LEN("consequence"));
        TSNode alt =
            ts_node_child_by_field_name(node, "alternative", TS_LSP_FIELD_LEN("alternative"));
        const CBMType *a = ts_eval_expr_type(ctx, cons);
        const CBMType *b = ts_eval_expr_type(ctx, alt);
        if (cbm_type_is_unknown(a))
            result = b;
        else if (cbm_type_is_unknown(b))
            result = a;
        else if (a == b)
            result = a;
        else {
            const CBMType *members[3] = {a, b, NULL};
            result = cbm_type_union(ctx->arena, members, 2);
        }
    } else if (strcmp(kind, "binary_expression") == 0) {
        // String concatenation `a + b` where either side is string → string.
        TSNode left = ts_node_child_by_field_name(node, "left", TS_LSP_FIELD_LEN("left"));
        TSNode right = ts_node_child_by_field_name(node, "right", TS_LSP_FIELD_LEN("right"));
        if (!ts_node_is_null(left) && !ts_node_is_null(right)) {
            const CBMType *l = ts_eval_expr_type(ctx, left);
            const CBMType *r = ts_eval_expr_type(ctx, right);
            if ((l && l->kind == CBM_TYPE_BUILTIN && l->data.builtin.name &&
                 strcmp(l->data.builtin.name, "string") == 0) ||
                (r && r->kind == CBM_TYPE_BUILTIN && r->data.builtin.name &&
                 strcmp(r->data.builtin.name, "string") == 0)) {
                result = cbm_type_builtin(ctx->arena, "string");
            } else {
                result = cbm_type_builtin(ctx->arena, "number");
            }
        }
    }

    ctx->eval_depth--;
    /* Store only completed, non-degraded evaluations (see g_ts_eval_degraded);
     * result is never NULL here (initialized to unknown), so NULL stays the
     * empty-slot sentinel. */
    if (result && g_ts_eval_degraded == degraded_before && ctx->flow_reads == flow_before)
        ts_memo_put(ctx, node.id, result);
    return result;
}

// Walk a parsed type and replace NAMED references whose bare name matches a known
// import binding. Recurses through TEMPLATE / UNION / INTERSECTION compound kinds.
//
// Naming convention: ctx->import_module_qns[i] is the imported module's QN (e.g.
// "test.conn"); to get the full type QN, we append the local-binding name. Falls back
// to the original type if no match.
static const CBMType *resolve_type_with_imports(TSLSPContext *ctx, const CBMType *t) {
    if (!t || !ctx)
        return t;

    if (t->kind == CBM_TYPE_NAMED && t->data.named.qualified_name) {
        const char *qn = t->data.named.qualified_name;
        const char *bare = qn;
        if (ctx->module_qn) {
            size_t module_len = strlen(ctx->module_qn);
            if (strncmp(qn, ctx->module_qn, module_len) == 0 && qn[module_len] == '.')
                bare = qn + module_len + 1;
        }
        /* Only a bare name or the local prefix added by the type parser can
         * denote an import. A qualified spelling keeps its owner; matching
         * just its last segment would redirect it to a same-name decoy. */
        if (strchr(bare, '.'))
            return t;

        // A registered local type shadows an import from an outer scope.
        if (ctx->module_qn) {
            const char *local_qn = bare != qn ? qn
                : cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, bare);
            const CBMRegisteredType *local_rt = cbm_registry_lookup_type(ctx->registry, local_qn);
            if (local_rt)
                return bare != qn ? t : cbm_type_named(ctx->arena, local_qn);
        }

        for (int i = 0; i < ctx->import_count; i++) {
            const char *lname = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
            const char *mqn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
            if (!lname || !mqn)
                continue;
            if (strcmp(lname, bare) != 0)
                continue;
            return cbm_type_named(ctx->arena,
                                  ts_import_symbol_qn(ctx, mqn, ts_import_export_name(ctx, bare)));
        }
        return t;
    }
    if (t->kind == CBM_TYPE_TEMPLATE && t->data.template_type.template_args &&
        t->data.template_type.arg_count > 0) {
        int ac = t->data.template_type.arg_count;
        const CBMType **new_args = (const CBMType **)cbm_arena_alloc(
            ctx->arena, (size_t)(ac + 1) * sizeof(const CBMType *));
        if (!new_args)
            return t;
        for (int i = 0; i < ac; i++) {
            new_args[i] = resolve_type_with_imports(ctx, t->data.template_type.template_args[i]);
        }
        new_args[ac] = NULL;
        /* The generic base has the same import identity as a named type.
         * Resolving only its arguments strands imported Packet<T> in this
         * module, so neither parameter nor field receivers find its methods. */
        const char *base_name = t->data.template_type.template_name;
        if (base_name) {
            const CBMType *base =
                resolve_type_with_imports(ctx, cbm_type_named(ctx->arena, base_name));
            if (base && base->kind == CBM_TYPE_NAMED)
                base_name = base->data.named.qualified_name;
        }
        return cbm_type_template(ctx->arena, base_name, new_args, ac);
    }
    if (t->kind == CBM_TYPE_UNION || t->kind == CBM_TYPE_INTERSECTION) {
        if (!t->data.union_type.members || t->data.union_type.count == 0)
            return t;
        int mc = t->data.union_type.count;
        const CBMType **new_members = (const CBMType **)cbm_arena_alloc(
            ctx->arena, (size_t)(mc + 1) * sizeof(const CBMType *));
        if (!new_members)
            return t;
        for (int i = 0; i < mc; i++) {
            new_members[i] = resolve_type_with_imports(ctx, t->data.union_type.members[i]);
        }
        new_members[mc] = NULL;
        return t->kind == CBM_TYPE_UNION ? cbm_type_union(ctx->arena, new_members, mc)
                                         : cbm_type_intersection(ctx->arena, new_members, mc);
    }
    return t;
}

const CBMType *ts_parse_type_node(TSLSPContext *ctx, TSNode node) {
    if (!ctx || ts_node_is_null(node))
        return cbm_type_unknown();
    char *text = node_text(ctx, node);
    const CBMType *parsed = parse_ts_type_text(ctx->arena, text, ctx->module_qn);
    return resolve_type_with_imports(ctx, parsed);
}

// ── Statement processing ──────────────────────────────────────────────────────

// Bind a variable_declarator: `let x: T = init` / `const x = init` / `var x = ...`.
/* Reserve local names before visiting their initializers or nested callables.
 * A not-yet-inferred local must shadow an outer typed receiver, not borrow it. */
static bool ts_is_pattern_container(const char *kind) {
    return strcmp(kind, "object_pattern") == 0 || strcmp(kind, "array_pattern") == 0 ||
           strcmp(kind, "rest_pattern") == 0 || strcmp(kind, "pair_pattern") == 0 ||
           strcmp(kind, "assignment_pattern") == 0 ||
           strcmp(kind, "object_assignment_pattern") == 0;
}

/* A child of a pattern binds names unless it is a pair key or a default value. */
static bool ts_pattern_child_binds(TSTreeCursor *cursor) {
    if (!ts_node_is_named(ts_tree_cursor_current_node(cursor)))
        return false;
    const char *field = ts_tree_cursor_current_field_name(cursor);
    return !field || strcmp(field, "value") == 0 || strcmp(field, "left") == 0;
}

/* Bind every name a pattern declares to unknown. The walk is iterative, so the
 * depth of a pattern cannot exhaust the stack. */
static void bind_unknown_pattern(TSLSPContext *ctx, TSNode pattern) {
    if (ts_node_is_null(pattern))
        return;
    TSTreeCursor cursor = ts_tree_cursor_new(pattern);
    uint32_t depth = 0;
    bool visit = true;
    for (;;) {
        if (visit) {
            TSNode node = ts_tree_cursor_current_node(&cursor);
            const char *kind = ts_node_type(node);
            if (strcmp(kind, "identifier") == 0 ||
                strcmp(kind, "shorthand_property_identifier_pattern") == 0) {
                char *name = node_text(ctx, node);
                if (name)
                    cbm_scope_bind(ctx->current_scope, name, cbm_type_unknown());
            } else if (ts_is_pattern_container(kind) && ts_tree_cursor_goto_first_child(&cursor)) {
                depth++;
                visit = ts_pattern_child_binds(&cursor);
                continue;
            }
        }
        while (depth > 0 && !ts_tree_cursor_goto_next_sibling(&cursor)) {
            ts_tree_cursor_goto_parent(&cursor);
            depth--;
        }
        if (depth == 0)
            break;
        visit = ts_pattern_child_binds(&cursor);
    }
    ts_tree_cursor_delete(&cursor);
}

static void shadow_block_declarations(TSLSPContext *ctx, TSNode block) {
    TSTreeCursor statements = ts_tree_cursor_new(block);
    if (ts_tree_cursor_goto_first_child(&statements)) {
        do {
            TSNode stmt = ts_tree_cursor_current_node(&statements);
            if (ts_is_function_declaration(stmt) &&
                !node_kind_is(ts_node_parent(block), "internal_module")) {
                TSNode name = ts_node_child_by_field_name(stmt, "name", TS_LSP_FIELD_LEN("name"));
                bind_unknown_pattern(ctx, name);
                continue;
            }
            /* A `var` belongs to the function (ts_hoist_vars). */
            if (!node_kind_is(stmt, "lexical_declaration"))
                continue;
            TSTreeCursor declarations = ts_tree_cursor_new(stmt);
            if (ts_tree_cursor_goto_first_child(&declarations)) {
                do {
                    TSNode decl = ts_tree_cursor_current_node(&declarations);
                    if (node_kind_is(decl, "variable_declarator")) {
                        TSNode name =
                            ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
                        bind_unknown_pattern(ctx, name);
                    }
                } while (ts_tree_cursor_goto_next_sibling(&declarations));
            }
            ts_tree_cursor_delete(&declarations);
        } while (ts_tree_cursor_goto_next_sibling(&statements));
    }
    ts_tree_cursor_delete(&statements);
}

/* A `var` or `let` declaration can be written again; a `const` cannot. */
static bool ts_declaration_writable(TSLSPContext *ctx, TSNode declaration) {
    if (node_kind_is(declaration, "variable_declaration"))
        return true;
    TSNode kind = ts_node_child_by_field_name(declaration, "kind", TS_LSP_FIELD_LEN("kind"));
    const char *text = ts_node_is_null(kind) ? NULL : node_text(ctx, kind);
    return text && strcmp(text, "let") == 0;
}

/* Destructuring patterns. Every name a pattern declares shadows an outer
 * binding of that name. A name gets a type only when the container type
 * proves it: a member of a known object type, a slot of a tuple, or the
 * element of a one-argument template such as Array<T>. A default value, a
 * rest element, a computed key or a pattern nested deeper than
 * TS_PATTERN_MAX_DEPTH leaves the name unknown. */
#define TS_PATTERN_MAX_DEPTH 64

/* The element an iteration of `container` yields, if one type proves it. */
static const CBMType *ts_iterated_type(const CBMType *container) {
    if (container && container->kind == CBM_TYPE_TEMPLATE &&
        container->data.template_type.template_args &&
        container->data.template_type.arg_count == 1 &&
        container->data.template_type.template_args[0])
        return container->data.template_type.template_args[0];
    return cbm_type_unknown();
}

static const CBMType *ts_pattern_slot_type(const CBMType *container, int index) {
    if (container && container->kind == CBM_TYPE_TUPLE) {
        if (container->data.tuple.elems && index < container->data.tuple.count &&
            container->data.tuple.elems[index])
            return container->data.tuple.elems[index];
        return cbm_type_unknown();
    }
    return ts_iterated_type(container);
}

/* The member a pair-pattern key names; NULL for a computed or numeric key. */
static char *ts_pattern_key_name(TSLSPContext *ctx, TSNode key) {
    if (node_kind_is(key, "property_identifier") || node_kind_is(key, "identifier"))
        return node_text(ctx, key);
    if (node_kind_is(key, "string") && ts_node_named_child_count(key) == 1) {
        TSNode fragment = ts_node_named_child(key, 0);
        if (node_kind_is(fragment, "string_fragment"))
            return node_text(ctx, fragment);
    }
    return NULL;
}

static void ts_bind_pattern(TSLSPContext *ctx, TSNode pattern, const CBMType *type,
                            bool writable, int depth) {
    if (ts_node_is_null(pattern))
        return;
    if (!type)
        type = cbm_type_unknown();
    const char *kind = ts_node_type(pattern);
    if (strcmp(kind, "identifier") == 0 ||
        strcmp(kind, "shorthand_property_identifier_pattern") == 0) {
        char *name = node_text(ctx, pattern);
        if (name)
            ts_bind_local(ctx, ctx->current_scope, name, type, NULL, writable);
        return;
    }
    bool object = strcmp(kind, "object_pattern") == 0;
    if ((!object && strcmp(kind, "array_pattern") != 0) || depth >= TS_PATTERN_MAX_DEPTH) {
        bind_unknown_pattern(ctx, pattern);
        return;
    }
    int slot = 0;
    TSTreeCursor cursor = ts_tree_cursor_new(pattern);
    if (ts_tree_cursor_goto_first_child(&cursor)) {
        do {
            TSNode child = ts_tree_cursor_current_node(&cursor);
            if (!ts_node_is_named(child)) {
                if (strcmp(ts_node_type(child), ",") == 0)
                    slot++;
                continue;
            }
            const CBMType *member = NULL;
            TSNode target = child;
            if (!object) {
                member = ts_pattern_slot_type(type, slot);
            } else if (node_kind_is(child, "shorthand_property_identifier_pattern")) {
                char *name = node_text(ctx, child);
                member = name ? lookup_member_type(ctx, type, name) : NULL;
            } else if (node_kind_is(child, "pair_pattern")) {
                TSNode key = ts_node_child_by_field_name(child, "key", TS_LSP_FIELD_LEN("key"));
                char *name = ts_pattern_key_name(ctx, key);
                member = name ? lookup_member_type(ctx, type, name) : NULL;
                target = ts_node_child_by_field_name(child, "value", TS_LSP_FIELD_LEN("value"));
            }
            ts_bind_pattern(ctx, target, member, writable, depth + 1);
        } while (ts_tree_cursor_goto_next_sibling(&cursor));
    }
    ts_tree_cursor_delete(&cursor);
}

static const CBMType *ts_declarator_type(TSLSPContext *ctx, TSNode decl,
                                         const CBMType **declared_out);

/* True when the collector recorded this `var` declarator as a write of
 * the binding its function hoists (ts_site_visit_var). */
static bool ts_var_writes_hoisted(const TSLSPContext *ctx, TSNode decl) {
    TSNode block = ts_node_parent(ts_node_parent(decl));
    if (node_kind_is(block, "export_statement"))
        block = ts_node_parent(block);
    if (node_kind_is(block, "program") ||
        (node_kind_is(block, "statement_block") && ts_is_flow_function(ts_node_parent(block))))
        return false; /* A body declaration still binds and checks its uniform-write proof. */
    const struct TsAssignSites *sites = ctx->assign_sites;
    TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
    if (!sites || !sites->by_start || ts_node_is_null(name))
        return false;
    uint32_t start = ts_node_start_byte(name);
    int lo = 0;
    int hi = sites->count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (sites->by_start[mid]->start < start)
            lo = mid + 1;
        else
            hi = mid;
    }
    return lo < sites->count && sites->by_start[lo]->start < ts_node_end_byte(name);
}

/* A nested `var` declarator writes the binding of its function. A straight-
 * line one gives the rest of its block the new type, as an assignment does. */
static void ts_var_redeclare(TSLSPContext *ctx, TSNode decl, bool straight) {
    TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
    const CBMType *bound = ts_declarator_type(ctx, decl, NULL);
    if (node_kind_is(name, "identifier")) {
        ts_flow_write(ctx, node_text(ctx, name), bound, straight);
        return;
    }
    ts_flow_write_pattern(ctx, name, 0);
    if (straight)
        ts_bind_pattern(ctx, name, bound, true, 0);
}

static bool ts_is_binding_pattern(TSNode node) {
    return node_kind_is(node, "object_pattern") || node_kind_is(node, "array_pattern") ||
           node_kind_is(node, "assignment_pattern") || node_kind_is(node, "rest_pattern");
}

/* The type a declarator gives its name: the annotation, else the value. */
static const CBMType *ts_declarator_type(TSLSPContext *ctx, TSNode decl,
                                         const CBMType **declared_out) {
    TSNode tann = ts_node_child_by_field_name(decl, "type", TS_LSP_FIELD_LEN("type"));
    TSNode value = ts_node_child_by_field_name(decl, "value", TS_LSP_FIELD_LEN("value"));
    const CBMType *declared = NULL;
    if (!ts_node_is_null(tann)) {
        // type_annotation contains the actual type as a named child.
        TSNode tch = ts_node_named_child(tann, 0);
        if (!ts_node_is_null(tch))
            declared = ts_parse_type_node(ctx, tch);
    }
    const CBMType *inferred =
        ts_node_is_null(value) ? cbm_type_unknown() : ts_eval_expr_type(ctx, value);
    if (declared_out)
        *declared_out = declared;
    return declared ? declared : inferred;
}

/* A declaration's lexical scope, widened for hoisted var bindings. */
static TSNode ts_proof_binding_scope(TSNode node, bool hoisted) {
    for (TSNode p = ts_node_parent(node); !ts_node_is_null(p); p = ts_node_parent(p)) {
        if (node_kind_is(p, "program") || ts_is_flow_function(p))
            return p;
        if (!hoisted && (node_kind_is(p, "statement_block") || node_kind_is(p, "switch_body") ||
                         node_kind_is(p, "for_statement") || node_kind_is(p, "for_in_statement") ||
                         node_kind_is(p, "catch_clause")))
            return p;
    }
    return (TSNode){0};
}

/* Built only for a reassigned concrete receiver. This one additional cursor
 * walk records shadow ranges; it never evaluates statements or emits calls. */
static bool ts_proof_shadows(TSLSPContext *ctx) {
    struct TsAssignSites *sites = ctx->assign_sites;
    if (sites->shadows_ready)
        return sites->shadows_complete;
    sites->shadows_ready = true;
    TsSiteVec names = {0};
    TSTreeCursor cursor = ts_tree_cursor_new(sites->root);
    for (;;) {
        TSNode node = ts_tree_cursor_current_node(&cursor);
        TSNode parent = ts_node_parent(node), pattern = {0}, scope = {0};
        const char *kind = ts_node_type(node);
        if (strcmp(kind, "variable_declarator") == 0) {
            pattern = ts_node_child_by_field_name(node, "name", 4);
            scope = ts_proof_binding_scope(node, node_kind_is(parent, "variable_declaration"));
        } else if (ts_is_function_declaration(node) || node_kind_is(node, "class_declaration")) {
            pattern = ts_node_child_by_field_name(node, "name", 4);
            scope = ts_proof_binding_scope(node, false);
        } else if (ts_is_function_value(node) || node_kind_is(node, "class")) {
            pattern = ts_node_child_by_field_name(node, "name", 4);
            scope = node; /* named expression: self-binding only */
        } else if (strcmp(kind, "required_parameter") == 0 ||
                   strcmp(kind, "optional_parameter") == 0) {
            pattern = ts_node_child_by_field_name(node, "pattern", 7);
            scope = ts_proof_binding_scope(node, true);
        } else if (node_kind_is(parent, "formal_parameters") ||
                   (node_kind_is(parent, "arrow_function") &&
                    ts_node_eq(ts_node_child_by_field_name(parent, "parameter", 9), node))) {
            pattern = node;
            scope = ts_proof_binding_scope(node, true);
        } else if (strcmp(kind, "catch_clause") == 0) {
            pattern = ts_node_child_by_field_name(node, "parameter", 9);
            scope = node;
        } else if (strcmp(kind, "for_in_statement") == 0) {
            TSNode decl_kind = ts_node_child_by_field_name(node, "kind", 4);
            if (!ts_node_is_null(decl_kind)) {
                pattern = ts_node_child_by_field_name(node, "left", 4);
                scope = node_kind_is(decl_kind, "var") ? ts_proof_binding_scope(node, true) : node;
            }
        }
        if (!ts_node_is_null(pattern) && !ts_node_is_null(scope) &&
            !node_kind_is(scope, "program")) {
            if (node_kind_is(pattern, "type_identifier"))
                ts_site_push(ctx, &names, pattern, ts_node_start_byte(scope),
                             ts_node_end_byte(scope));
            else
                ts_site_push_pattern(ctx, &names, pattern, ts_node_start_byte(scope),
                                     ts_node_end_byte(scope), 0);
        }
        if (names.failed)
            break;
        if (ts_tree_cursor_goto_first_child(&cursor))
            continue;
        while (!ts_tree_cursor_goto_next_sibling(&cursor)) {
            if (!ts_tree_cursor_goto_parent(&cursor))
                goto done;
        }
    }
done:
    ts_tree_cursor_delete(&cursor);
    if (names.failed)
        return false;
    if (names.count)
        qsort(names.items, (size_t)names.count, sizeof(*names.items), ts_site_name_cmp);
    sites->shadows = names.items;
    sites->shadow_count = names.count;
    sites->shadows_complete = true;
    return true;
}

static int ts_proof_first_name(const TsAssignSite *sites, int count, const char *name) {
    int lo = 0, hi = count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (strcmp(sites[mid].name, name) < 0)
            lo = mid + 1;
        else
            hi = mid;
    }
    return lo;
}

static bool ts_proof_name(TSLSPContext *ctx, TSNode node, const char *name) {
    const struct TsAssignSites *s = ctx->assign_sites;
    if (!name || !s || !s->complete)
        return false;
    int i = ts_proof_first_name(s->by_name, s->count, name);
    if (i < s->count && strcmp(s->by_name[i].name, name) == 0)
        return false; /* a constructor/factory/argument that is itself reassigned */
    if (ts_node_is_null(node))
        return true; /* The current lexical scope checks constructor shadows. */
    uint32_t at = ts_node_start_byte(node);
    for (i = ts_proof_first_name(s->shadows, s->shadow_count, name);
         i < s->shadow_count && strcmp(s->shadows[i].name, name) == 0; i++) {
        if (s->shadows[i].fn_start <= at && at < s->shadows[i].fn_end)
            return false;
    }
    return true;
}

/* Only expressions whose binding and argument types are independent of the
 * point of the statement walk may be read in a future write's scope. */
static bool ts_proof_expression(TSLSPContext *ctx, TSNode node, int depth) {
    if (ts_node_is_null(node) || depth > 16)
        return false;
    if (node_kind_is(node, "parenthesized_expression") || node_kind_is(node, "await_expression") ||
        node_kind_is(node, "non_null_expression"))
        return ts_proof_expression(ctx, ts_node_named_child(node, 0), depth + 1);
    if (node_kind_is(node, "number") || node_kind_is(node, "string") ||
        node_kind_is(node, "true") || node_kind_is(node, "false") || node_kind_is(node, "null") ||
        node_kind_is(node, "undefined"))
        return true;
    if (node_kind_is(node, "identifier")) {
        const char *name = node_text(ctx, node);
        return ts_proof_name(ctx, node, name) &&
               !cbm_type_is_unknown(type_of_identifier(ctx, name));
    }
    if (node_kind_is(node, "new_expression")) {
        TSNode ctor = ts_node_child_by_field_name(node, "constructor", 11);
        return node_kind_is(ctor, "identifier") && ts_proof_name(ctx, ctor, node_text(ctx, ctor));
    }
    if (!node_kind_is(node, "call_expression"))
        return false;
    TSNode fn = ts_node_child_by_field_name(node, "function", 8);
    if (!node_kind_is(fn, "identifier") || !ts_proof_name(ctx, fn, node_text(ctx, fn)))
        return false;
    const CBMType *signature = type_of_identifier(ctx, node_text(ctx, fn));
    if (!signature || signature->kind != CBM_TYPE_FUNC)
        return false;
    TSNode args = ts_node_child_by_field_name(node, "arguments", 9);
    for (uint32_t i = 0; i < ts_node_named_child_count(args); i++) {
        TSNode arg = ts_node_named_child(args, i);
        if (node_kind_is(arg, "comment"))
            continue;
        if (!ts_proof_expression(ctx, arg, depth + 1) ||
            cbm_type_is_unknown(ts_eval_expr_type(ctx, arg)))
            return false;
    }
    return true;
}

static bool ts_proof_context(TSNode node) {
    int depth = 0;
    for (TSNode p = node; !ts_node_is_null(p); p = ts_node_parent(p)) {
        if (++depth > 64 || node_kind_is(p, "with_statement") || node_kind_is(p, "internal_module"))
            return false;
    }
    return true;
}

static const CBMType *ts_uniform_write_type(TSLSPContext *ctx, const char *name,
                                            const CBMType *initial, TSNode initializer) {
    struct TsAssignSites *s = ctx->assign_sites;
    if (!s || !s->complete || !s->count || !initial || !name)
        return NULL;
    const CBMType *base = simplify_type(ctx, initial);
    if (!base || base->kind != CBM_TYPE_NAMED)
        return NULL;
    const CBMRegisteredType *type =
        cbm_registry_lookup_type(ctx->registry, base->data.named.qualified_name);
    if (!type || type->is_interface)
        return NULL;
    int lo = 0, hi = s->count;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        CBM_LSP_WORK(1);
        int cmp = strcmp(s->by_name[mid].name, name);
        if (cmp < 0 || (cmp == 0 && s->by_name[mid].start < ctx->fn_start))
            lo = mid + 1;
        else
            hi = mid;
    }
    int first = lo;
    if (first == s->count || strcmp(s->by_name[first].name, name) != 0 || !ts_proof_shadows(ctx))
        return NULL;
    if (!ts_proof_context(initializer) || !ts_proof_expression(ctx, initializer, 0))
        return NULL;
    bool seen = false;
    for (int i = first; i < s->count && strcmp(s->by_name[i].name, name) == 0; i++) {
        CBM_LSP_WORK(1);
        const TsAssignSite *site = &s->by_name[i];
        if (site->start >= ctx->fn_end)
            break;
        if (ts_node_is_null(site->value))
            return NULL;
        if (!ts_proof_context(site->value) || !ts_proof_expression(ctx, site->value, 0))
            return NULL;
        const CBMType *written = ts_eval_expr_type(ctx, site->value);
        if (!written || !cbm_type_equal(initial, written))
            return NULL;
        seen = true;
    }
    return seen ? initial : NULL;
}

static void bind_variable_declarator(TSLSPContext *ctx, TSNode decl, bool writable) {
    TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
    if (ts_node_is_null(name))
        return;
    const CBMType *declared = NULL;
    const CBMType *bound = ts_declarator_type(ctx, decl, &declared);

    if (node_kind_is(name, "identifier")) {
        char *nm = node_text(ctx, name);
        if (writable && !declared)
            declared = ts_uniform_write_type(ctx, nm, bound,
                                             ts_node_child_by_field_name(decl, "value", 5));
        ts_bind_local(ctx, ctx->current_scope, nm, bound, declared, writable);
    } else {
        ts_bind_pattern(ctx, name, bound, writable, 0);
    }
}

// Bind a single TS parameter into the current scope. Robust against grammar field-name
// variations: tries `pattern`, `name`, then falls back to first named child of the param.
static void bind_parameter(TSLSPContext *ctx, TSNode param) {
    const char *pk = ts_node_type(param);
    if (strcmp(pk, "identifier") == 0) {
        char *name = node_text(ctx, param);
        ts_bind_local(ctx, ctx->current_scope, name, cbm_type_unknown(), NULL, true);
        return;
    }
    /* JavaScript lists parameter patterns without a parameter node. */
    if (ts_is_binding_pattern(param)) {
        ts_bind_pattern(ctx, param, NULL, true, 0);
        return;
    }
    if (strcmp(pk, "required_parameter") != 0 && strcmp(pk, "optional_parameter") != 0 &&
        strcmp(pk, "tuple_parameter") != 0 && strcmp(pk, "optional_tuple_parameter") != 0)
        return;

    // Find pattern: try field "pattern", then "name", then first non-type named child.
    TSNode pattern = ts_node_child_by_field_name(param, "pattern", TS_LSP_FIELD_LEN("pattern"));
    if (ts_node_is_null(pattern)) {
        pattern = ts_node_child_by_field_name(param, "name", TS_LSP_FIELD_LEN("name"));
    }
    if (ts_node_is_null(pattern)) {
        uint32_t nc = ts_node_named_child_count(param);
        for (uint32_t i = 0; i < nc; i++) {
            TSNode c = ts_node_named_child(param, i);
            if (ts_node_is_null(c))
                continue;
            const char *k = ts_node_type(c);
            if (strcmp(k, "type_annotation") == 0)
                continue;
            if (strcmp(k, "decorator") == 0)
                continue;
            pattern = c;
            break;
        }
    }
    if (ts_node_is_null(pattern))
        return;

    // Find the type annotation: prefer field "type", fall back to descending into a child
    // of kind "type_annotation".
    TSNode tann = ts_node_child_by_field_name(param, "type", TS_LSP_FIELD_LEN("type"));
    if (ts_node_is_null(tann)) {
        uint32_t nc = ts_node_named_child_count(param);
        for (uint32_t i = 0; i < nc; i++) {
            TSNode c = ts_node_named_child(param, i);
            if (!ts_node_is_null(c) && strcmp(ts_node_type(c), "type_annotation") == 0) {
                tann = c;
                break;
            }
        }
    }

    const CBMType *t = cbm_type_unknown();
    if (!ts_node_is_null(tann)) {
        // The tree may give us either the type_annotation node or its inner type node.
        TSNode tch = (strcmp(ts_node_type(tann), "type_annotation") == 0)
                         ? ts_node_named_child(tann, 0)
                         : tann;
        if (!ts_node_is_null(tch)) {
            const char *tk = ts_node_type(tch);
            // Inline object type `{ a: T; b: U }` — walk members and build OBJECT_LIT
            // directly via AST. Falling back to text-parsing the node would yield UNKNOWN.
            if (strcmp(tk, "object_type") == 0) {
                const char *p_names[32] = {0};
                const CBMType *p_types[32] = {0};
                int pcount = 0;
                uint32_t omc = ts_node_named_child_count(tch);
                for (uint32_t oi = 0; oi < omc && pcount < 31; oi++) {
                    TSNode m = ts_node_named_child(tch, oi);
                    if (ts_node_is_null(m))
                        continue;
                    const char *mk = ts_node_type(m);
                    if (strcmp(mk, "property_signature") == 0) {
                        TSNode pname =
                            ts_node_child_by_field_name(m, "name", TS_LSP_FIELD_LEN("name"));
                        TSNode ptype =
                            ts_node_child_by_field_name(m, "type", TS_LSP_FIELD_LEN("type"));
                        if (ts_node_is_null(pname))
                            continue;
                        char *pnm_text = node_text(ctx, pname);
                        if (!pnm_text)
                            continue;
                        const CBMType *pt = cbm_type_unknown();
                        if (!ts_node_is_null(ptype)) {
                            TSNode ptch = (strcmp(ts_node_type(ptype), "type_annotation") == 0)
                                              ? ts_node_named_child(ptype, 0)
                                              : ptype;
                            if (!ts_node_is_null(ptch))
                                pt = ts_parse_type_node(ctx, ptch);
                        }
                        p_names[pcount] = pnm_text;
                        p_types[pcount] = pt;
                        pcount++;
                    }
                }
                p_names[pcount] = NULL;
                p_types[pcount] = NULL;
                t = cbm_type_object_lit(ctx->arena, p_names, p_types, NULL, NULL);
            } else {
                t = ts_parse_type_node(ctx, tch);
            }
        }
    }

    /* `...items: T[]`: the annotation types the whole rest array. */
    if (node_kind_is(pattern, "rest_pattern") &&
        node_kind_is(ts_node_named_child(pattern, 0), "identifier"))
        pattern = ts_node_named_child(pattern, 0);
    if (node_kind_is(pattern, "identifier")) {
        char *nm = node_text(ctx, pattern);
        ts_bind_local(ctx, ctx->current_scope, nm, t, t, true);
    } else {
        ts_bind_pattern(ctx, pattern, t, true, 0);
    }
}

/* True for `for (x of xs)`, false for `for (k in obj)`. */
static bool ts_for_header_iterates(TSNode loop) {
    bool of = node_kind_is(loop, "for_of_statement");
    TSTreeCursor cursor = ts_tree_cursor_new(loop);
    if (ts_tree_cursor_goto_first_child(&cursor)) {
        do {
            TSNode child = ts_tree_cursor_current_node(&cursor);
            if (ts_node_is_named(child))
                continue;
            const char *token = ts_node_type(child);
            if (strcmp(token, "of") == 0 || strcmp(token, "in") == 0) {
                of = token[0] == 'o';
                break;
            }
        } while (ts_tree_cursor_goto_next_sibling(&cursor));
    }
    ts_tree_cursor_delete(&cursor);
    return of;
}

void ts_process_statement(TSLSPContext *ctx, TSNode node) {
    if (!ctx || ts_node_is_null(node))
        return;
    const char *kind = ts_node_type(node);

    if (strcmp(kind, "lexical_declaration") == 0 || strcmp(kind, "variable_declaration") == 0) {
        bool writable = ts_declaration_writable(ctx, node);
        bool hoisted = strcmp(kind, "variable_declaration") == 0;
        bool straight = node.id == ctx->straight_stmt;
        uint32_t nc = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < nc; i++) {
            TSNode c = ts_node_named_child(node, i);
            if (!node_kind_is(c, "variable_declarator"))
                continue;
            if (hoisted && ts_node_is_null(ts_node_child_by_field_name(c, "value", 5)) &&
                ts_node_is_null(ts_node_child_by_field_name(c, "type", 4)))
                continue; /* An empty var redeclaration does not change its hoisted binding. */
            if (hoisted && ts_var_writes_hoisted(ctx, c))
                ts_var_redeclare(ctx, c, straight);
            else
                bind_variable_declarator(ctx, c, writable);
        }
    } else if (strcmp(kind, "for_in_statement") == 0 || strcmp(kind, "for_of_statement") == 0) {
        TSNode left = ts_node_child_by_field_name(node, "left", TS_LSP_FIELD_LEN("left"));
        TSNode right = ts_node_child_by_field_name(node, "right", TS_LSP_FIELD_LEN("right"));
        if (ts_node_is_null(left) || ts_node_is_null(right))
            return;
        /* `for (k in obj)` yields keys; only `of` yields the elements. */
        const CBMType *elem = ts_for_header_iterates(node)
                                  ? ts_iterated_type(ts_eval_expr_type(ctx, right))
                                  : cbm_type_unknown();
        TSNode decl_kind = ts_node_child_by_field_name(node, "kind", TS_LSP_FIELD_LEN("kind"));
        const char *decl_text = ts_node_is_null(decl_kind) ? NULL : node_text(ctx, decl_kind);
        bool writable = !decl_text || strcmp(decl_text, "const") != 0;
        TSNode target = left;
        if (node_kind_is(left, "lexical_declaration") ||
            node_kind_is(left, "variable_declaration")) {
            writable = ts_declaration_writable(ctx, left);
            TSNode v = ts_node_named_child(left, 0);
            target = node_kind_is(v, "variable_declarator")
                         ? ts_node_child_by_field_name(v, "name", TS_LSP_FIELD_LEN("name"))
                         : (TSNode){0};
        }
        ts_bind_pattern(ctx, target, elem, writable, 0);
    }
}

// ── Call resolution + tree walk ───────────────────────────────────────────────

static void resolve_value_references_at(TSLSPContext *ctx, TSNode call_node) {
    if (!ctx || !ctx->enclosing_func_qn) {
        return;
    }
    TSNode args =
        ts_node_child_by_field_name(call_node, "arguments", TS_LSP_FIELD_LEN("arguments"));
    if (ts_node_is_null(args)) {
        return;
    }
    uint32_t count = ts_node_named_child_count(args);
    for (uint32_t i = 0; i < count; i++) {
        TSNode arg = ts_node_named_child(args, i);
        if (node_kind_is(arg, "member_expression")) {
            /* A direct `receiver.method` value can be promoted only when a
             * lexical receiver has one concrete registered method.  Reject
             * unions/intersections here: lookup_method() otherwise returns the
             * first member, which would turn a multi-target value into false
             * precision. */
            if (!ctx->cross_file_mode) {
                continue;
            }
            TSNode object = ts_node_child_by_field_name(arg, "object", TS_LSP_FIELD_LEN("object"));
            TSNode property =
                ts_node_child_by_field_name(arg, "property", TS_LSP_FIELD_LEN("property"));
            if (!node_kind_is(object, "identifier") ||
                !node_kind_is(property, "property_identifier")) {
                continue;
            }
            char *object_name = node_text(ctx, object);
            char *method_name = node_text(ctx, property);
            if (!object_name || !method_name ||
                !ts_scope_has_binding(ctx->current_scope, object_name)) {
                continue;
            }
            const CBMType *receiver = ts_eval_expr_type(ctx, object);
            const CBMType *base = receiver ? simplify_type(ctx, receiver) : NULL;
            base = base ? unwrap_passthrough_template(base) : NULL;
            if (!base || (base->kind != CBM_TYPE_NAMED && base->kind != CBM_TYPE_TEMPLATE)) {
                continue;
            }
            const CBMRegisteredFunc *target = lookup_method(ctx, receiver, method_name);
            if (target && target->qualified_name) {
                ts_emit_resolved_reference(ctx, target->qualified_name,
                                           "lsp_ts_bound_method_value_reference", 0.95f, property);
            }
            continue;
        }
        if (!node_kind_is(arg, "identifier")) {
            continue;
        }
        char *name = node_text(ctx, arg);
        if (ts_scope_has_binding(ctx->current_scope, name)) {
            ts_block_shadowed_reference_usage(ctx, name, arg);
            continue;
        }
        /* Per-file resolution still performs the scope/shadow check above, but
         * promotion waits for the project-wide registry phase where the graph
         * target can be proved and materialized. */
        if (!ctx->cross_file_mode) {
            continue;
        }
        const CBMRegisteredFunc *target = ts_exact_same_module_function(ctx, name);
        const char *strategy = "lsp_ts_same_module_value_reference";
        const char *reason = NULL;
        if (!target) {
            target = ts_exact_imported_function(ctx, name);
            strategy = "lsp_ts_import_value_reference";
            /* `import { foo as bar }`: the site names `bar`, the target is `foo`. */
            if (target && ts_import_export_name(ctx, name) != name) {
                strategy = "lsp_callable_value_reference";
                reason = name;
            }
        }
        if (target) {
            ts_emit_resolved_reference_reason(ctx, target->qualified_name, strategy, 0.95f, reason,
                                              arg);
        }
    }
}

static TSNode unwrap_await_callee(TSNode node) {
    if (ts_node_is_null(node) || strcmp(ts_node_type(node), "await_expression") != 0 ||
        ts_node_named_child_count(node) == 0) {
        return node;
    }
    return ts_node_named_child(node, 0);
}

static void resolve_call_at(TSLSPContext *ctx, TSNode call_node) {
    TSNode fn = ts_node_child_by_field_name(call_node, "function", TS_LSP_FIELD_LEN("function"));
    fn = unwrap_await_callee(fn);
    if (ts_node_is_null(fn))
        return;

    TSNode args =
        ts_node_child_by_field_name(call_node, "arguments", TS_LSP_FIELD_LEN("arguments"));

    const char *fk = ts_node_type(fn);

    // member_expression: obj.method(...)
    if (strcmp(fk, "member_expression") == 0) {
        TSNode obj = ts_node_child_by_field_name(fn, "object", TS_LSP_FIELD_LEN("object"));
        TSNode prop = ts_node_child_by_field_name(fn, "property", TS_LSP_FIELD_LEN("property"));
        if (!ts_node_is_null(obj) && !ts_node_is_null(prop)) {
            char *mname = node_text(ctx, prop);
            if (mname) {
                // Identifier as namespace import: `name.fn()` or `mod.fn()`.
                if (node_kind_is(obj, "identifier")) {
                    char *on = node_text(ctx, obj);
                    if (on && !ts_scope_has_binding(ctx->current_scope, on) &&
                        !ts_import_is_instance(ctx, on)) {
                        bool is_import = false;
                        const CBMRegisteredFunc *f =
                            ts_lookup_namespace_call(ctx, on, mname, args, &is_import);
                        if (f) {
                            ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_namespace",
                                                     0.95f, call_node);
                            return;
                        }
                        if (is_import) {
                            ts_emit_unresolved_call_at(
                                ctx, cbm_arena_sprintf(ctx->arena, "%s.%s", on, mname),
                                ctx->cross_file_mode && ts_scope_has_binding(ctx->named_imports, on)
                                    ? "ts_import_value_receiver"
                                    : "module_symbol_not_in_registry",
                                call_node);
                            return;
                        }
                    }
                }
                // Type-based dispatch.
                const CBMType *recv = ts_eval_expr_type(ctx, obj);
                const CBMRegisteredFunc *f = ts_lookup_method_for_call(ctx, recv, mname, args);

                if (f) {
                    ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_method", 0.95f,
                                             call_node);
                    return;
                }
                const char *object_name =
                    node_kind_is(obj, "identifier") ? node_text(ctx, obj) : NULL;
                ts_emit_unresolved_call_at(ctx, mname,
                                           object_name && ts_import_is_instance(ctx, object_name)
                                               ? "ts_import_value_receiver"
                                               : "method_not_in_registry",
                                           call_node);
            }
        }
        return;
    }

    // identifier: free function call.
    if (strcmp(fk, "identifier") == 0) {
        char *name = node_text(ctx, fn);
        if (!name)
            return;
        if (ts_scope_has_binding(ctx->current_scope, name))
            return;

        // Imported default/named function.
        for (int i = 0; i < ctx->import_count; i++) {
            const char *lname = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
            const char *mqn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
            if (lname && mqn && strcmp(lname, name) == 0) {
                const char *member = ts_import_export_name(ctx, name);
                const CBMRegisteredFunc *f = ts_lookup_symbol_for_call(ctx, mqn, member, args);
                if (f && member != name) {
                    ts_emit_resolved_call_reason_at(ctx, f->qualified_name, "lsp_import_alias",
                                                    0.95f, name, call_node);
                    return;
                }
                if (f) {
                    ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_import", 0.95f,
                                             call_node);
                    return;
                }
                // Fall through to qualified_name fallback.
                const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", mqn, member);
                ts_emit_unresolved_call_at(ctx, qn, "import_symbol_not_in_registry", call_node);
                return;
            }
        }
        // Module-local function: ordered argument types first, then arity.
        if (ts_is_module_callable(ctx, name)) {
            const CBMRegisteredFunc *f = ts_lookup_symbol_for_call(ctx, ctx->module_qn, name, args);
            if (f) {
                ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_local", 0.95f, call_node);
                return;
            }
        }
        ts_emit_unresolved_call_at(ctx, name, "func_not_in_registry", call_node);
    }
}

typedef struct {
    CBMScope *scope;
    uint32_t start;
    uint32_t end;
} TsFnSave;

/* The frame just pushed is the function's: its own writes are flow, and a
 * read through it of an outer reassigned local is not proven. */
static TsFnSave ts_enter_function(TSLSPContext *ctx, TSNode fn) {
    TsFnSave saved = {ctx->fn_scope, ctx->fn_start, ctx->fn_end};
    ctx->fn_scope = ctx->current_scope;
    ctx->fn_start = ts_node_start_byte(fn);
    ctx->fn_end = ts_node_end_byte(fn);
    ts_hoist_vars(ctx);
    return saved;
}

static void ts_leave_function(TSLSPContext *ctx, TsFnSave saved) {
    ctx->fn_scope = saved.scope;
    ctx->fn_start = saved.start;
    ctx->fn_end = saved.end;
}

/* Walk one statement of a block whose frame is current: an assignment it
 * makes directly is straight-line code of that frame. */
static void process_block_statement(TSLSPContext *ctx, TSNode stmt) {
    ctx->straight_stmt = stmt.id;
    process_node(ctx, stmt);
}

static void ts_process_assignment(TSLSPContext *ctx, TSNode node, bool straight) {
    TSNode left = ts_node_child_by_field_name(node, "left", TS_LSP_FIELD_LEN("left"));
    TSNode right = ts_node_child_by_field_name(node, "right", TS_LSP_FIELD_LEN("right"));
    if (node_kind_is(node, "augmented_assignment_expression"))
        straight = false; /* `x ??= y` keeps x or takes y */
    if (!ts_node_is_null(right))
        process_node(ctx, right);
    while (ts_write_wrapper(left))
        left = ts_write_operand(left);
    if (node_kind_is(left, "identifier")) {
        const CBMType *value = straight ? ts_eval_expr_type(ctx, right) : NULL;
        ts_flow_write(ctx, node_text(ctx, left), value, straight);
    } else if (node_kind_is(left, "object_pattern") || node_kind_is(left, "array_pattern")) {
        process_node(ctx, left); /* default values can call */
        ts_flow_write_pattern(ctx, left, 0);
    } else if (!ts_node_is_null(left)) {
        process_node(ctx, left);
    }
}

/* The expression of a straight-line statement: a comma list runs in order. */
static void ts_walk_straight_expression(TSLSPContext *ctx, TSNode expr) {
    for (;;) {
        while (node_kind_is(expr, "parenthesized_expression") &&
               ts_node_named_child_count(expr) == 1)
            expr = ts_node_named_child(expr, 0);
        if (node_kind_is(expr, "assignment_expression")) {
            ts_process_assignment(ctx, expr, true);
            return;
        }
        if (!node_kind_is(expr, "sequence_expression")) {
            process_node(ctx, expr);
            return;
        }
        /* The last operand may be the rest of the list: continue with it
         * instead of recursing, so a long minified list stays flat. */
        TSNode last = {0};
        bool have_last = false;
        TSTreeCursor cursor = ts_tree_cursor_new(expr);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                TSNode child = ts_tree_cursor_current_node(&cursor);
                if (!ts_node_is_named(child))
                    continue;
                if (have_last)
                    ts_walk_straight_expression(ctx, last);
                last = child;
                have_last = true;
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
        if (!have_last)
            return;
        expr = last;
    }
}

// Process an arrow_function or function_expression as a callback whose param types are
// contextually typed by the enclosing call (e.g. `arr.map(x => x.length)` — `x` should
// be bound to `arr`'s element type via Array<T>.map's `(x: T) => U` signature). The
// caller passes `expected` = the FUNC type the callback must conform to.
static void process_callback_arrow(TSLSPContext *ctx, TSNode arrow, const CBMType *expected) {
    if (ts_node_is_null(arrow) || !expected || expected->kind != CBM_TYPE_FUNC)
        return;

    CBMScope *saved = ctx->current_scope;
    ctx->current_scope = cbm_scope_push(ctx->arena, saved);
    TsFnSave fn_saved = ts_enter_function(ctx, arrow);

    // Tree-sitter typescript shapes for arrow functions:
    //   `(x, y) => body`  → parameters: formal_parameters
    //   `x => body`       → parameter: identifier (singular field)
    TSNode params =
        ts_node_child_by_field_name(arrow, "parameters", TS_LSP_FIELD_LEN("parameters"));
    TSNode bare_param =
        ts_node_child_by_field_name(arrow, "parameter", TS_LSP_FIELD_LEN("parameter"));
    int idx = 0;
    if (!ts_node_is_null(bare_param)) {
        // Single bare param: `x => ...`.
        const char *pk = ts_node_type(bare_param);
        if (strcmp(pk, "identifier") == 0) {
            char *nm = node_text(ctx, bare_param);
            const CBMType *pt =
                (expected->data.func.param_types && expected->data.func.param_types[0])
                    ? expected->data.func.param_types[0]
                    : cbm_type_unknown();
            ts_bind_local(ctx, ctx->current_scope, nm, pt, pt, true);
        }
    } else if (!ts_node_is_null(params)) {
        uint32_t pc = ts_node_named_child_count(params);
        for (uint32_t i = 0; i < pc; i++) {
            TSNode p = ts_node_named_child(params, i);
            if (ts_node_is_null(p))
                continue;
            const char *pk = ts_node_type(p);
            const char *pname = NULL;
            TSNode pattern = {0};
            const CBMType *expected_pt =
                (expected->data.func.param_types && expected->data.func.param_types[idx])
                    ? expected->data.func.param_types[idx]
                    : NULL;

            if (strcmp(pk, "identifier") == 0) {
                pname = node_text(ctx, p);
            } else if (ts_is_binding_pattern(p)) {
                pattern = p; /* JavaScript: a pattern without a parameter node */
            } else {
                // required_parameter / optional_parameter — extract pattern.
                TSNode pp = ts_node_child_by_field_name(p, "pattern", TS_LSP_FIELD_LEN("pattern"));
                if (ts_node_is_null(pp)) {
                    pp = ts_node_child_by_field_name(p, "name", TS_LSP_FIELD_LEN("name"));
                }
                if (!ts_node_is_null(pp) && strcmp(ts_node_type(pp), "identifier") == 0) {
                    pname = node_text(ctx, pp);
                } else {
                    pattern = pp;
                }
                // If the param has its own annotation, use that. Otherwise use expected.
                TSNode tann = ts_node_child_by_field_name(p, "type", TS_LSP_FIELD_LEN("type"));
                if (!ts_node_is_null(tann)) {
                    TSNode tch = (strcmp(ts_node_type(tann), "type_annotation") == 0)
                                     ? ts_node_named_child(tann, 0)
                                     : tann;
                    if (!ts_node_is_null(tch)) {
                        const CBMType *annotated = ts_parse_type_node(ctx, tch);
                        if (!cbm_type_is_unknown(annotated)) {
                            expected_pt = annotated;
                        }
                    }
                }
            }
            if (pname) {
                ts_bind_local(ctx, ctx->current_scope, pname,
                              expected_pt ? expected_pt : cbm_type_unknown(), expected_pt, true);
            } else if (!ts_node_is_null(pattern)) {
                /* A rest element collects the remaining arguments, not this one. */
                bool rest = node_kind_is(pattern, "rest_pattern");
                ts_bind_pattern(ctx, pattern, rest ? NULL : expected_pt, true, 0);
            }
            idx++;
        }
    }

    TSNode body = ts_node_child_by_field_name(arrow, "body", TS_LSP_FIELD_LEN("body"));
    if (!ts_node_is_null(body)) {
        if (strcmp(ts_node_type(body), "statement_block") == 0) {
            shadow_block_declarations(ctx, body);
            TSTreeCursor cursor = ts_tree_cursor_new(body);
            if (ts_tree_cursor_goto_first_child(&cursor)) {
                do {
                    process_block_statement(ctx, ts_tree_cursor_current_node(&cursor));
                } while (ts_tree_cursor_goto_next_sibling(&cursor));
            }
            ts_tree_cursor_delete(&cursor);
        } else {
            process_node(ctx, body);
        }
    }

    ts_leave_function(ctx, fn_saved);
    ctx->current_scope = saved;
}

// Try to extract a narrowing fact from an `if`-condition: `x instanceof Foo`,
// `typeof x === 'string'`, or `x.kind === 'lit'` (discriminated union).
// On success: writes the narrowed variable name and target type, plus whether the
// match polarity is `==` (true → consequence) or `!=` (true → alternative).
// Returns true if narrowing applies.
static bool extract_narrowing(TSLSPContext *ctx, TSNode condition, const char **out_var,
                              const CBMType **out_type, bool *out_inverted) {
    *out_var = NULL;
    *out_type = NULL;
    *out_inverted = false;
    if (ts_node_is_null(condition))
        return false;

    // Strip outer parens if any.
    while (!ts_node_is_null(condition) &&
           strcmp(ts_node_type(condition), "parenthesized_expression") == 0) {
        condition = ts_node_named_child(condition, 0);
    }
    if (ts_node_is_null(condition))
        return false;
    const char *k = ts_node_type(condition);

    // `x instanceof Foo`: binary_expression with operator "instanceof".
    if (strcmp(k, "binary_expression") == 0) {
        TSNode op =
            ts_node_child_by_field_name(condition, "operator", TS_LSP_FIELD_LEN("operator"));
        char *opt = ts_node_is_null(op) ? NULL : node_text(ctx, op);
        TSNode left = ts_node_child_by_field_name(condition, "left", TS_LSP_FIELD_LEN("left"));
        TSNode right = ts_node_child_by_field_name(condition, "right", TS_LSP_FIELD_LEN("right"));

        if (opt && strcmp(opt, "instanceof") == 0 && !ts_node_is_null(left) &&
            !ts_node_is_null(right) && strcmp(ts_node_type(left), "identifier") == 0 &&
            strcmp(ts_node_type(right), "identifier") == 0) {
            *out_var = node_text(ctx, left);
            char *class_name = node_text(ctx, right);
            if (class_name) {
                *out_type = parse_ts_type_text(ctx->arena, class_name, ctx->module_qn);
                *out_type = resolve_type_with_imports(ctx, *out_type);
            }
            return *out_var && *out_type;
        }

        // `typeof x === 'string'` / `typeof x !== 'number'`
        if (opt &&
            (strcmp(opt, "===") == 0 || strcmp(opt, "==") == 0 || strcmp(opt, "!==") == 0 ||
             strcmp(opt, "!=") == 0) &&
            !ts_node_is_null(left) && !ts_node_is_null(right)) {
            bool inverted = (strcmp(opt, "!==") == 0 || strcmp(opt, "!=") == 0);

            // typeof x === 'string'
            if (strcmp(ts_node_type(left), "unary_expression") == 0) {
                TSNode op2 =
                    ts_node_child_by_field_name(left, "operator", TS_LSP_FIELD_LEN("operator"));
                char *opt2 = ts_node_is_null(op2) ? NULL : node_text(ctx, op2);
                TSNode arg =
                    ts_node_child_by_field_name(left, "argument", TS_LSP_FIELD_LEN("argument"));
                if (opt2 && strcmp(opt2, "typeof") == 0 && !ts_node_is_null(arg) &&
                    strcmp(ts_node_type(arg), "identifier") == 0 &&
                    strcmp(ts_node_type(right), "string") == 0) {
                    *out_var = node_text(ctx, arg);
                    char *lit = node_text(ctx, right);
                    if (lit) {
                        // Strip surrounding quotes.
                        size_t ll = strlen(lit);
                        if (ll >= 2 && (lit[0] == '"' || lit[0] == '\'') && lit[ll - 1] == lit[0]) {
                            lit[ll - 1] = '\0';
                            lit++;
                        }
                        *out_type = cbm_type_builtin(ctx->arena, lit);
                    }
                    *out_inverted = inverted;
                    return *out_var && *out_type;
                }
            }
        }
    }

    return false;
}

/* The type of name where a narrowing test failed: its union without the
 * members the test proves (`x instanceof A` removes A, `typeof x ===
 * 'string'` removes string). NULL when the test removes no member, or all. */
static const CBMType *ts_narrow_excluding(TSLSPContext *ctx, const char *name,
                                          const CBMType *matched) {
    const CBMType *current = ts_lookup_binding_type(ctx, name);
    const CBMType *u = current ? simplify_type(ctx, current) : NULL;
    if (!u || u->kind != CBM_TYPE_UNION || !u->data.union_type.members || !matched)
        return NULL;
    int count = u->data.union_type.count;
    if (count <= 0)
        return NULL;
    const CBMType *want = simplify_type(ctx, matched);
    const CBMType **rest =
        (const CBMType **)cbm_arena_alloc(ctx->arena, (size_t)count * sizeof(*rest));
    if (!rest)
        return NULL;
    int n = 0;
    for (int i = 0; i < count; i++) {
        const CBMType *member = u->data.union_type.members[i];
        const CBMType *simple = simplify_type(ctx, member);
        if (cbm_type_equal(member, matched) || (simple && want && cbm_type_equal(simple, want)))
            continue;
        rest[n++] = member;
    }
    if (n == 0 || n == count)
        return NULL;
    return n == 1 ? rest[0] : cbm_type_union(ctx->arena, rest, n);
}

/* Walk one branch of an if statement, with name bound to type when known. */
static void ts_walk_narrowed(TSLSPContext *ctx, TSNode branch, const char *name,
                             const CBMType *type) {
    if (ts_node_is_null(branch))
        return;
    if (!name || !type) {
        process_node(ctx, branch);
        return;
    }
    CBMScope *saved = ctx->current_scope;
    ctx->current_scope = cbm_scope_push(ctx->arena, saved);
    cbm_scope_bind(ctx->current_scope, name, type);
    process_node(ctx, branch);
    ctx->current_scope = saved;
}

// Look up a union member that satisfies a discriminant: when narrowed via `x.kind ===
// 'foo'`, find the member of x's type whose `kind` property is the literal 'foo'.
// Returns NULL if no match. Pragmatic v1: only handles `member_expression === string`.
static const CBMType *narrow_discriminated_union(TSLSPContext *ctx, TSNode condition,
                                                 const char **out_var) {
    *out_var = NULL;
    if (ts_node_is_null(condition))
        return NULL;
    while (!ts_node_is_null(condition) &&
           strcmp(ts_node_type(condition), "parenthesized_expression") == 0) {
        condition = ts_node_named_child(condition, 0);
    }
    if (ts_node_is_null(condition))
        return NULL;
    if (strcmp(ts_node_type(condition), "binary_expression") != 0)
        return NULL;

    TSNode op = ts_node_child_by_field_name(condition, "operator", TS_LSP_FIELD_LEN("operator"));
    char *opt = ts_node_is_null(op) ? NULL : node_text(ctx, op);
    if (!opt || (strcmp(opt, "===") != 0 && strcmp(opt, "==") != 0))
        return NULL;

    TSNode left = ts_node_child_by_field_name(condition, "left", TS_LSP_FIELD_LEN("left"));
    TSNode right = ts_node_child_by_field_name(condition, "right", TS_LSP_FIELD_LEN("right"));
    if (ts_node_is_null(left) || ts_node_is_null(right))
        return NULL;

    // left = `x.kind`, right = string literal.
    if (strcmp(ts_node_type(left), "member_expression") != 0 ||
        strcmp(ts_node_type(right), "string") != 0)
        return NULL;

    TSNode obj = ts_node_child_by_field_name(left, "object", TS_LSP_FIELD_LEN("object"));
    TSNode prop = ts_node_child_by_field_name(left, "property", TS_LSP_FIELD_LEN("property"));
    if (ts_node_is_null(obj) || strcmp(ts_node_type(obj), "identifier") != 0)
        return NULL;
    if (ts_node_is_null(prop))
        return NULL;
    char *var_name = node_text(ctx, obj);
    char *prop_name = node_text(ctx, prop);
    char *lit = node_text(ctx, right);
    if (!var_name || !prop_name || !lit)
        return NULL;
    size_t ll = strlen(lit);
    if (ll >= 2 && (lit[0] == '"' || lit[0] == '\'') && lit[ll - 1] == lit[0]) {
        lit[ll - 1] = '\0';
        lit++;
    }

    const CBMType *var_type = ts_lookup_binding_type(ctx, var_name);
    if (!var_type || var_type->kind != CBM_TYPE_UNION)
        return NULL;
    if (!var_type->data.union_type.members)
        return NULL;

    for (int i = 0; i < var_type->data.union_type.count; i++) {
        const CBMType *m = var_type->data.union_type.members[i];
        if (!m || m->kind != CBM_TYPE_NAMED)
            continue;
        const CBMRegisteredType *rt =
            cbm_registry_lookup_type(ctx->registry, m->data.named.qualified_name);
        if (!rt || !rt->field_names || !rt->field_types)
            continue;
        for (int j = 0; rt->field_names[j]; j++) {
            if (strcmp(rt->field_names[j], prop_name) != 0)
                continue;
            const CBMType *ft = rt->field_types[j];
            if (!ft)
                continue;
            // Discriminant fields are typically string-literal types (`'circle'`) or
            // the BUILTIN("string") fallback. For BUILTIN fallback we can't narrow
            // precisely, so skip unless the parsed text matches our literal.
            if (ft->kind == CBM_TYPE_TS_LITERAL && ft->data.literal_ts.value &&
                strcmp(ft->data.literal_ts.value, lit) == 0) {
                *out_var = var_name;
                return m;
            }
            // Some interfaces declare `kind: 'circle'` as NAMED("'circle'") via
            // text fall-through; handle that too.
            if (ft->kind == CBM_TYPE_NAMED && ft->data.named.qualified_name) {
                const char *qn = ft->data.named.qualified_name;
                size_t qnl = strlen(qn);
                if (qnl >= 2 && (qn[0] == '\'' || qn[0] == '"') && qn[qnl - 1] == qn[0]) {
                    if (strncmp(qn + 1, lit, qnl - 2) == 0 && strlen(lit) == qnl - 2) {
                        *out_var = var_name;
                        return m;
                    }
                }
            }
        }
    }
    return NULL;
}

// Resolve a JSX element opening — emits a resolved call edge for component invocations.
// `<Foo prop={x}/>` and `<Foo>...</Foo>` both invoke the component as a function.
// Lowercase first letter is treated as a JSX intrinsic (HTML element) and ignored.
static void resolve_jsx_element(TSLSPContext *ctx, TSNode element_node) {
    if (!ctx->jsx_mode)
        return;
    // The element's first named child is the opening element (or self-closing).
    const char *kind = ts_node_type(element_node);
    TSNode tag = element_node;
    if (strcmp(kind, "jsx_element") == 0) {
        TSNode opening = ts_node_named_child(element_node, 0);
        if (!ts_node_is_null(opening))
            tag = opening;
    }

    // Get the name from the opening / self_closing element. Field is "name".
    TSNode name_node = ts_node_child_by_field_name(tag, "name", TS_LSP_FIELD_LEN("name"));
    if (ts_node_is_null(name_node))
        return;
    char *tag_name = node_text(ctx, name_node);
    if (!tag_name || !tag_name[0])
        return;
    // Lowercase first → intrinsic (HTML element). Skip emission.
    if (tag_name[0] >= 'a' && tag_name[0] <= 'z')
        return;

    /* Parameters and locals own the JSX identifier before module/import
     * symbols.  They may still be callable at runtime, but without a graph
     * node for that lexical value we must fail closed instead of redirecting
     * the tag to a same-named component definition. */
    if (ts_scope_has_binding(ctx->current_scope, tag_name))
        return;

    // Resolve as a free-function/component call.
    if (ctx->module_qn) {
        const CBMRegisteredFunc *f =
            cbm_registry_lookup_symbol(ctx->registry, ctx->module_qn, tag_name);
        if (f) {
            ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_jsx", 0.95f, tag);
            return;
        }
    }
    // Try imports.
    for (int i = 0; i < ctx->import_count; i++) {
        const char *lname = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
        const char *mqn = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
        if (lname && mqn && strcmp(lname, tag_name) == 0) {
            /* A relative module path ("./widget") is unresolved at the per-file
             * stage — it is the raw specifier, not a module QN, so "./widget.Widget"
             * matches no node and (winning the join on equal confidence) would drop
             * the edge. The cross-file pass re-runs with the path resolved to the
             * real module QN and emits the correct resolution, so skip the per-file
             * emission for relative specifiers and let that one stand. */
            if (mqn[0] == '.') {
                ts_emit_unresolved_call_at(ctx, tag_name, "jsx_import_unresolved_path", tag);
                return;
            }
            /* The import establishes lexical ownership, but a raw package or
             * tsconfig-alias specifier is not a semantic target.  Require the
             * current (per-file or cross-file overlay) registry to materialize
             * the exact component before emitting CALLS.  An unresolved
             * per-file row deliberately keeps the file eligible for the
             * cross-file pass, where resolved import QNs and project defs are
             * available. */
            const char *member = ts_import_export_name(ctx, tag_name);
            const CBMRegisteredFunc *f = cbm_registry_lookup_symbol(ctx->registry, mqn, member);
            if (f && member != tag_name) {
                ts_emit_resolved_call_reason_at(ctx, f->qualified_name, "lsp_import_alias", 0.95f,
                                                tag_name, tag);
                return;
            }
            if (f) {
                ts_emit_resolved_call_at(ctx, f->qualified_name, "lsp_ts_jsx_import", 0.95f, tag);
                return;
            }
            ts_emit_unresolved_call_at(ctx, tag_name, "jsx_component_not_in_registry", tag);
            return;
        }
    }
    ts_emit_unresolved_call_at(ctx, tag_name, "jsx_component_not_in_registry", tag);
}

/* Namespace members need the same function boundary handling as top-level
 * declarations. Generic recursion can find their calls, but without setting
 * enclosing_func_qn it cannot attribute those calls to the namespace member. */
static void process_namespace_member(TSLSPContext *ctx, TSNode node) {
    if (!ctx || ts_node_is_null(node))
        return;

    const char *kind = ts_node_type(node);
    if (strcmp(kind, "export_statement") == 0) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++)
            process_namespace_member(ctx, ts_node_named_child(node, i));
        return;
    }

    if (ts_is_function_declaration(node) && ctx->module_qn) {
        TSNode name = ts_node_child_by_field_name(node, "name", TS_LSP_FIELD_LEN("name"));
        if (!ts_node_is_null(name)) {
            char *function_name = node_text(ctx, name);
            if (function_name) {
                const char *function_qn =
                    cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, function_name);
                process_function_body(ctx, node, function_qn, NULL);
                return;
            }
        }
    }

    process_node(ctx, node);
}

static void process_node_inner(TSLSPContext *ctx, TSNode node);

/* Depth-guarded entry for the statement walk. Each nested callback, block or
 * expression recurses once, so a deeply nested file could overflow the native
 * stack. Past CBM_LSP_MAX_WALK_DEPTH the subtree is skipped and its calls stay
 * unresolved (see resolve_calls_in_node in go_lsp.c). */
static void process_node(TSLSPContext *ctx, TSNode node) {
    if (!ctx || ts_node_is_null(node) || ctx->walk_depth >= cbm_lsp_max_walk_depth())
        return;
    ctx->walk_depth++;
#ifdef CBM_ENABLE_TEST_SEAMS
    if (ctx->walk_depth > g_ts_max_walk_depth)
        g_ts_max_walk_depth = ctx->walk_depth;
#endif
    process_node_inner(ctx, node);
    ctx->walk_depth--;
}

static void process_node_inner(TSLSPContext *ctx, TSNode node) {
    const char *kind = ts_node_type(node);

    /* A nested statement block owns `let`/`const` declarations. Function-body
     * blocks are intentionally unwrapped by process_function_body(), so this
     * branch applies only to nested lexical blocks and cannot hide parameters. */
    if (strcmp(kind, "statement_block") == 0) {
        CBMScope *saved = ctx->current_scope;
        ctx->current_scope = cbm_scope_push(ctx->arena, saved);
        shadow_block_declarations(ctx, node);
        TSTreeCursor cursor = ts_tree_cursor_new(node);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                process_block_statement(ctx, ts_tree_cursor_current_node(&cursor));
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
        ctx->current_scope = saved;
        return;
    }

    /* Loop-header and catch bindings must not replace a receiver in the
     * surrounding module/function. Unknown catch parameters still shadow it. */
    if (strcmp(kind, "for_statement") == 0 || strcmp(kind, "for_in_statement") == 0 ||
        strcmp(kind, "for_of_statement") == 0 || strcmp(kind, "catch_clause") == 0) {
        if (strcmp(kind, "catch_clause") != 0)
            ts_flow_enter_loop(ctx, node);
        CBMScope *saved = ctx->current_scope;
        ctx->current_scope = cbm_scope_push(ctx->arena, saved);
        if (strcmp(kind, "catch_clause") == 0) {
            TSNode param =
                ts_node_child_by_field_name(node, "parameter", TS_LSP_FIELD_LEN("parameter"));
            bind_unknown_pattern(ctx, param);
        }
        ts_process_statement(ctx, node);
        TSTreeCursor cursor = ts_tree_cursor_new(node);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                process_node(ctx, ts_tree_cursor_current_node(&cursor));
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
        ctx->current_scope = saved;
        return;
    }

    if (strcmp(kind, "while_statement") == 0 || strcmp(kind, "do_statement") == 0)
        ts_flow_enter_loop(ctx, node); /* then the default walk below */

    if (strcmp(kind, "expression_statement") == 0 && node.id == ctx->straight_stmt) {
        TSTreeCursor cursor = ts_tree_cursor_new(node);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                TSNode child = ts_tree_cursor_current_node(&cursor);
                if (ts_node_is_named(child))
                    ts_walk_straight_expression(ctx, child);
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
        return;
    }
    if (strcmp(kind, "assignment_expression") == 0 ||
        strcmp(kind, "augmented_assignment_expression") == 0) {
        ts_process_assignment(ctx, node, false);
        return;
    }
    if (strcmp(kind, "update_expression") == 0)
        ts_flow_write_pattern(ctx, ts_node_named_child(node, 0), 0);

    // Scope-affecting statements bind first, then we recurse.
    ts_process_statement(ctx, node);

    if (strcmp(kind, "new_expression") == 0) {
        TSNode ctor = ts_node_child_by_field_name(node, "constructor", 11);
        const char *name = node_kind_is(ctor, "identifier") ? node_text(ctx, ctor) : NULL;
        if (name && ts_import_is_instance(ctx, name))
            ts_emit_unresolved_call_at(ctx, name, "ts_value_not_constructor", node);
    }

    if (strcmp(kind, "call_expression") == 0) {
        resolve_call_at(ctx, node);
        resolve_value_references_at(ctx, node);

        // Contextual callback typing: when an arg is an arrow_function and the
        // corresponding param of the called function is itself a FUNC, propagate the
        // expected callback param types into the arrow's body before walking it.
        // Handle arg processing manually for this path to avoid double-walking via
        // default recurse below.
        do {
            TSNode fn_node =
                ts_node_child_by_field_name(node, "function", TS_LSP_FIELD_LEN("function"));
            if (ts_node_is_null(fn_node))
                break;
            TSNode args =
                ts_node_child_by_field_name(node, "arguments", TS_LSP_FIELD_LEN("arguments"));
            if (ts_node_is_null(args))
                break;
            const CBMType *fn_type = ts_signature_for_call(ctx, fn_node, args);
            if (!fn_type || fn_type->kind != CBM_TYPE_FUNC)
                break;
            if (!fn_type->data.func.param_types)
                break;

            // Process the function child for nested call resolution.
            process_node(ctx, fn_node);

            // param_types is NULL-terminated (no count field). Measure its
            // length so we never index past the terminator: a call may pass
            // more args than the function declares params (e.g. excess/variadic
            // args), and the extra args simply have no expected type. Indexing
            // param_types[i] by the raw arg count read out of bounds → garbage
            // CBMType* → crash on expected->kind.
            uint32_t param_count = 0;
            while (fn_type->data.func.param_types[param_count])
                param_count++;

            uint32_t argc = ts_node_named_child_count(args);
            for (uint32_t i = 0; i < argc; i++) {
                TSNode arg = ts_node_named_child(args, i);
                if (ts_node_is_null(arg))
                    continue;
                const char *ak = ts_node_type(arg);
                const CBMType *expected =
                    (i < param_count) ? fn_type->data.func.param_types[i] : NULL;
                if ((strcmp(ak, "arrow_function") == 0 || strcmp(ak, "function_expression") == 0) &&
                    expected && expected->kind == CBM_TYPE_FUNC) {
                    process_callback_arrow(ctx, arg, expected);
                } else {
                    process_node(ctx, arg);
                }
            }
            return; // Skip default recurse since we processed children manually.
        } while (0);
    }

    // JSX element resolution (TSX / JSX modes).
    if (ctx->jsx_mode &&
        (strcmp(kind, "jsx_element") == 0 || strcmp(kind, "jsx_self_closing_element") == 0)) {
        resolve_jsx_element(ctx, node);
    }

    // Switch-statement narrowing: `switch (x.kind) { case 'foo': ... }` — narrow x
    // to the union member whose discriminant property matches the case literal.
    if (strcmp(kind, "switch_statement") == 0) {
        TSNode value = ts_node_child_by_field_name(node, "value", TS_LSP_FIELD_LEN("value"));
        TSNode body = ts_node_child_by_field_name(node, "body", TS_LSP_FIELD_LEN("body"));
        // Walk the value expression so any nested calls resolve.
        if (!ts_node_is_null(value))
            process_node(ctx, value);

        // Identify discriminant: switch on `x.kind` member_expression.
        const char *disc_var = NULL;
        const char *disc_prop = NULL;
        const CBMType *var_union = NULL;
        if (!ts_node_is_null(value)) {
            // Strip parens.
            TSNode v = value;
            while (!ts_node_is_null(v) &&
                   strcmp(ts_node_type(v), "parenthesized_expression") == 0) {
                v = ts_node_named_child(v, 0);
            }
            if (!ts_node_is_null(v) && strcmp(ts_node_type(v), "member_expression") == 0) {
                TSNode obj = ts_node_child_by_field_name(v, "object", TS_LSP_FIELD_LEN("object"));
                TSNode prop =
                    ts_node_child_by_field_name(v, "property", TS_LSP_FIELD_LEN("property"));
                if (!ts_node_is_null(obj) && !ts_node_is_null(prop) &&
                    strcmp(ts_node_type(obj), "identifier") == 0) {
                    disc_var = node_text(ctx, obj);
                    disc_prop = node_text(ctx, prop);
                    if (disc_var) {
                        const CBMType *t = ts_lookup_binding_type(ctx, disc_var);
                        if (t && t->kind == CBM_TYPE_UNION)
                            var_union = t;
                    }
                }
            }
        }

        CBMScope *switch_scope = ctx->current_scope;
        ctx->current_scope = cbm_scope_push(ctx->arena, switch_scope);
        if (!ts_node_is_null(body)) {
            TSTreeCursor cases = ts_tree_cursor_new(body);
            if (ts_tree_cursor_goto_first_child(&cases)) {
                do {
                    shadow_block_declarations(ctx, ts_tree_cursor_current_node(&cases));
                } while (ts_tree_cursor_goto_next_sibling(&cases));
            }
            ts_tree_cursor_delete(&cases);
        }
        if (disc_var && cbm_scope_lookup_local(ctx->current_scope, disc_var))
            var_union = NULL;

        // Walk each switch_case in the body; narrow x in each case's scope.
        if (!ts_node_is_null(body)) {
            uint32_t bnc = ts_node_named_child_count(body);
            for (uint32_t i = 0; i < bnc; i++) {
                TSNode case_node = ts_node_named_child(body, i);
                if (ts_node_is_null(case_node))
                    continue;
                const char *ck = ts_node_type(case_node);
                if (strcmp(ck, "switch_case") != 0 && strcmp(ck, "switch_default") != 0) {
                    process_node(ctx, case_node);
                    continue;
                }

                // Find this case's literal value.
                const CBMType *narrowed = NULL;
                if (var_union && disc_prop && strcmp(ck, "switch_case") == 0) {
                    TSNode case_value =
                        ts_node_child_by_field_name(case_node, "value", TS_LSP_FIELD_LEN("value"));
                    if (!ts_node_is_null(case_value) &&
                        strcmp(ts_node_type(case_value), "string") == 0) {
                        char *lit = node_text(ctx, case_value);
                        if (lit) {
                            size_t ll = strlen(lit);
                            if (ll >= 2 && (lit[0] == '"' || lit[0] == '\'') &&
                                lit[ll - 1] == lit[0]) {
                                lit[ll - 1] = '\0';
                                lit++;
                            }
                            // Match member with matching discriminant field literal.
                            for (int mi = 0; mi < var_union->data.union_type.count; mi++) {
                                const CBMType *m = var_union->data.union_type.members[mi];
                                if (!m || m->kind != CBM_TYPE_NAMED)
                                    continue;
                                const CBMRegisteredType *rt = cbm_registry_lookup_type(
                                    ctx->registry, m->data.named.qualified_name);
                                if (!rt || !rt->field_names || !rt->field_types)
                                    continue;
                                for (int fj = 0; rt->field_names[fj]; fj++) {
                                    if (strcmp(rt->field_names[fj], disc_prop) != 0)
                                        continue;
                                    const CBMType *ft = rt->field_types[fj];
                                    if (!ft)
                                        continue;
                                    if (ft->kind == CBM_TYPE_TS_LITERAL &&
                                        ft->data.literal_ts.value &&
                                        strcmp(ft->data.literal_ts.value, lit) == 0) {
                                        narrowed = m;
                                        break;
                                    }
                                    if (ft->kind == CBM_TYPE_NAMED &&
                                        ft->data.named.qualified_name) {
                                        const char *qn = ft->data.named.qualified_name;
                                        size_t qnl = strlen(qn);
                                        if (qnl >= 2 && (qn[0] == '\'' || qn[0] == '"') &&
                                            qn[qnl - 1] == qn[0] &&
                                            strncmp(qn + 1, lit, qnl - 2) == 0 &&
                                            strlen(lit) == qnl - 2) {
                                            narrowed = m;
                                            break;
                                        }
                                    }
                                }
                                if (narrowed)
                                    break;
                            }
                        }
                    }
                }

                // Walk case body with narrowed scope if applicable.
                CBMScope *saved = ctx->current_scope;
                if (narrowed && disc_var) {
                    ctx->current_scope = cbm_scope_push(ctx->arena, saved);
                    cbm_scope_bind(ctx->current_scope, disc_var, narrowed);
                }
                // case_node's children include the value and the case body.
                uint32_t cnc = ts_node_child_count(case_node);
                for (uint32_t j = 0; j < cnc; j++) {
                    process_node(ctx, ts_node_child(case_node, j));
                }
                ctx->current_scope = saved;
            }
        }
        ctx->current_scope = switch_scope;
        return;
    }

    // Flow-sensitive narrowing for `if (...) { consequence } else { alternative }`.
    // Recognises `x instanceof T`, `typeof x === 'string'`, and `x.kind === 'lit'`
    // (discriminated union). Narrowed binding is pushed into a child scope for the
    // matching branch; the other branch sees the original type.
    if (strcmp(kind, "if_statement") == 0) {
        TSNode condition =
            ts_node_child_by_field_name(node, "condition", TS_LSP_FIELD_LEN("condition"));
        TSNode consequence =
            ts_node_child_by_field_name(node, "consequence", TS_LSP_FIELD_LEN("consequence"));
        TSNode alt =
            ts_node_child_by_field_name(node, "alternative", TS_LSP_FIELD_LEN("alternative"));

        // Walk the condition itself so any nested calls there resolve too.
        if (!ts_node_is_null(condition))
            process_node(ctx, condition);

        // 1. Try simple narrowing (instanceof, typeof).
        const char *nv = NULL;
        const CBMType *nt = NULL;
        bool inverted = false;
        bool ok = extract_narrowing(ctx, condition, &nv, &nt, &inverted);

        // 2. Try discriminated-union narrowing if simple narrowing didn't apply.
        if (!ok) {
            const char *dv = NULL;
            const CBMType *dt = narrow_discriminated_union(ctx, condition, &dv);
            if (dv && dt) {
                nv = dv;
                nt = dt;
                inverted = false;
                ok = true;
            }
        }

        /* The branch where the test holds gets the narrowed type; the other
         * branch gets the union without the members the test proves. */
        bool narrowed = ok && nv && nt;
        const CBMType *rest = narrowed ? ts_narrow_excluding(ctx, nv, nt) : NULL;
        ts_walk_narrowed(ctx, consequence, nv, narrowed ? (inverted ? rest : nt) : NULL);
        ts_walk_narrowed(ctx, alt, nv, narrowed ? (inverted ? nt : rest) : NULL);
        return; // Skip default recurse.
    }

    // Function-introducing nodes get their own scope + enclosing_func_qn handling.
    if (ts_is_function_declaration(node) || ts_is_function_value(node) ||
        strcmp(kind, "method_definition") == 0 || strcmp(kind, "method_signature") == 0) {
        // Nested functions just get a fresh scope; top-level / class-method walks own
        // their enclosing_func_qn via process_function_body.
        CBMScope *saved = ctx->current_scope;
        ctx->current_scope = cbm_scope_push(ctx->arena, saved);
        TsFnSave fn_saved = ts_enter_function(ctx, node);
        TSNode params =
            ts_node_child_by_field_name(node, "parameters", TS_LSP_FIELD_LEN("parameters"));
        if (!ts_node_is_null(params)) {
            uint32_t nc = ts_node_named_child_count(params);
            for (uint32_t i = 0; i < nc; i++)
                bind_parameter(ctx, ts_node_named_child(params, i));
        }
        TSNode bare_param =
            ts_node_child_by_field_name(node, "parameter", TS_LSP_FIELD_LEN("parameter"));
        if (!ts_node_is_null(bare_param))
            bind_parameter(ctx, bare_param);
        TSNode body = ts_node_child_by_field_name(node, "body", TS_LSP_FIELD_LEN("body"));
        if (!ts_node_is_null(body)) {
            // Arrow functions with a single-expression body: body IS the expression
            // (often a call_expression). Recursing into children skips it. Always
            // process_node(body) so resolve_call_at fires for that expression.
            process_node(ctx, body);
        }
        ts_leave_function(ctx, fn_saved);
        ctx->current_scope = saved;
        return;
    }

    if (strcmp(kind, "internal_module") == 0) {
        TSNode name = ts_node_child_by_field_name(node, "name", TS_LSP_FIELD_LEN("name"));
        const char *saved_module_qn = ctx->module_qn;
        CBMScope *saved_scope = ctx->current_scope;
        ctx->current_scope = cbm_scope_push(ctx->arena, saved_scope);
        TsFnSave fn_saved = ts_enter_function(ctx, node);
        if (!ts_node_is_null(name) && saved_module_qn) {
            char *namespace_name = node_text(ctx, name);
            if (namespace_name && namespace_name[0]) {
                ctx->module_qn =
                    cbm_arena_sprintf(ctx->arena, "%s.%s", saved_module_qn, namespace_name);
            }
        }
        TSNode body = ts_node_child_by_field_name(node, "body", TS_LSP_FIELD_LEN("body"));
        if (!ts_node_is_null(body)) {
            shadow_block_declarations(ctx, body);
            uint32_t count = ts_node_named_child_count(body);
            for (uint32_t i = 0; i < count; i++) {
                TSNode member = ts_node_named_child(body, i);
                ctx->straight_stmt = member.id;
                process_namespace_member(ctx, member);
            }
        }
        ctx->module_qn = saved_module_qn;
        ts_leave_function(ctx, fn_saved);
        ctx->current_scope = saved_scope;
        return;
    }

    // Class / interface declarations are walked by the registry pass; here we just dive
    // into method_definition bodies for inner call resolution.
    if (strcmp(kind, "class_declaration") == 0 || strcmp(kind, "class") == 0 ||
        strcmp(kind, "abstract_class_declaration") == 0) {
        const char *class_qn = ts_class_qn(ctx, node);
        TSNode body = ts_node_child_by_field_name(node, "body", TS_LSP_FIELD_LEN("body"));
        if (!ts_node_is_null(body) && class_qn) {
            uint32_t nc = ts_node_named_child_count(body);
            for (uint32_t i = 0; i < nc; i++) {
                TSNode m = ts_node_named_child(body, i);
                if (!node_kind_is(m, "method_definition"))
                    continue;
                TSNode mname = ts_node_child_by_field_name(m, "name", TS_LSP_FIELD_LEN("name"));
                if (ts_node_is_null(mname))
                    continue;
                char *mn = node_text(ctx, mname);
                if (!mn)
                    continue;
                const char *mqn = strcmp(mn, "constructor") == 0
                                      ? cbm_arena_sprintf(ctx->arena, "%s.%s", class_qn, mn)
                                      : cbm_arena_sprintf(ctx->arena, "%s.%s", class_qn, mn);
                process_function_body(ctx, m, mqn, class_qn);
            }
        }
        return;
    }

    // Default: recurse into children via a cursor (O(n)). ts_node_child(node,i)
    // is O(i) in tree-sitter → O(n²) when `node` is a wide block/root.
    {
        TSTreeCursor cursor = ts_tree_cursor_new(node);
        if (ts_tree_cursor_goto_first_child(&cursor)) {
            do {
                process_node(ctx, ts_tree_cursor_current_node(&cursor));
            } while (ts_tree_cursor_goto_next_sibling(&cursor));
        }
        ts_tree_cursor_delete(&cursor);
    }
}

static void process_function_body(TSLSPContext *ctx, TSNode func_node, const char *func_qn,
                                  const char *class_qn) {
    if (ts_node_is_null(func_node))
        return;
    CBMScope *saved_scope = ctx->current_scope;
    const char *saved_func = ctx->enclosing_func_qn;
    const char *saved_class = ctx->enclosing_class_qn;

    ctx->current_scope = cbm_scope_push(ctx->arena, saved_scope);
    TsFnSave fn_saved = ts_enter_function(ctx, func_node);
    ctx->enclosing_func_qn = func_qn;
    ctx->enclosing_class_qn = class_qn ? class_qn : saved_class;

    if (class_qn) {
        // Bind `this` to the class type for member resolution within methods.
        cbm_scope_bind(ctx->current_scope, "this", cbm_type_named(ctx->arena, class_qn));
    }

    TSNode params =
        ts_node_child_by_field_name(func_node, "parameters", TS_LSP_FIELD_LEN("parameters"));
    if (!ts_node_is_null(params)) {
        uint32_t nc = ts_node_named_child_count(params);
        for (uint32_t i = 0; i < nc; i++)
            bind_parameter(ctx, ts_node_named_child(params, i));

        // JSDoc / signature-derived param-type fallback: if bind_parameter left a
        // param bound to UNKNOWN (no inline TS annotation), use the registered func's
        // signature param_types[i] (which apply_jsdoc_signatures may have populated).
        if (func_qn) {
            const CBMRegisteredFunc *rf = ts_lookup_func(ctx, ctx->registry, func_qn);
            if (rf && rf->signature && rf->signature->kind == CBM_TYPE_FUNC &&
                rf->signature->data.func.param_names && rf->signature->data.func.param_types) {
                for (int i = 0; rf->signature->data.func.param_names[i] &&
                                rf->signature->data.func.param_types[i];
                     i++) {
                    const char *pname = rf->signature->data.func.param_names[i];
                    const CBMType *ptype = rf->signature->data.func.param_types[i];
                    if (cbm_type_is_unknown(ptype))
                        continue;
                    const CBMType *existing = cbm_scope_lookup(ctx->current_scope, pname);
                    if (existing && !cbm_type_is_unknown(existing))
                        continue;
                    ts_bind_local(ctx, ctx->current_scope, pname, ptype, ptype, true);
                }
            }
        }
    }

    TSNode bare_param =
        ts_node_child_by_field_name(func_node, "parameter", TS_LSP_FIELD_LEN("parameter"));
    if (!ts_node_is_null(bare_param))
        bind_parameter(ctx, bare_param);

    TSNode body = ts_node_child_by_field_name(func_node, "body", TS_LSP_FIELD_LEN("body"));
    if (!ts_node_is_null(body)) {
        // statement_block: walk every child statement. Expression body (concise
        // arrow): walk the expression directly — process_node on that handles
        // call_expression resolution.
        if (strcmp(ts_node_type(body), "statement_block") == 0) {
            shadow_block_declarations(ctx, body);
            TSTreeCursor cursor = ts_tree_cursor_new(body);
            if (ts_tree_cursor_goto_first_child(&cursor)) {
                do {
                    process_block_statement(ctx, ts_tree_cursor_current_node(&cursor));
                } while (ts_tree_cursor_goto_next_sibling(&cursor));
            }
            ts_tree_cursor_delete(&cursor);
        } else {
            process_node(ctx, body);
        }
    }

    ts_leave_function(ctx, fn_saved);
    ctx->enclosing_class_qn = saved_class;
    ctx->enclosing_func_qn = saved_func;
    ctx->current_scope = saved_scope;
}

/* Bind exported declarations in the same module scope as unwrapped ones.
 * This pass evaluates types only; the statement walk emits calls once. */
static void bind_module_declaration(TSLSPContext *ctx, TSNode node) {
    if (node_kind_is(node, "export_statement")) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++)
            bind_module_declaration(ctx, ts_node_named_child(node, i));
    } else if (node_kind_is(node, "lexical_declaration") ||
               node_kind_is(node, "variable_declaration")) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++) {
            TSNode decl = ts_node_named_child(node, i);
            if (!node_kind_is(decl, "variable_declarator"))
                continue;
            TSNode value = ts_node_child_by_field_name(decl, "value", TS_LSP_FIELD_LEN("value"));
            /* Module callables already have exact registry identities. Binding
             * them as unknown locals would hide JSX tags and direct calls. */
            if (ts_is_function_value(value) ||
                (node_kind_is(node, "variable_declaration") && ts_node_is_null(value) &&
                 ts_node_is_null(ts_node_child_by_field_name(decl, "type", 4))))
                continue;
            bind_variable_declarator(ctx, decl, ts_declaration_writable(ctx, node));
        }
    }
}

static void process_module_statement(TSLSPContext *ctx, TSNode node) {
    if (node_kind_is(node, "export_statement")) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++)
            process_module_statement(ctx, ts_node_named_child(node, i));
        return;
    }
    if (ts_is_function_declaration(node)) {
        process_namespace_member(ctx, node);
        return;
    }
    if (node_kind_is(node, "lexical_declaration") || node_kind_is(node, "variable_declaration")) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++) {
            TSNode decl = ts_node_named_child(node, i);
            if (!node_kind_is(decl, "variable_declarator"))
                continue;
            TSNode value = ts_node_child_by_field_name(decl, "value", TS_LSP_FIELD_LEN("value"));
            TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
            if (node_kind_is(name, "identifier") && ts_is_function_value(value)) {
                const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn,
                                                 node_text(ctx, name));
                process_function_body(ctx, value, qn, NULL);
            } else {
                process_node(ctx, value);
            }
        }
        return;
    }
    process_node(ctx, node);
}

void ts_lsp_process_file(TSLSPContext *ctx, TSNode root) {
    if (!ctx || ts_node_is_null(root) || ctx->dts_mode)
        return;

    ts_prepare_module_callables(ctx, root);
    ts_collect_assign_sites(ctx, root);
    ctx->fn_scope = ctx->current_scope;
    ctx->fn_start = 0;
    ctx->fn_end = UINT32_MAX;
    ts_hoist_vars(ctx);
    uint32_t count = 0;
    TSNode *children = collect_children(ctx->arena, root, &count);
    for (uint32_t i = 0; i < count; i++)
        bind_module_declaration(ctx, children[i]);

    /* A callback without a named ancestor belongs to the module. The exact
     * call-site rebind gives nested named callables their extracted identity.
     * Every statement is visited here once, including initializers and test
     * registration callbacks; there is no second generic root walk. */
    const char *saved_func = ctx->enclosing_func_qn;
    ctx->enclosing_func_qn = ctx->module_qn;
    ctx->flow_walk = true;
    for (uint32_t i = 0; i < count; i++) {
        ctx->straight_stmt = children[i].id;
        process_module_statement(ctx, children[i]);
    }
    ctx->flow_walk = false;
    ctx->enclosing_func_qn = saved_func;
}

// ── Initialization ────────────────────────────────────────────────────────────

void ts_lsp_init(TSLSPContext *ctx, CBMArena *arena, const char *source, int source_len,
                 const CBMTypeRegistry *registry, const char *module_qn, bool js_mode,
                 bool jsx_mode, bool dts_mode, CBMResolvedCallArray *out) {
    if (!ctx)
        return;
#ifdef CBM_ENABLE_TEST_SEAMS
    g_ts_signature_lookup_work = 0;
    g_ts_max_member_lookup_steps = 0;
    g_ts_max_method_lookup_steps = 0;
    g_ts_max_walk_depth = 0;
#endif
    memset(ctx, 0, sizeof(TSLSPContext));
    ctx->arena = arena;
    ctx->source = source;
    ctx->source_len = source_len;
    ctx->registry = registry;
    ctx->module_qn = module_qn;
    ctx->resolved_calls = out;
    ctx->js_mode = js_mode;
    ctx->jsx_mode = jsx_mode;
    ctx->dts_mode = dts_mode;
    ctx->current_scope = arena ? cbm_scope_push(arena, NULL) : NULL;
    ctx->fn_scope = ctx->current_scope;
    ctx->fn_start = 0;
    ctx->fn_end = UINT32_MAX;

    const char *debug_env = getenv("CBM_LSP_DEBUG");
    ctx->debug = (debug_env && debug_env[0]);
}

void ts_lsp_add_import(TSLSPContext *ctx, const char *local_name, const char *module_qn) {
    if (!ctx || !ctx->arena || !local_name || !module_qn)
        return;
    int new_count = ctx->import_count + 1;
    const char **names =
        (const char **)cbm_arena_alloc(ctx->arena, (size_t)new_count * sizeof(const char *));
    const char **qns =
        (const char **)cbm_arena_alloc(ctx->arena, (size_t)new_count * sizeof(const char *));
    if (!names || !qns)
        return;
    for (int i = 0; i < ctx->import_count; i++) {
        names[i] = ctx->import_local_names ? ctx->import_local_names[i] : NULL;
        qns[i] = ctx->import_module_qns ? ctx->import_module_qns[i] : NULL;
    }
    names[ctx->import_count] = cbm_arena_strdup(ctx->arena, local_name);
    qns[ctx->import_count] = cbm_arena_strdup(ctx->arena, module_qn);
    ctx->import_local_names = names;
    ctx->import_module_qns = qns;
    ctx->import_count = new_count;
}

static void ts_lsp_add_import_alias(TSLSPContext *ctx, const char *local, const char *exported) {
    if ((size_t)ctx->import_alias_count == ctx->import_alias_capacity) {
        /* The arena retains old arrays: grow geometrically so collecting A
         * aliases retains O(A) pointers instead of O(A squared). */
        size_t capacity = ctx->import_alias_capacity ? ctx->import_alias_capacity * 2 : 8;
        const char **locals =
            (const char **)cbm_arena_alloc(ctx->arena, capacity * sizeof(const char *));
        const char **exports =
            (const char **)cbm_arena_alloc(ctx->arena, capacity * sizeof(const char *));
        if (!locals || !exports)
            return;
        for (int i = 0; i < ctx->import_alias_count; i++) {
            locals[i] = ctx->import_alias_locals[i];
            exports[i] = ctx->import_alias_exports[i];
        }
        ctx->import_alias_locals = locals;
        ctx->import_alias_exports = exports;
        ctx->import_alias_capacity = capacity;
    }
    ctx->import_alias_locals[ctx->import_alias_count] = local;
    ctx->import_alias_exports[ctx->import_alias_count] = exported;
    ctx->import_alias_count++;
}

/* Record each `import { foo as bar }` binding of the file (#2297). The import
 * map holds only local bindings, so a renamed binding spelled `<module>.bar`,
 * named nothing, and every call through it lost its CALLS edge. Reading the
 * file's own import statements serves the per-file and both cross-file entry
 * points alike. Default bindings use their provider's recorded default
 * declaration or value. Namespace imports remain module bindings. Run before
 * the type passes, which resolve imported type names. */
static void ts_lsp_collect_import_aliases(TSLSPContext *ctx, TSNode root) {
    if (!ctx || !ctx->arena || ts_node_is_null(root) || ctx->import_count == 0)
        return;
    ctx->named_imports = cbm_scope_push(ctx->arena, NULL);
    uint32_t kn = 0;
    TSNode *kids = collect_children(ctx->arena, root, &kn);
    for (uint32_t i = 0; i < kn; i++) {
        if (!node_kind_is(kids[i], "import_statement"))
            continue;
        TSNode clause = find_first_kind(kids[i], "import_clause");
        if (ts_node_is_null(clause))
            continue; /* A side-effect-only import has no local bindings. */
        for (uint32_t j = 0; j < ts_node_named_child_count(clause); j++) {
            TSNode binding = ts_node_named_child(clause, j);
            if (node_kind_is(binding, "identifier")) {
                const char *local = node_text(ctx, binding);
                cbm_scope_bind(ctx->named_imports, local, cbm_type_unknown());
                ts_lsp_add_import_alias(ctx, local, "default");
            }
        }
        TSNode named = find_first_kind(clause, "named_imports");
        if (ts_node_is_null(named))
            continue;
        uint32_t sn = 0;
        TSNode *specs = collect_children(ctx->arena, named, &sn);
        for (uint32_t j = 0; j < sn; j++) {
            if (!node_kind_is(specs[j], "import_specifier"))
                continue;
            TSNode name = ts_node_child_by_field_name(specs[j], "name", TS_LSP_FIELD_LEN("name"));
            TSNode alias =
                ts_node_child_by_field_name(specs[j], "alias", TS_LSP_FIELD_LEN("alias"));
            TSNode binding = ts_node_is_null(alias) ? name : alias;
            if (node_kind_is(binding, "identifier"))
                cbm_scope_bind(ctx->named_imports, node_text(ctx, binding), cbm_type_unknown());
            if (!node_kind_is(name, "identifier") || !node_kind_is(alias, "identifier"))
                continue;
            char *exported = node_text(ctx, name);
            char *local = node_text(ctx, alias);
            if (exported && local && strcmp(exported, local) != 0)
                ts_lsp_add_import_alias(ctx, local, exported);
        }
    }
}

// ── Stdlib seeds (Phase 5 will replace with generator) ────────────────────────

static const CBMType *tt_builtin(CBMArena *a, const char *n) {
    return cbm_type_builtin(a, n);
}
static const CBMType *tt_param(CBMArena *a, const char *n) {
    return cbm_type_type_param(a, n);
}

static void ts_reg_method(CBMTypeRegistry *reg, CBMArena *arena, const char *recv_qn,
                          const char *name, const CBMType *ret_type) {
    CBMRegisteredFunc rf;
    memset(&rf, 0, sizeof(rf));
    rf.qualified_name = cbm_arena_sprintf(arena, "%s.%s", recv_qn, name);
    rf.short_name = cbm_arena_strdup(arena, name);
    rf.receiver_type = cbm_arena_strdup(arena, recv_qn);
    rf.min_params = -1;
    const CBMType *rets[2] = {ret_type ? ret_type : cbm_type_unknown(), NULL};
    rf.signature = cbm_type_func(arena, NULL, NULL, rets);
    cbm_registry_add_func(reg, rf);
}

static void reg_type_with_methods(CBMTypeRegistry *reg, CBMArena *arena, const char *qn,
                                  const char *short_name, const char **type_params,
                                  const char **method_names, const CBMType **method_returns) {
    CBMRegisteredType rt;
    memset(&rt, 0, sizeof(rt));
    rt.qualified_name = cbm_arena_strdup(arena, qn);
    rt.short_name = cbm_arena_strdup(arena, short_name);
    rt.type_param_names = type_params;
    if (method_names) {
        int count = 0;
        while (method_names[count])
            count++;
        const char **mqns =
            (const char **)cbm_arena_alloc(arena, (size_t)(count + 1) * sizeof(const char *));
        const char **mnames_copy =
            (const char **)cbm_arena_alloc(arena, (size_t)(count + 1) * sizeof(const char *));
        if (mqns && mnames_copy) {
            for (int i = 0; i < count; i++) {
                mnames_copy[i] = cbm_arena_strdup(arena, method_names[i]);
                mqns[i] = cbm_arena_sprintf(arena, "%s.%s", qn, method_names[i]);
            }
            mnames_copy[count] = NULL;
            mqns[count] = NULL;
            rt.method_names = mnames_copy;
            rt.method_qns = mqns;
        }
    }
    cbm_registry_add_type(reg, rt);

    if (method_names && method_returns) {
        for (int i = 0; method_names[i]; i++) {
            ts_reg_method(reg, arena, qn, method_names[i], method_returns[i]);
        }
    }
}

void cbm_ts_stdlib_register(CBMTypeRegistry *reg, CBMArena *arena) {
    if (!reg || !arena)
        return;

    const CBMType *t_string = tt_builtin(arena, "string");
    const CBMType *t_number = tt_builtin(arena, "number");
    const CBMType *t_boolean = tt_builtin(arena, "boolean");
    const CBMType *t_void = tt_builtin(arena, "void");
    const CBMType *t_unknown = cbm_type_unknown();

    // Array<T>: minimal method surface for v1.
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const CBMType *tparam_U = tt_param(arena, "U");
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        static const char *methods[] = {
            "push",    "pop",      "shift",   "unshift", "slice",  "splice", "concat",    "join",
            "indexOf", "includes", "forEach", "map",     "filter", "find",   "findIndex", "reduce",
            "some",    "every",    "sort",    "reverse", "at",     "flat",   "flatMap",   NULL,
        };
        const CBMType *returns[24];
        const CBMType *t_T = tparam_T;
        const CBMType *t_arr_T_args[2] = {t_T, NULL};
        const CBMType *t_arr_T = cbm_type_template(arena, "Array", t_arr_T_args, 1);
        returns[0] = t_number;  // push
        returns[1] = t_T;       // pop
        returns[2] = t_T;       // shift
        returns[3] = t_number;  // unshift
        returns[4] = t_arr_T;   // slice
        returns[5] = t_arr_T;   // splice
        returns[6] = t_arr_T;   // concat
        returns[7] = t_string;  // join
        returns[8] = t_number;  // indexOf
        returns[9] = t_boolean; // includes
        returns[10] = t_void;   // forEach
        returns[11] =
            cbm_type_template(arena, "Array", (const CBMType *[]){tparam_U, NULL}, 1); // map<U>
        returns[12] = t_arr_T;                                                         // filter
        returns[13] = t_T;                                                             // find
        returns[14] = t_number;                                                        // findIndex
        returns[15] = tparam_U;                                                        // reduce<U>
        returns[16] = t_boolean;                                                       // some
        returns[17] = t_boolean;                                                       // every
        returns[18] = t_arr_T;                                                         // sort
        returns[19] = t_arr_T;                                                         // reverse
        returns[20] = t_T;                                                             // at
        returns[21] = t_arr_T;                                                         // flat
        returns[22] = t_arr_T;                                                         // flatMap
        returns[23] = NULL;
        reg_type_with_methods(reg, arena, "Array", "Array", tparams, methods, returns);

        // Patch the registered Array.{forEach,map,filter,find,findIndex,some,every,
        // flatMap,sort,reduce} signatures with a typed callback (x: T) => U so that
        // contextual typing can bind the callback's first param to T inside the
        // closure body. We rebuild rf.signature carrying through the existing return
        // type. This unlocks `arr.map(x => x.length)`-style resolution.
        const char *p_names[] = {"callback", NULL};
        struct {
            const char *method;
            const CBMType *ret;
            const CBMType *cb_param0;
            const CBMType *cb_ret;
        } cb_specs[] = {
            {"forEach", t_void, t_T, t_void},
            {"map", returns[11], t_T, tparam_U},
            {"filter", t_arr_T, t_T, t_boolean},
            {"find", t_T, t_T, t_boolean},
            {"findIndex", t_number, t_T, t_boolean},
            {"some", t_boolean, t_T, t_boolean},
            {"every", t_boolean, t_T, t_boolean},
            {"flatMap", t_arr_T, t_T, tparam_U},
            {"sort", t_arr_T, t_T, t_number},
            {"reduce", tparam_U, t_T, tparam_U},
            {NULL, NULL, NULL, NULL},
        };
        for (int ci = 0; cb_specs[ci].method; ci++) {
            // Build callback FUNC type: (x: T) => returnType
            const CBMType *cb_param_types[2] = {cb_specs[ci].cb_param0, NULL};
            const CBMType *cb_returns[2] = {cb_specs[ci].cb_ret, NULL};
            const char *cb_param_names[2] = {"x", NULL};
            const CBMType *cb_func =
                cbm_type_func(arena, cb_param_names, cb_param_types, cb_returns);

            // Rebuild Array.<method>'s signature with this callback as param 0.
            const CBMType *outer_param_types[2] = {cb_func, NULL};
            const CBMType *outer_returns[2] = {cb_specs[ci].ret, NULL};
            const CBMType *new_sig =
                cbm_type_func(arena, p_names, outer_param_types, outer_returns);

            // Find Array.<method> in the registry and patch its signature.
            char *qn = cbm_arena_sprintf(arena, "Array.%s", cb_specs[ci].method);
            for (int fi = 0; fi < reg->func_count; fi++) {
                if (reg->funcs[fi].qualified_name &&
                    strcmp(reg->funcs[fi].qualified_name, qn) == 0) {
                    reg->funcs[fi].signature = new_sig;
                    break;
                }
            }
        }
    }

    // Promise<T>
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        static const char *methods[] = {"then", "catch", "finally", NULL};
        const CBMType *returns[4];
        const CBMType *t_promise_T_args[2] = {tparam_T, NULL};
        const CBMType *t_promise_T = cbm_type_template(arena, "Promise", t_promise_T_args, 1);
        returns[0] = t_promise_T;
        returns[1] = t_promise_T;
        returns[2] = t_promise_T;
        returns[3] = NULL;
        reg_type_with_methods(reg, arena, "Promise", "Promise", tparams, methods, returns);
    }

    // Map<K,V>
    {
        const char **tparams = (const char **)cbm_arena_alloc(arena, 3 * sizeof(const char *));
        tparams[0] = "K";
        tparams[1] = "V";
        tparams[2] = NULL;
        static const char *methods[] = {"get", "set", "has", "delete", "clear", "forEach", NULL};
        const CBMType *returns[7] = {
            tt_param(arena, "V"),
            cbm_type_template(arena, "Map",
                              (const CBMType *[]){tt_param(arena, "K"), tt_param(arena, "V"), NULL},
                              2),
            t_boolean,
            t_boolean,
            t_void,
            t_void,
            NULL,
        };
        reg_type_with_methods(reg, arena, "Map", "Map", tparams, methods, returns);
    }

    // Set<T>
    {
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        static const char *methods[] = {"add", "has", "delete", "clear", "forEach", NULL};
        const CBMType *returns[6] = {
            cbm_type_template(arena, "Set", (const CBMType *[]){tt_param(arena, "T"), NULL}, 1),
            t_boolean,
            t_boolean,
            t_void,
            t_void,
            NULL,
        };
        reg_type_with_methods(reg, arena, "Set", "Set", tparams, methods, returns);
    }

    // Iterator<T> / Iterable<T>
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        // IteratorResult<T> is loose — we fold it to T-or-undefined via the iterator method's
        // return.
        static const char *iter_methods[] = {"next", "return", "throw", NULL};
        const CBMType *iter_returns[4] = {tparam_T, tparam_T, tparam_T, NULL};
        reg_type_with_methods(reg, arena, "Iterator", "Iterator", tparams, iter_methods,
                              iter_returns);

        const CBMType *iter_t =
            cbm_type_template(arena, "Iterator", (const CBMType *[]){tparam_T, NULL}, 1);
        static const char *iterable_methods[] = {NULL}; // [Symbol.iterator] not modeled by name
        const CBMType *iterable_returns[1] = {NULL};
        (void)iter_t;
        reg_type_with_methods(reg, arena, "Iterable", "Iterable", tparams, iterable_methods,
                              iterable_returns);
    }

    // AsyncIterator<T> / AsyncIterable<T> — methods return Promise<T>
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        const CBMType *prom_T =
            cbm_type_template(arena, "Promise", (const CBMType *[]){tparam_T, NULL}, 1);
        static const char *methods[] = {"next", "return", "throw", NULL};
        const CBMType *returns[4] = {prom_T, prom_T, prom_T, NULL};
        reg_type_with_methods(reg, arena, "AsyncIterator", "AsyncIterator", tparams, methods,
                              returns);
        reg_type_with_methods(reg, arena, "AsyncIterable", "AsyncIterable", tparams, methods,
                              returns);
    }

    // Generator<T> — extends Iterator<T> with yield-based methods.
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const char **tparams = (const char **)cbm_arena_alloc(arena, 2 * sizeof(const char *));
        tparams[0] = "T";
        tparams[1] = NULL;
        static const char *methods[] = {"next", "return", "throw", NULL};
        const CBMType *returns[4] = {tparam_T, tparam_T, tparam_T, NULL};
        reg_type_with_methods(reg, arena, "Generator", "Generator", tparams, methods, returns);
        reg_type_with_methods(reg, arena, "AsyncGenerator", "AsyncGenerator", tparams, methods,
                              returns);
    }

    // String prototype methods (most common).
    {
        static const char *methods[] = {
            "charAt",      "charCodeAt",  "concat",     "includes",  "indexOf",
            "lastIndexOf", "padStart",    "padEnd",     "repeat",    "replace",
            "slice",       "split",       "startsWith", "endsWith",  "substring",
            "toLowerCase", "toUpperCase", "trim",       "trimStart", "trimEnd",
            "match",       "matchAll",    "normalize",  "at",        NULL,
        };
        // Simplified: most string methods return string or boolean — fold to string for v1.
        int mc = 0;
        while (methods[mc])
            mc++;
        const CBMType **returns =
            (const CBMType **)cbm_arena_alloc(arena, (size_t)(mc + 1) * sizeof(const CBMType *));
        for (int i = 0; i < mc; i++) {
            // booleans: includes, startsWith, endsWith
            const char *m = methods[i];
            if (strcmp(m, "includes") == 0 || strcmp(m, "startsWith") == 0 ||
                strcmp(m, "endsWith") == 0) {
                returns[i] = t_boolean;
            } else if (strcmp(m, "indexOf") == 0 || strcmp(m, "lastIndexOf") == 0 ||
                       strcmp(m, "charCodeAt") == 0) {
                returns[i] = t_number;
            } else if (strcmp(m, "split") == 0) {
                returns[i] =
                    cbm_type_template(arena, "Array", (const CBMType *[]){t_string, NULL}, 1);
            } else {
                returns[i] = t_string;
            }
        }
        returns[mc] = NULL;
        reg_type_with_methods(reg, arena, "String", "String", NULL, methods, returns);
    }

    // console — used so frequently that resolving `console.log` directly is high value.
    {
        static const char *methods[] = {"log", "error", "warn", "info", "debug", NULL};
        const CBMType *returns[6] = {t_void, t_void, t_void, t_void, t_void, NULL};
        reg_type_with_methods(reg, arena, "console", "console", NULL, methods, returns);
    }

    // JSON namespace.
    {
        static const char *methods[] = {"parse", "stringify", NULL};
        const CBMType *returns[3] = {t_unknown, t_string, NULL};
        reg_type_with_methods(reg, arena, "JSON", "JSON", NULL, methods, returns);
    }

    // Object — constructor namespace methods that are commonly chained.
    {
        static const char *methods[] = {"keys",     "values", "entries",        "assign", "freeze",
                                        "isFrozen", "create", "getPrototypeOf", NULL};
        const CBMType *returns[9] = {
            cbm_type_template(arena, "Array", (const CBMType *[]){t_string, NULL}, 1),
            cbm_type_template(arena, "Array", (const CBMType *[]){t_unknown, NULL}, 1),
            cbm_type_template(arena, "Array", (const CBMType *[]){t_unknown, NULL}, 1),
            t_unknown,
            t_unknown,
            t_boolean,
            t_unknown,
            t_unknown,
            NULL,
        };
        reg_type_with_methods(reg, arena, "Object", "Object", NULL, methods, returns);
    }

    // Number wrapper class (so `(42).toString()` and similar resolve).
    {
        static const char *methods[] = {
            "toString", "toFixed", "toExponential", "toPrecision", "valueOf", NULL,
        };
        const CBMType *returns[6] = {t_string, t_string, t_string, t_string, t_number, NULL};
        reg_type_with_methods(reg, arena, "Number", "Number", NULL, methods, returns);
    }

    // Boolean wrapper class.
    {
        static const char *methods[] = {"toString", "valueOf", NULL};
        const CBMType *returns[3] = {t_string, t_boolean, NULL};
        reg_type_with_methods(reg, arena, "Boolean", "Boolean", NULL, methods, returns);
    }

    // Date wrapper class — common date operations.
    {
        static const char *methods[] = {
            "toISOString", "toString", "toJSON",      "toDateString", "toTimeString",
            "getTime",     "valueOf",  "getFullYear", "getMonth",     "getDate",
            "getDay",      "getHours", "getMinutes",  "getSeconds",   "getMilliseconds",
            "setFullYear", "setMonth", "setDate",     "setHours",     "setMinutes",
            "setSeconds",  NULL,
        };
        int mc = 0;
        while (methods[mc])
            mc++;
        const CBMType **returns =
            (const CBMType **)cbm_arena_alloc(arena, (size_t)(mc + 1) * sizeof(const CBMType *));
        for (int i = 0; i < mc; i++) {
            const char *m = methods[i];
            if (strcmp(m, "toISOString") == 0 || strcmp(m, "toString") == 0 ||
                strcmp(m, "toJSON") == 0 || strcmp(m, "toDateString") == 0 ||
                strcmp(m, "toTimeString") == 0) {
                returns[i] = t_string;
            } else {
                returns[i] = t_number;
            }
        }
        returns[mc] = NULL;
        reg_type_with_methods(reg, arena, "Date", "Date", NULL, methods, returns);
    }

    // RegExp wrapper class.
    {
        static const char *methods[] = {"test", "exec", "toString", "compile", NULL};
        const CBMType *returns[5] = {t_boolean, t_unknown, t_string, t_unknown, NULL};
        reg_type_with_methods(reg, arena, "RegExp", "RegExp", NULL, methods, returns);
    }

    // Error class — used heavily in `throw new Error(...)` and catch handlers.
    {
        static const char *methods[] = {"toString", NULL};
        const CBMType *returns[2] = {t_string, NULL};
        reg_type_with_methods(reg, arena, "Error", "Error", NULL, methods, returns);
    }

    // Math namespace — static math operations.
    {
        static const char *methods[] = {
            "floor", "ceil", "round", "trunc",  "abs",   "sqrt", "cbrt", "pow",  "exp",
            "log",   "log2", "log10", "sin",    "cos",   "tan",  "asin", "acos", "atan",
            "atan2", "min",  "max",   "random", "hypot", "sign", NULL,
        };
        int mc = 0;
        while (methods[mc])
            mc++;
        const CBMType **returns =
            (const CBMType **)cbm_arena_alloc(arena, (size_t)(mc + 1) * sizeof(const CBMType *));
        for (int i = 0; i < mc; i++)
            returns[i] = t_number;
        returns[mc] = NULL;
        reg_type_with_methods(reg, arena, "Math", "Math", NULL, methods, returns);
    }

    // Static methods that don't fit reg_type_with_methods cleanly:
    // Promise.resolve(x): Promise<T> — generic in T derived from arg type
    // Promise.all(promises): Promise<T[]>
    // Promise.reject(reason): Promise<never>
    // Array.from(iter): Array<T>
    // Array.isArray(x): boolean
    // Array.of(...items): Array<T>
    {
        const CBMType *tparam_T = tt_param(arena, "T");
        const CBMType *t_T = tparam_T;
        const CBMType *prom_T =
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_T, NULL}, 1);
        const CBMType *arr_T = cbm_type_template(arena, "Array", (const CBMType *[]){t_T, NULL}, 1);
        const CBMType *prom_arr_T =
            cbm_type_template(arena, "Promise", (const CBMType *[]){arr_T, NULL}, 1);
        ts_reg_method(reg, arena, "Promise", "resolve", prom_T);
        ts_reg_method(reg, arena, "Promise", "all", prom_arr_T);
        ts_reg_method(reg, arena, "Promise", "reject", prom_T);
        ts_reg_method(reg, arena, "Promise", "race", prom_T);
        ts_reg_method(reg, arena, "Promise", "allSettled", prom_arr_T);

        ts_reg_method(reg, arena, "Array", "from", arr_T);
        ts_reg_method(reg, arena, "Array", "isArray", t_boolean);
        ts_reg_method(reg, arena, "Array", "of", arr_T);
    }

    // ── DOM essentials ───────────────────────────────────────────────────────
    // Element + Document + Window + Event + Response cover the most-used DOM
    // surface for browser TS code. Hand-curated subset; full lib.dom.d.ts would
    // be Phase 5 (generator).
    {
        // EventTarget base
        static const char *et_methods[] = {
            "addEventListener",
            "removeEventListener",
            "dispatchEvent",
            NULL,
        };
        const CBMType *et_returns[4] = {t_void, t_void, t_boolean, NULL};
        reg_type_with_methods(reg, arena, "EventTarget", "EventTarget", NULL, et_methods,
                              et_returns);

        // Node
        static const char *node_methods[] = {
            "appendChild",   "removeChild",      "replaceChild",        "cloneNode",     "contains",
            "hasChildNodes", "addEventListener", "removeEventListener", "dispatchEvent", NULL,
        };
        const CBMType *node_t = cbm_type_named(arena, "Node");
        const CBMType *node_returns[10] = {
            node_t, node_t, node_t, node_t, t_boolean, t_boolean, t_void, t_void, t_boolean, NULL,
        };
        reg_type_with_methods(reg, arena, "Node", "Node", NULL, node_methods, node_returns);

        // Element
        static const char *el_methods[] = {
            "getAttribute",
            "setAttribute",
            "removeAttribute",
            "hasAttribute",
            "querySelector",
            "querySelectorAll",
            "closest",
            "matches",
            "appendChild",
            "removeChild",
            "replaceChild",
            "addEventListener",
            "removeEventListener",
            "dispatchEvent",
            "getBoundingClientRect",
            "scrollIntoView",
            "focus",
            "blur",
            "click",
            "remove",
            NULL,
        };
        const CBMType *el_t = cbm_type_named(arena, "Element");
        const CBMType *nodelist_t =
            cbm_type_template(arena, "NodeList", (const CBMType *[]){el_t, NULL}, 1);
        const CBMType *el_returns[21] = {
            t_string,  t_void, t_void, t_boolean, el_t,   nodelist_t, el_t,
            t_boolean, el_t,   el_t,   el_t,      t_void, t_void,     t_boolean,
            t_unknown, t_void, t_void, t_void,    t_void, t_void,     NULL,
        };
        reg_type_with_methods(reg, arena, "Element", "Element", NULL, el_methods, el_returns);

        // HTMLElement (extends Element)
        static const char *html_methods[] = {
            "getAttribute",
            "setAttribute",
            "querySelector",
            "querySelectorAll",
            "closest",
            "addEventListener",
            "removeEventListener",
            "click",
            "focus",
            "blur",
            "remove",
            NULL,
        };
        const CBMType *html_t = cbm_type_named(arena, "HTMLElement");
        const CBMType *html_returns[12] = {
            t_string, t_void,
            html_t,   cbm_type_template(arena, "NodeList", (const CBMType *[]){html_t, NULL}, 1),
            html_t,   t_void,
            t_void,   t_void,
            t_void,   t_void,
            t_void,   NULL,
        };
        reg_type_with_methods(reg, arena, "HTMLElement", "HTMLElement", NULL, html_methods,
                              html_returns);

        // Document
        static const char *doc_methods[] = {
            "getElementById",
            "querySelector",
            "querySelectorAll",
            "getElementsByClassName",
            "getElementsByTagName",
            "createElement",
            "createTextNode",
            "createDocumentFragment",
            "addEventListener",
            "removeEventListener",
            NULL,
        };
        const CBMType *doc_returns[11] = {
            html_t,
            html_t,
            cbm_type_template(arena, "NodeList", (const CBMType *[]){html_t, NULL}, 1),
            cbm_type_template(arena, "HTMLCollection", (const CBMType *[]){html_t, NULL}, 1),
            cbm_type_template(arena, "HTMLCollection", (const CBMType *[]){html_t, NULL}, 1),
            html_t,
            node_t,
            node_t,
            t_void,
            t_void,
            NULL,
        };
        reg_type_with_methods(reg, arena, "Document", "Document", NULL, doc_methods, doc_returns);

        // Event
        static const char *event_methods[] = {
            "preventDefault", "stopPropagation", "stopImmediatePropagation", "composedPath", NULL,
        };
        const CBMType *event_returns[5] = {
            t_void,
            t_void,
            t_void,
            cbm_type_template(
                arena, "Array",
                (const CBMType *[]){
                    et_methods[0] ? cbm_type_named(arena, "EventTarget") : t_unknown, NULL},
                1),
            NULL,
        };
        reg_type_with_methods(reg, arena, "Event", "Event", NULL, event_methods, event_returns);

        // Response (fetch API)
        static const char *resp_methods[] = {
            "json", "text", "blob", "arrayBuffer", "formData", "clone", NULL,
        };
        const CBMType *resp_returns[7] = {
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_unknown, NULL}, 1),
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_string, NULL}, 1),
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_unknown, NULL}, 1),
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_unknown, NULL}, 1),
            cbm_type_template(arena, "Promise", (const CBMType *[]){t_unknown, NULL}, 1),
            cbm_type_named(arena, "Response"),
            NULL,
        };
        reg_type_with_methods(reg, arena, "Response", "Response", NULL, resp_methods, resp_returns);

        // Window
        static const char *win_methods[] = {
            "addEventListener",
            "removeEventListener",
            "alert",
            "confirm",
            "prompt",
            "fetch",
            "setTimeout",
            "clearTimeout",
            "setInterval",
            "clearInterval",
            "requestAnimationFrame",
            "cancelAnimationFrame",
            NULL,
        };
        const CBMType *win_returns[13] = {
            t_void,
            t_void,
            t_void,
            t_boolean,
            t_string,
            cbm_type_template(arena, "Promise",
                              (const CBMType *[]){cbm_type_named(arena, "Response"), NULL}, 1),
            t_number,
            t_void,
            t_number,
            t_void,
            t_number,
            t_void,
            NULL,
        };
        reg_type_with_methods(reg, arena, "Window", "Window", NULL, win_methods, win_returns);
    }
}

// ── Single-file entry point ───────────────────────────────────────────────────

// Build a registry from result->defs: register Class/Interface as types; Function/Method
// as funcs. Walks AST briefly for class fields/extends.
static void register_file_defs(CBMArena *arena, CBMTypeRegistry *reg, CBMFileResult *result,
                               const char *module_qn) {
    /* Class facts precede return signatures, including forward declarations.
     * The existing scope index keeps this proof linear in the definition set. */
    CBMScope *classes = cbm_scope_push(arena, NULL);
    for (int i = 0; i < result->defs.count; i++) {
        const CBMDefinition *d = &result->defs.items[i];
        if (d->label && strcmp(d->label, "Class") == 0 && d->qualified_name)
            cbm_scope_bind(classes, d->qualified_name, cbm_type_unknown());
    }
    for (int i = 0; i < result->defs.count; i++) {
        CBMDefinition *d = &result->defs.items[i];
        if (!d->qualified_name || !d->name || !d->label)
            continue;

        if (strcmp(d->label, "Class") == 0 || strcmp(d->label, "Interface") == 0) {
            CBMRegisteredType rt;
            memset(&rt, 0, sizeof(rt));
            rt.qualified_name = d->qualified_name;
            rt.short_name = d->name;
            rt.is_interface = (strcmp(d->label, "Interface") == 0);
            rt.ts_value_binding_written = d->ts_value_binding_written;
            // base_classes → embedded_types (extends/implements).
            if (d->base_classes) {
                int bc = 0;
                while (d->base_classes[bc])
                    bc++;
                if (bc > 0) {
                    const char **emb = (const char **)cbm_arena_alloc(
                        arena, (size_t)(bc + 1) * sizeof(const char *));
                    if (emb) {
                        for (int j = 0; j < bc; j++) {
                            const char *b = d->base_classes[j];
                            // For TS, extract_defs returns base text like "extends Animal"
                            // or "extends Foo<Bar>" (raw class_heritage node text). Strip
                            // the keyword and pull the first identifier.
                            if (b) {
                                while (*b == ' ' || *b == '\t' || *b == '\n')
                                    b++;
                                if (strncmp(b, "extends", 7) == 0 &&
                                    (b[7] == ' ' || b[7] == '\t')) {
                                    b += 7;
                                }
                                if (strncmp(b, "implements", 10) == 0 &&
                                    (b[10] == ' ' || b[10] == '\t')) {
                                    b += 10;
                                }
                                while (*b == ' ' || *b == '\t' || *b == '\n')
                                    b++;
                                size_t bl = 0;
                                while (b[bl] && b[bl] != ' ' && b[bl] != ',' && b[bl] != '<' &&
                                       b[bl] != '(' && b[bl] != '\n' && b[bl] != '\t')
                                    bl++;
                                if (bl == 0) {
                                    emb[j] = NULL;
                                    continue;
                                }
                                char *base_name = cbm_arena_strndup(arena, b, bl);
                                if (strchr(base_name, '.') == NULL) {
                                    emb[j] =
                                        cbm_arena_sprintf(arena, "%s.%s", module_qn, base_name);
                                } else {
                                    emb[j] = base_name;
                                }
                            } else {
                                emb[j] = NULL;
                            }
                        }
                        emb[bc] = NULL;
                        rt.embedded_types = emb;
                    }
                }
            }
            cbm_registry_add_type(reg, rt);
        } else if (strcmp(d->label, "Function") == 0 || strcmp(d->label, "Method") == 0) {
            /* Interface members are registered by ast_sweep_shapes from the
             * AST, whose signature resolves names against this module first;
             * the def text would type `status(): Response` as the global
             * lib.dom Response and break chained calls. */
            if (strcmp(d->label, "Method") == 0 && d->parent_class) {
                const CBMRegisteredType *owner = cbm_registry_lookup_type(reg, d->parent_class);
                if (owner && owner->is_interface) {
                    continue;
                }
            }
            CBMRegisteredFunc rf;
            memset(&rf, 0, sizeof(rf));
            rf.qualified_name = d->qualified_name;
            rf.short_name = d->name;
            rf.min_params = -1;

            // Build return type list.
            //
            // For TS, prefer the RAW d->return_type text over d->return_types[]: the
            // latter is post-cleaned via extract_defs.c::clean_type_name which truncates
            // at the first '<' (so `Promise<number>` becomes `Promise`, losing the
            // generic args). The raw text preserves generics; parse_ts_type_text strips
            // the leading `:` annotation prefix.
            const CBMType **rets = NULL;
            if (d->return_type && d->return_type[0]) {
                rets = (const CBMType **)cbm_arena_alloc(arena, 2 * sizeof(const CBMType *));
                if (rets) {
                    rets[0] = parse_ts_type_text(arena, d->return_type, module_qn);
                    if (d->ts_return_constructor) {
                        const CBMType *target = rets[0];
                        if (target && target->kind == CBM_TYPE_TEMPLATE &&
                            target->data.template_type.template_name &&
                            strcmp(target->data.template_type.template_name, "Promise") == 0 &&
                            target->data.template_type.arg_count == 1 &&
                            target->data.template_type.template_args)
                            target = target->data.template_type.template_args[0];
                        if (!target || target->kind != CBM_TYPE_NAMED ||
                            !cbm_scope_lookup_local(classes, target->data.named.qualified_name))
                            rets[0] = cbm_type_unknown();
                    }
                    rets[1] = NULL;
                }
            } else if (d->return_types) {
                int n = 0;
                while (d->return_types[n])
                    n++;
                if (n > 0) {
                    rets = (const CBMType **)cbm_arena_alloc(arena, (size_t)(n + 1) *
                                                                        sizeof(const CBMType *));
                    if (rets) {
                        for (int j = 0; j < n; j++) {
                            rets[j] = parse_ts_type_text(arena, d->return_types[j], module_qn);
                        }
                        rets[n] = NULL;
                    }
                }
            }
            /* The counted occurrence-preserving carrier wins even when its
             * explicit count is zero. Legacy names are only safe alongside the
             * legacy fallback because the two legacy projections share shape. */
            bool has_ordered_params =
                d->signature_param_types != NULL || d->signature_param_count > 0;
            const CBMType **params_t = NULL;
            const char **param_names = NULL;
            if (has_ordered_params) {
                CBMTSLSPSignatureParserContext param_parser_ctx = {module_qn};
                params_t = cbm_type_materialize_signature_params(
                    arena, d->signature_param_types, d->signature_param_count,
                    cbm_ts_lsp_parse_signature_param_text, &param_parser_ctx);
            } else {
                params_t = parse_param_types_array(arena, d->param_types, module_qn);
                param_names = d->param_names;
            }
            rf.signature = cbm_type_func(arena, param_names, params_t, rets);

            // Methods: deduce receiver from QN ("module.Class.method" → receiver "module.Class").
            if (strcmp(d->label, "Method") == 0) {
                const char *dot = strrchr(d->qualified_name, '.');
                if (dot && dot != d->qualified_name) {
                    char *recv = cbm_arena_strndup(arena, d->qualified_name,
                                                   (size_t)(dot - d->qualified_name));
                    rf.receiver_type = recv;

                    // Ensure the receiver type is registered (auto-create if missing).
                    const CBMRegisteredType *existing = cbm_registry_lookup_type(reg, recv);
                    if (!existing) {
                        CBMRegisteredType auto_rt;
                        memset(&auto_rt, 0, sizeof(auto_rt));
                        auto_rt.qualified_name = recv;
                        const char *short_name = strrchr(recv, '.');
                        auto_rt.short_name = short_name ? short_name + 1 : recv;
                        cbm_registry_add_type(reg, auto_rt);
                    }
                }
            }

            cbm_registry_add_func(reg, rf);
        }
    }

    // Second pass: attach method_names / method_qns to each registered type from
    // the registered methods. Lets dispatch find them via lookup_member_type.
    for (int ti = 0; ti < reg->type_count; ti++) {
        CBMRegisteredType *rt = &reg->types[ti];
        if (!rt->qualified_name)
            continue;

        // Count methods first.
        int mcount = 0;
        for (int fi = 0; fi < reg->func_count; fi++) {
            const CBMRegisteredFunc *f = &reg->funcs[fi];
            if (f->receiver_type && strcmp(f->receiver_type, rt->qualified_name) == 0) {
                mcount++;
            }
        }
        if (mcount == 0)
            continue;

        const char **mnames =
            (const char **)cbm_arena_alloc(arena, (size_t)(mcount + 1) * sizeof(const char *));
        const char **mqns =
            (const char **)cbm_arena_alloc(arena, (size_t)(mcount + 1) * sizeof(const char *));
        if (!mnames || !mqns)
            continue;
        int idx = 0;
        for (int fi = 0; fi < reg->func_count && idx < mcount; fi++) {
            const CBMRegisteredFunc *f = &reg->funcs[fi];
            if (f->receiver_type && strcmp(f->receiver_type, rt->qualified_name) == 0) {
                mnames[idx] = f->short_name;
                mqns[idx] = f->qualified_name;
                idx++;
            }
        }
        mnames[mcount] = NULL;
        mqns[mcount] = NULL;
        rt->method_names = mnames;
        rt->method_qns = mqns;
    }
}

// AST walk stacks for the passes below. The first chunk lives on the C stack, the
// same 256 slots the old fixed arrays used; a wider pending set grows on the heap
// through cbm_walk_stack_reserve and is released when the walk ends, so nothing
// is cut from the per-file result arena. A fixed cap used to stop pushing without
// a word, which skipped every top-level declaration past the 256th and left the
// return walk short of returns it had never reached (#2388).
enum { TS_WALK_STACK_INLINE = 256 };

static int ts_walk_pending_count(int top, uint32_t count, const char *walker) {
    if (top < 0 || count > (uint32_t)(INT_MAX - top)) {
        char pending[24];
        snprintf(pending, sizeof(pending), "%llu", (unsigned long long)count + (unsigned)top);
        cbm_log_error("extract.walk_stack_alloc_failed", "walker", walker, "pending", pending);
        return -1;
    }
    return top + (int)count;
}

#ifdef CBM_ENABLE_TEST_SEAMS
int cbm_ts_lsp_test_walk_pending_count(int top, uint32_t count) {
    return ts_walk_pending_count(top, count, "ts_lsp_test");
}
#endif

// Push every child of n in cursor order (one O(N) pass). The walk pops the stack,
// so children are visited last-child first: the order these walks have always
// used. False means the stack could not grow; cbm_walk_stack_reserve has logged it.
static bool ts_walk_push_children(TSNode **stack, int *cap, int *top, TSNode n,
                                  const TSNode *inline_buf, const char *walker) {
    uint32_t count = ts_node_child_count(n);
    if (count == 0)
        return true;
    int need = ts_walk_pending_count(*top, count, walker);
    if (need < 0 ||
        !cbm_walk_stack_reserve((void **)stack, cap, need, sizeof(TSNode), inline_buf, walker))
        return false;
    TSTreeCursor cursor = ts_tree_cursor_new(n);
    if (ts_tree_cursor_goto_first_child(&cursor)) {
        uint32_t pushed = 0;
        do {
            (*stack)[(*top)++] = ts_tree_cursor_current_node(&cursor);
            pushed++;
        } while (pushed < count && ts_tree_cursor_goto_next_sibling(&cursor));
    }
    ts_tree_cursor_delete(&cursor);
    return true;
}

static bool ts_walk_push(TSNode **stack, int *cap, int *top, TSNode n, const TSNode *inline_buf,
                         const char *walker) {
    int need = ts_walk_pending_count(*top, 1, walker);
    if (need < 0 ||
        !cbm_walk_stack_reserve((void **)stack, cap, need, sizeof(TSNode), inline_buf, walker))
        return false;
    (*stack)[(*top)++] = n;
    return true;
}

/* Return inference runs before the statement walk. Reserve declarations so
 * an unknown local or parameter cannot borrow a module constructor/function.
 * Reserving nested sibling bindings too can only withhold an inferred type. */
static void ts_reserve_return_bindings(TSLSPContext *ctx, TSNode fn) {
    TSTreeCursor cursor = ts_tree_cursor_new(fn);
    for (;;) {
        TSNode node = ts_tree_cursor_current_node(&cursor);
        TSNode binding = cbm_ts_return_binding(node);
        if (node_kind_is(binding, "type_identifier"))
            cbm_scope_bind(ctx->current_scope, node_text(ctx, binding), cbm_type_unknown());
        else
            bind_unknown_pattern(ctx, binding);
        if (ts_tree_cursor_goto_first_child(&cursor))
            continue;
        while (!ts_tree_cursor_goto_next_sibling(&cursor)) {
            if (!ts_tree_cursor_goto_parent(&cursor))
                goto done;
        }
    }
done:
    ts_tree_cursor_delete(&cursor);
}

/* Infer only when every return in this callable proves the same type.
 * Nested callables own their returns; traversal order never chooses a type. */
static const CBMType *infer_return_type_from_body(TSLSPContext *ctx, TSNode body) {
    if (ts_node_is_null(body) || !cbm_ts_returns_on_normal_exit(body, 0))
        return cbm_type_unknown();

    TSNode inline_stack[TS_WALK_STACK_INLINE];
    TSNode *stack = inline_stack;
    int cap = TS_WALK_STACK_INLINE;
    int top = 0;
    const CBMType *found = NULL;
    stack[top++] = body;
    while (top > 0) {
        TSNode n = stack[--top];
        if (ts_node_is_null(n))
            continue;
        const char *k = ts_node_type(n);
        if (strcmp(k, "return_statement") == 0) {
            // The first named child is the return expression (if any).
            uint32_t rnc = ts_node_named_child_count(n);
            if (rnc == 0) {
                found = cbm_type_unknown();
                break;
            }
            TSNode expr = ts_node_named_child(n, 0);
            if (ts_node_is_null(expr))
                continue;
            const CBMType *t = ts_eval_expr_type(ctx, expr);
            if (!t || cbm_type_is_unknown(t) || (found && !cbm_type_equal(found, t))) {
                found = cbm_type_unknown();
                break;
            }
            found = t;
            continue;
        }
        // Don't recurse into nested function bodies — their returns belong to them.
        if (ts_is_function_declaration(n) || ts_is_function_value(n) ||
            node_kind_is(n, "method_definition") || node_kind_is(n, "class_declaration") ||
            node_kind_is(n, "class"))
            continue;

        if (!ts_walk_push_children(&stack, &cap, &top, n, inline_stack, "ts_lsp_return_walk")) {
            found = cbm_type_unknown();
            break;
        }
    }
    cbm_walk_stack_release(stack, inline_stack);
    return found ? found : cbm_type_unknown();
}

// These two AST passes patch the FIRST matching local registration, even when
// the general registry index prefers the last duplicate. Do not follow fallback
// or copy its entries into the overlay. The snapshot lives only across these
// passes, which mutate signatures but never append or rename registered funcs.
typedef struct {
    CBMRegisteredFunc **slots;
    size_t capacity;
} TSSignatureIndex;

static void ts_signature_work(void) {
#ifdef CBM_ENABLE_TEST_SEAMS
    g_ts_signature_lookup_work++;
#endif
}

static size_t ts_signature_slot(const TSSignatureIndex *index, const char *qn) {
    uint64_t hash = 0xcbf29ce484222325ULL;
    for (const unsigned char *p = (const unsigned char *)qn; *p; p++) {
        hash ^= *p;
        hash *= 0x100000001b3ULL;
    }
    size_t slot = (size_t)hash & (index->capacity - 1);
    for (;;) {
        ts_signature_work();
        if (!index->slots[slot] || strcmp(index->slots[slot]->qualified_name, qn) == 0)
            return slot;
        slot = (slot + 1) & (index->capacity - 1);
    }
}

static TSSignatureIndex ts_signature_index(CBMTypeRegistry *reg) {
    TSSignatureIndex index = {0};
    if (reg->func_count <= 0 || (size_t)reg->func_count > SIZE_MAX / 2)
        return index;
    size_t capacity = 16;
    while (capacity < (size_t)reg->func_count * 2) {
        if (capacity > SIZE_MAX / 2)
            return index;
        capacity *= 2;
    }
    if (capacity > SIZE_MAX / sizeof(*index.slots))
        return index;
    index.slots = cbm_alloc(CBM_MEM_CLASS_EXTRACT, capacity * sizeof(*index.slots));
    if (!index.slots)
        return index; // Preserve the original lookup on allocation failure.
    index.capacity = capacity;
    memset(index.slots, 0, capacity * sizeof(*index.slots));
    for (int i = 0; i < reg->func_count; i++) {
        ts_signature_work();
        CBMRegisteredFunc *func = &reg->funcs[i];
        if (!func->qualified_name)
            continue;
        size_t slot = ts_signature_slot(&index, func->qualified_name);
        if (!index.slots[slot])
            index.slots[slot] = func;
    }
    return index;
}

static CBMRegisteredFunc *ts_signature_func(CBMTypeRegistry *reg, const TSSignatureIndex *index,
                                            const char *qn) {
    if (!qn)
        return NULL;
    if (index->slots)
        return index->slots[ts_signature_slot(index, qn)];
    for (int i = 0; i < reg->func_count; i++) {
        ts_signature_work();
        if (reg->funcs[i].qualified_name && strcmp(reg->funcs[i].qualified_name, qn) == 0)
            return &reg->funcs[i];
    }
    return NULL;
}

#ifdef CBM_ENABLE_TEST_SEAMS
int cbm_ts_lsp_test_signature_func_index(CBMTypeRegistry *reg, const char *qn) {
    TSSignatureIndex index = ts_signature_index(reg);
    CBMRegisteredFunc *func = ts_signature_func(reg, &index, qn);
    int result = func ? (int)(func - reg->funcs) : -1;
    cbm_free(CBM_MEM_CLASS_EXTRACT, index.slots);
    return result;
}
#endif

// Rebuild a function's CBMRegisteredFunc signature from the AST directly. extract_defs
// only handles type_identifier / generic_type / predefined_type for params, so function
// types (`(x: Foo) => void`), object types, tuple types etc. are missing from
// def->param_types. This pass walks the AST and rebuilds signatures from scratch.
//
// Called after `register_file_defs` so the func entries already exist; we only mutate
// in place.
static void rebuild_signatures_from_ast(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg,
                                        const TSSignatureIndex *index) {
    if (ts_node_is_null(root) || !reg || !ctx->module_qn)
        return;

    // Seeded with every top-level child, so a file with more than 256 of them
    // needs the growing stack (see TS_WALK_STACK_INLINE). If it cannot grow, the
    // walk stops and the declarations not yet reached keep extract_defs' signature.
    TSNode inline_stack[TS_WALK_STACK_INLINE];
    TSNode *stack = inline_stack;
    int cap = TS_WALK_STACK_INLINE;
    int top = 0;
    bool walking =
        ts_walk_push_children(&stack, &cap, &top, root, inline_stack, "ts_lsp_rebuild_signatures");

    while (walking && top > 0) {
        TSNode n = stack[--top];
        if (ts_node_is_null(n))
            continue;
        const char *k = ts_node_type(n);

        // Recurse into export_statement and class bodies.
        if (strcmp(k, "export_statement") == 0 || strcmp(k, "class_body") == 0) {
            walking = ts_walk_push_children(&stack, &cap, &top, n, inline_stack,
                                            "ts_lsp_rebuild_signatures");
            continue;
        }
        if (strcmp(k, "class_declaration") == 0) {
            TSNode body = ts_node_child_by_field_name(n, "body", TS_LSP_FIELD_LEN("body"));
            if (!ts_node_is_null(body))
                walking = ts_walk_push(&stack, &cap, &top, body, inline_stack,
                                       "ts_lsp_rebuild_signatures");
            continue;
        }

        bool is_func = (strcmp(k, "function_declaration") == 0);
        bool is_method = (strcmp(k, "method_definition") == 0);
        if (!is_func && !is_method)
            continue;

        TSNode name_node = ts_node_child_by_field_name(n, "name", TS_LSP_FIELD_LEN("name"));
        if (ts_node_is_null(name_node))
            continue;
        char *fname = node_text(ctx, name_node);
        if (!fname)
            continue;

        // Resolve this declaration's FQN to find its registered func.
        const char *fqn = NULL;
        if (is_func) {
            fqn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, fname);
        } else {
            // Method: climb to enclosing class_declaration.
            TSNode parent = ts_node_parent(n);
            while (!ts_node_is_null(parent) &&
                   strcmp(ts_node_type(parent), "class_declaration") != 0) {
                parent = ts_node_parent(parent);
            }
            if (ts_node_is_null(parent))
                continue;
            TSNode cn = ts_node_child_by_field_name(parent, "name", TS_LSP_FIELD_LEN("name"));
            if (ts_node_is_null(cn))
                continue;
            char *cname = node_text(ctx, cn);
            if (!cname)
                continue;
            fqn = cbm_arena_sprintf(ctx->arena, "%s.%s.%s", ctx->module_qn, cname, fname);
        }

        // Rebuild parameters from AST.
        TSNode params =
            ts_node_child_by_field_name(n, "parameters", TS_LSP_FIELD_LEN("parameters"));
        const char *p_names[32] = {0};
        const CBMType *p_types[32] = {0};
        int pc = 0;
        if (!ts_node_is_null(params)) {
            uint32_t pnc = ts_node_named_child_count(params);
            for (uint32_t i = 0; i < pnc && pc < 31; i++) {
                TSNode p = ts_node_named_child(params, i);
                if (ts_node_is_null(p))
                    continue;
                const char *pk = ts_node_type(p);
                if (strcmp(pk, "required_parameter") != 0 && strcmp(pk, "optional_parameter") != 0)
                    continue;

                // Param name.
                TSNode pat = ts_node_child_by_field_name(p, "pattern", TS_LSP_FIELD_LEN("pattern"));
                if (ts_node_is_null(pat)) {
                    pat = ts_node_child_by_field_name(p, "name", TS_LSP_FIELD_LEN("name"));
                }
                if (ts_node_is_null(pat) || strcmp(ts_node_type(pat), "identifier") != 0)
                    continue;
                char *pn = node_text(ctx, pat);
                if (!pn)
                    continue;

                // Param type.
                const CBMType *pt = cbm_type_unknown();
                TSNode tann = ts_node_child_by_field_name(p, "type", TS_LSP_FIELD_LEN("type"));
                if (ts_node_is_null(tann)) {
                    // Fall back to kind-based search.
                    uint32_t pcnt = ts_node_named_child_count(p);
                    for (uint32_t j = 0; j < pcnt; j++) {
                        TSNode c = ts_node_named_child(p, j);
                        if (!ts_node_is_null(c) &&
                            strcmp(ts_node_type(c), "type_annotation") == 0) {
                            tann = c;
                            break;
                        }
                    }
                }
                if (!ts_node_is_null(tann)) {
                    TSNode tch = (strcmp(ts_node_type(tann), "type_annotation") == 0)
                                     ? ts_node_named_child(tann, 0)
                                     : tann;
                    if (!ts_node_is_null(tch))
                        pt = ts_parse_type_node(ctx, tch);
                }

                p_names[pc] = pn;
                p_types[pc] = pt;
                pc++;
            }
        }
        p_names[pc] = NULL;
        p_types[pc] = NULL;

        // Rebuild return type from AST.
        const CBMType *ret = cbm_type_unknown();
        TSNode rt_node =
            ts_node_child_by_field_name(n, "return_type", TS_LSP_FIELD_LEN("return_type"));
        if (!ts_node_is_null(rt_node)) {
            TSNode tch = (strcmp(ts_node_type(rt_node), "type_annotation") == 0)
                             ? ts_node_named_child(rt_node, 0)
                             : rt_node;
            if (!ts_node_is_null(tch))
                ret = ts_parse_type_node(ctx, tch);
        }

        // Build new signature and patch in registry.
        const CBMType *rets[2] = {ret, NULL};
        const CBMType *new_sig = cbm_type_func(ctx->arena, p_names, p_types, rets);
        CBMRegisteredFunc *func = ts_signature_func(reg, index, fqn);
        if (func) {
            // Preserve the ret type if AST gave UNKNOWN but the existing reg sig had one.
            if (cbm_type_is_unknown(ret) && func->signature &&
                func->signature->kind == CBM_TYPE_FUNC && func->signature->data.func.return_types &&
                func->signature->data.func.return_types[0] &&
                !cbm_type_is_unknown(func->signature->data.func.return_types[0])) {
                const CBMType *preserved[2] = {func->signature->data.func.return_types[0], NULL};
                new_sig = cbm_type_func(ctx->arena, p_names, p_types, preserved);
            }
            func->signature = new_sig;
        }
    }
    cbm_walk_stack_release(stack, inline_stack);
}

// Convert NAMED references to TYPE_PARAM for any function whose declaration has a
// `type_parameters` block. Without this, generic functions like `function id<T>(x: T): T`
// register T as NAMED("module.T") instead of TYPE_PARAM("T"), defeating substitution.
static void convert_signature_type_params(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg,
                                          const TSSignatureIndex *index) {
    if (ts_node_is_null(root) || !reg || !ctx->module_qn)
        return;

    // Walk: function_declaration, class_declaration { method_definition }, plus exported.
    // Seeded with every top-level child, so a file with more than 256 of them needs
    // the growing stack (see TS_WALK_STACK_INLINE). If it cannot grow, the walk stops
    // and the generics not yet reached keep their NAMED parameters.
    TSNode inline_stack[TS_WALK_STACK_INLINE];
    TSNode *stack = inline_stack;
    int cap = TS_WALK_STACK_INLINE;
    int top = 0;
    bool walking =
        ts_walk_push_children(&stack, &cap, &top, root, inline_stack, "ts_lsp_type_params");

    while (walking && top > 0) {
        TSNode n = stack[--top];
        if (ts_node_is_null(n))
            continue;
        const char *k = ts_node_type(n);

        // Recurse into export_statement and class_body.
        if (strcmp(k, "export_statement") == 0 || strcmp(k, "class_body") == 0) {
            walking =
                ts_walk_push_children(&stack, &cap, &top, n, inline_stack, "ts_lsp_type_params");
            continue;
        }
        if (strcmp(k, "class_declaration") == 0) {
            TSNode body = ts_node_child_by_field_name(n, "body", TS_LSP_FIELD_LEN("body"));
            if (!ts_node_is_null(body))
                walking =
                    ts_walk_push(&stack, &cap, &top, body, inline_stack, "ts_lsp_type_params");
            continue;
        }

        bool is_func = (strcmp(k, "function_declaration") == 0);
        bool is_method = (strcmp(k, "method_definition") == 0);
        if (!is_func && !is_method)
            continue;

        TSNode tparams =
            ts_node_child_by_field_name(n, "type_parameters", TS_LSP_FIELD_LEN("type_parameters"));
        if (ts_node_is_null(tparams))
            continue;

        // Collect type param names.
        const char *names[16] = {0};
        const CBMType *args[16] = {0};
        int tpc = 0;
        uint32_t tnc = ts_node_named_child_count(tparams);
        for (uint32_t i = 0; i < tnc && tpc < 15; i++) {
            TSNode tp = ts_node_named_child(tparams, i);
            if (ts_node_is_null(tp))
                continue;
            // type_parameter has child name (type_identifier or identifier).
            TSNode tname = ts_node_child_by_field_name(tp, "name", TS_LSP_FIELD_LEN("name"));
            if (ts_node_is_null(tname)) {
                // First named child fallback.
                if (ts_node_named_child_count(tp) > 0) {
                    tname = ts_node_named_child(tp, 0);
                }
            }
            if (ts_node_is_null(tname))
                continue;
            char *nm = node_text(ctx, tname);
            if (!nm)
                continue;
            names[tpc] = nm;
            args[tpc] = cbm_type_type_param(ctx->arena, nm);
            tpc++;
        }
        names[tpc] = NULL;
        args[tpc] = NULL;
        if (tpc == 0)
            continue;

        // Resolve the function's QN.
        TSNode name_node = ts_node_child_by_field_name(n, "name", TS_LSP_FIELD_LEN("name"));
        if (ts_node_is_null(name_node))
            continue;
        char *fname = node_text(ctx, name_node);
        if (!fname)
            continue;

        // For methods, the receiver class must be in QN. For free functions, just module.
        const char *fqn = NULL;
        if (is_func) {
            fqn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, fname);
        } else {
            // Climb to enclosing class_declaration.
            TSNode parent = ts_node_parent(n);
            while (!ts_node_is_null(parent) &&
                   strcmp(ts_node_type(parent), "class_declaration") != 0) {
                parent = ts_node_parent(parent);
            }
            if (ts_node_is_null(parent))
                continue;
            TSNode cn = ts_node_child_by_field_name(parent, "name", TS_LSP_FIELD_LEN("name"));
            if (ts_node_is_null(cn))
                continue;
            char *cname = node_text(ctx, cn);
            if (!cname)
                continue;
            fqn = cbm_arena_sprintf(ctx->arena, "%s.%s.%s", ctx->module_qn, cname, fname);
        }

        // Patch the registered func's signature: rewrite NAMED → TYPE_PARAM.
        CBMRegisteredFunc *func = ts_signature_func(reg, index, fqn);
        if (func) {
            const CBMType *old_sig = func->signature;
            if (!old_sig)
                continue;
            const CBMType *new_sig = cbm_type_substitute(ctx->arena, old_sig, names, args);
            if (new_sig)
                func->signature = new_sig;
            // Also store the type_param_names for later overload-by-types use.
            const char **stored = (const char **)cbm_arena_alloc(
                ctx->arena, (size_t)(tpc + 1) * sizeof(const char *));
            if (stored) {
                for (int ti = 0; ti < tpc; ti++)
                    stored[ti] = names[ti];
                stored[tpc] = NULL;
                func->type_param_names = stored;
            }
        }
    }
    cbm_walk_stack_release(stack, inline_stack);
}

// Build once after shape registration, then release before later passes may
// grow the registry. This keeps per-file lookup storage out of the result arena.
static void refine_ast_signatures(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg) {
    TSSignatureIndex index = ts_signature_index(reg);
    rebuild_signatures_from_ast(ctx, root, reg, &index);
    convert_signature_type_params(ctx, root, reg, &index);
    cbm_free(CBM_MEM_CLASS_EXTRACT, index.slots);
}

// Parse a JSDoc comment block for `@param {T} name` and `@returns {T}` tags. For each
// match, returns the type as a parsed CBMType. Used in `js_mode` to infer signatures
// for JavaScript files where there are no inline type annotations.
//
// Pragmatic v1: scans the comment text linearly. Handles:
//   * @param {T} name — description
//   * @returns {T} — description
//   * @return {T}
// Skips: nested braces in the type, complex JSDoc syntax (callback definitions,
//        @typedef, etc.). Falls back gracefully on UNKNOWN.
typedef struct {
    const char *name;
    const CBMType *type;
} JSDocParam;

static void parse_jsdoc_block(TSLSPContext *ctx, const char *text, size_t len,
                              JSDocParam *out_params, int *out_param_count, int max_params,
                              const CBMType **out_return) {
    *out_return = NULL;
    *out_param_count = 0;
    if (!text || len == 0)
        return;

    const char *end = text + len;
    const char *p = text;
    while (p < end) {
        // Find next `@` that introduces a tag.
        while (p < end && *p != '@')
            p++;
        if (p >= end)
            return;
        p++; // skip @

        // Match "param" or "returns"/"return".
        const char *tag_start = p;
        while (p < end && (*p >= 'a' && *p <= 'z'))
            p++;
        size_t tag_len = (size_t)(p - tag_start);
        bool is_param = (tag_len == 5 && memcmp(tag_start, "param", 5) == 0);
        bool is_return = ((tag_len == 7 && memcmp(tag_start, "returns", 7) == 0) ||
                          (tag_len == 6 && memcmp(tag_start, "return", 6) == 0));
        if (!is_param && !is_return)
            continue;

        // Skip whitespace.
        while (p < end && (*p == ' ' || *p == '\t'))
            p++;
        if (p >= end || *p != '{')
            continue;
        p++; // skip {
        const char *type_start = p;
        int depth = 1;
        while (p < end && depth > 0) {
            if (*p == '{')
                depth++;
            else if (*p == '}')
                depth--;
            if (depth > 0)
                p++;
        }
        if (p >= end || *p != '}')
            continue;
        size_t type_len = (size_t)(p - type_start);
        char *type_text = cbm_arena_strndup(ctx->arena, type_start, type_len);
        const CBMType *parsed = parse_ts_type_text(ctx->arena, type_text, ctx->module_qn);
        p++; // skip }

        if (is_return) {
            *out_return = parsed;
            continue;
        }

        // Param: skip whitespace then read name.
        while (p < end && (*p == ' ' || *p == '\t'))
            p++;
        const char *name_start = p;
        while (p < end && ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') ||
                           (*p >= '0' && *p <= '9') || *p == '_' || *p == '$' || *p == '.'))
            p++;
        size_t name_len = (size_t)(p - name_start);
        if (name_len == 0)
            continue;
        if (*out_param_count < max_params) {
            char *nm = cbm_arena_strndup(ctx->arena, name_start, name_len);
            out_params[*out_param_count].name = nm;
            out_params[*out_param_count].type = parsed;
            (*out_param_count)++;
        }
    }
}

// For each function_declaration in `js_mode` with a JSDoc-style comment immediately
// before it, parse the comment and patch the registered func's signature.
static void apply_jsdoc_signatures(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg) {
    if (!ctx->js_mode || ts_node_is_null(root) || !reg || !ctx->module_qn)
        return;

    uint32_t kn = 0;
    TSNode *kids = collect_children(ctx->arena, root, &kn);
    for (uint32_t i = 0; i < kn; i++) {
        TSNode n = kids[i];
        if (strcmp(ts_node_type(n), "function_declaration") != 0)
            continue;

        // Find the immediate preceding comment sibling (skip whitespace nodes which
        // tree-sitter doesn't expose as named children, but unnamed children may include
        // comment nodes).
        TSNode prev = {0};
        for (int j = (int)i - 1; j >= 0; j--) {
            TSNode candidate = kids[j];
            const char *ck = ts_node_type(candidate);
            if (strcmp(ck, "comment") == 0) {
                prev = candidate;
                break;
            }
            // Anything else: stop — JSDoc must be immediately preceding.
            if (ts_node_is_named(candidate))
                break;
        }
        if (ts_node_is_null(prev))
            continue;

        // Get comment text and check JSDoc shape (`/** ... */`).
        char *ctext = node_text(ctx, prev);
        if (!ctext)
            continue;
        size_t clen = strlen(ctext);
        if (clen < 4 || ctext[0] != '/' || ctext[1] != '*' || ctext[2] != '*')
            continue;

        JSDocParam params[16];
        int pcount = 0;
        const CBMType *ret = NULL;
        parse_jsdoc_block(ctx, ctext + 3, clen - 3, params, &pcount, 16, &ret);

        // Resolve the function's QN and patch the registered signature.
        TSNode name_node = ts_node_child_by_field_name(n, "name", TS_LSP_FIELD_LEN("name"));
        if (ts_node_is_null(name_node))
            continue;
        char *fname = node_text(ctx, name_node);
        if (!fname)
            continue;
        const char *fqn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, fname);

        for (int fi = 0; fi < reg->func_count; fi++) {
            if (!reg->funcs[fi].qualified_name)
                continue;
            if (strcmp(reg->funcs[fi].qualified_name, fqn) != 0)
                continue;
            const CBMType *old_sig = reg->funcs[fi].signature;
            const CBMType **rets = NULL;
            if (ret && !cbm_type_is_unknown(ret)) {
                rets = (const CBMType **)cbm_arena_alloc(ctx->arena, 2 * sizeof(const CBMType *));
                if (rets) {
                    rets[0] = ret;
                    rets[1] = NULL;
                }
            } else if (old_sig && old_sig->kind == CBM_TYPE_FUNC) {
                rets = old_sig->data.func.return_types;
            }
            const CBMType **params_arr = NULL;
            const char **param_names_arr = NULL;
            if (pcount > 0) {
                params_arr = (const CBMType **)cbm_arena_alloc(
                    ctx->arena, (size_t)(pcount + 1) * sizeof(const CBMType *));
                param_names_arr = (const char **)cbm_arena_alloc(
                    ctx->arena, (size_t)(pcount + 1) * sizeof(const char *));
                if (params_arr && param_names_arr) {
                    for (int j = 0; j < pcount; j++) {
                        params_arr[j] = params[j].type;
                        param_names_arr[j] = params[j].name;
                    }
                    params_arr[pcount] = NULL;
                    param_names_arr[pcount] = NULL;
                }
            } else if (old_sig && old_sig->kind == CBM_TYPE_FUNC) {
                params_arr = old_sig->data.func.param_types;
                param_names_arr = old_sig->data.func.param_names;
            }
            reg->funcs[fi].signature = cbm_type_func(ctx->arena, param_names_arr, params_arr, rets);
            break;
        }
    }
}

// For each function_declaration whose registered signature has no return type, infer
// it from the body and rebuild the signature. This mirrors typescript-go's
// implicit return-type inference at a coarse level (single-return common case).
static void infer_implicit_returns(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg) {
    if (ts_node_is_null(root) || !reg || !ctx->module_qn)
        return;
    ts_collect_assign_sites(ctx, root);
    uint32_t kn = 0;
    TSNode *kids = collect_children(ctx->arena, root, &kn);

    for (uint32_t i = 0; i < kn; i++) {
        TSNode n = kids[i];
        const char *k = ts_node_type(n);

        TSNode decl = n;
        if (strcmp(k, "export_statement") == 0) {
            TSNode d =
                ts_node_child_by_field_name(n, "declaration", TS_LSP_FIELD_LEN("declaration"));
            if (!ts_node_is_null(d)) {
                decl = d;
                k = ts_node_type(decl);
            }
        }

        if (strcmp(k, "function_declaration") != 0)
            continue;

        TSNode name_node = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
        TSNode body = ts_node_child_by_field_name(decl, "body", TS_LSP_FIELD_LEN("body"));
        if (ts_node_is_null(name_node) || ts_node_is_null(body))
            continue;

        char *fname = node_text(ctx, name_node);
        if (!fname || !ts_proof_name(ctx, decl, fname))
            continue;
        const char *fqn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, fname);
        const CBMRegisteredFunc *existing = ts_lookup_func(ctx, reg, fqn);
        if (!existing)
            continue;
        // Only infer when the existing signature lacks an explicit return type.
        if (existing->signature && existing->signature->kind == CBM_TYPE_FUNC &&
            existing->signature->data.func.return_types &&
            existing->signature->data.func.return_types[0] &&
            !cbm_type_is_unknown(existing->signature->data.func.return_types[0])) {
            continue;
        }

        /* An explicit unknown/any return is a boundary, not an invitation to
         * replace the annotation with a concrete value seen in the body. */
        if (!ts_node_is_null(ts_node_child_by_field_name(decl, "return_type", 11)))
            continue;
        CBMScope *saved_scope = ctx->current_scope;
        struct TsEvalMemo *saved_memo = ctx->eval_memo;
        ctx->current_scope = cbm_scope_push(ctx->arena, saved_scope);
        ctx->eval_memo = NULL;
        ts_reserve_return_bindings(ctx, decl);
        const CBMType *inferred = infer_return_type_from_body(ctx, body);
        ctx->current_scope = saved_scope;
        ctx->eval_memo = saved_memo;
        if (cbm_type_is_unknown(inferred))
            continue;
        for (uint32_t j = 0; j < ts_node_child_count(decl); j++) {
            if (node_kind_is(ts_node_child(decl, j), "async")) {
                const CBMType *args[] = {ts_awaited_type_at(ctx, inferred, 0), NULL};
                inferred = cbm_type_template(ctx->arena, "Promise", args, 1);
                break;
            }
        }

        // Build a new FUNC signature carrying over params from the existing one (if any).
        const char **param_names = NULL;
        const CBMType **param_types = NULL;
        if (existing->signature && existing->signature->kind == CBM_TYPE_FUNC) {
            param_names = existing->signature->data.func.param_names;
            param_types = existing->signature->data.func.param_types;
        }
        const CBMType *rets[2] = {inferred, NULL};
        const CBMType *new_sig = cbm_type_func(ctx->arena, param_names, param_types, rets);

        // Patch the registered func in place: the first of that QN in reg.
        CBMRegisteredFunc *own = (CBMRegisteredFunc *)ts_own_func(ctx, reg, fqn);
        if (own) {
            own->signature = new_sig;
        }
    }
}

/* Interface methods are synthesized after definition extraction and therefore
 * cannot consume the CBMLSPDef ordered carrier.  Build their FUNC type from the
 * AST without matching by QN (overloads intentionally share a QN). */
static const CBMType *interface_method_signature_from_ast(TSLSPContext *ctx, TSNode method,
                                                          int *out_min_params) {
    const CBMType *param_types[32] = {0};
    int param_count = 0;
    int min_params = 0;
    TSNode params =
        ts_node_child_by_field_name(method, "parameters", TS_LSP_FIELD_LEN("parameters"));
    if (!ts_node_is_null(params)) {
        uint32_t count = ts_node_named_child_count(params);
        for (uint32_t i = 0; i < count && param_count < 31; i++) {
            TSNode param = ts_node_named_child(params, i);
            const char *kind = ts_node_type(param);
            if (strcmp(kind, "required_parameter") != 0 &&
                strcmp(kind, "optional_parameter") != 0) {
                continue;
            }

            TSNode pattern =
                ts_node_child_by_field_name(param, "pattern", TS_LSP_FIELD_LEN("pattern"));
            if (ts_node_is_null(pattern)) {
                pattern = ts_node_child_by_field_name(param, "name", TS_LSP_FIELD_LEN("name"));
            }
            if (!ts_node_is_null(pattern)) {
                char *name = node_text(ctx, pattern);
                if (name && strcmp(name, "this") == 0)
                    continue;
            }

            const CBMType *param_type = cbm_type_unknown();
            TSNode annotation =
                ts_node_child_by_field_name(param, "type", TS_LSP_FIELD_LEN("type"));
            if (ts_node_is_null(annotation)) {
                uint32_t child_count = ts_node_named_child_count(param);
                for (uint32_t j = 0; j < child_count; j++) {
                    TSNode child = ts_node_named_child(param, j);
                    if (strcmp(ts_node_type(child), "type_annotation") == 0) {
                        annotation = child;
                        break;
                    }
                }
            }
            if (!ts_node_is_null(annotation)) {
                TSNode type_node = strcmp(ts_node_type(annotation), "type_annotation") == 0
                                       ? ts_node_named_child(annotation, 0)
                                       : annotation;
                if (!ts_node_is_null(type_node))
                    param_type = ts_parse_type_node(ctx, type_node);
            }
            param_types[param_count++] = param_type;

            if (strcmp(kind, "required_parameter") == 0) {
                TSNode value =
                    ts_node_child_by_field_name(param, "value", TS_LSP_FIELD_LEN("value"));
                bool rest =
                    !ts_node_is_null(pattern) && strcmp(ts_node_type(pattern), "rest_pattern") == 0;
                if (ts_node_is_null(value) && !rest)
                    min_params++;
            }
        }
    }
    param_types[param_count] = NULL;

    const CBMType *return_type = cbm_type_unknown();
    TSNode return_node =
        ts_node_child_by_field_name(method, "return_type", TS_LSP_FIELD_LEN("return_type"));
    if (!ts_node_is_null(return_node)) {
        TSNode type_node = strcmp(ts_node_type(return_node), "type_annotation") == 0
                               ? ts_node_named_child(return_node, 0)
                               : return_node;
        if (!ts_node_is_null(type_node))
            return_type = ts_parse_type_node(ctx, type_node);
    }
    const CBMType *return_types[2] = {return_type, NULL};
    if (out_min_params)
        *out_min_params = min_params;
    return cbm_type_func(ctx->arena, NULL, param_count ? param_types : NULL, return_types);
}

/* Parsed type of a `type_annotation` field (`: T`), or unknown. */
static const CBMType *ts_annotation_field_type(TSLSPContext *ctx, TSNode owner) {
    TSNode tann = ts_node_child_by_field_name(owner, "type", TS_LSP_FIELD_LEN("type"));
    if (ts_node_is_null(tann))
        return cbm_type_unknown();
    TSNode tn =
        strcmp(ts_node_type(tann), "type_annotation") == 0 ? ts_node_named_child(tann, 0) : tann;
    return ts_node_is_null(tn) ? cbm_type_unknown() : ts_parse_type_node(ctx, tn);
}

/* Declared type of a class field (`public_field_definition`) or interface
 * property: the annotation when present, else, for an unannotated field
 * initialised with `new C()`, the type of that instance (#514). No other
 * initializer is inferred: `new` names its type exactly, arbitrary
 * expressions do not. */
static const CBMType *ts_field_decl_type(TSLSPContext *ctx, TSNode m) {
    if (!ts_node_is_null(ts_node_child_by_field_name(m, "type", TS_LSP_FIELD_LEN("type"))))
        return ts_annotation_field_type(ctx, m);
    TSNode val = ts_node_child_by_field_name(m, "value", TS_LSP_FIELD_LEN("value"));
    if (ts_node_is_null(val) || strcmp(ts_node_type(val), "new_expression") != 0)
        return cbm_type_unknown();
    const CBMType *nt = ts_new_expression_type(ctx, val);
    return nt ? nt : cbm_type_unknown();
}

/* A constructor parameter is a TS parameter property, i.e. also declares a
 * class field, iff it carries an accessibility modifier, `readonly` or
 * `override`. */
static bool ts_param_is_property(TSNode p) {
    uint32_t pc = ts_node_child_count(p);
    for (uint32_t ci = 0; ci < pc; ci++) {
        const char *ck = ts_node_type(ts_node_child(p, ci));
        if (strcmp(ck, "accessibility_modifier") == 0 || strcmp(ck, "readonly") == 0 ||
            strcmp(ck, "override_modifier") == 0)
            return true;
    }
    return false;
}

/* Append the parameter properties of a `constructor` method_definition to
 * the field arrays (#514): `constructor(private readonly svc: Svc)` declares
 * field `svc: Svc`, the dominant NestJS injection shape. Any other member is
 * ignored. Returns the new field count. */
static int ts_collect_param_properties(TSLSPContext *ctx, TSNode m, const char **names,
                                       const CBMType **types, int count, int cap) {
    TSNode mname = ts_node_child_by_field_name(m, "name", TS_LSP_FIELD_LEN("name"));
    char *mnm = ts_node_is_null(mname) ? NULL : node_text(ctx, mname);
    if (!mnm || strcmp(mnm, "constructor") != 0)
        return count;
    TSNode params = ts_node_child_by_field_name(m, "parameters", TS_LSP_FIELD_LEN("parameters"));
    uint32_t pnc = ts_node_is_null(params) ? 0 : ts_node_named_child_count(params);
    for (uint32_t pi = 0; pi < pnc && count < cap; pi++) {
        TSNode p = ts_node_named_child(params, pi);
        const char *pk = ts_node_type(p);
        if ((strcmp(pk, "required_parameter") != 0 && strcmp(pk, "optional_parameter") != 0) ||
            !ts_param_is_property(p))
            continue;
        TSNode pat = ts_node_child_by_field_name(p, "pattern", TS_LSP_FIELD_LEN("pattern"));
        if (ts_node_is_null(pat) || strcmp(ts_node_type(pat), "identifier") != 0)
            continue;
        char *pnm = node_text(ctx, pat);
        if (!pnm)
            continue;
        names[count] = pnm;
        types[count] = ts_annotation_field_type(ctx, p);
        count++;
    }
    return count;
}

// AST sweep: walk class/interface bodies to collect field names+types and refine
// embedded_types / type_param_names.
static void ast_sweep_shapes(TSLSPContext *ctx, TSNode root, CBMTypeRegistry *reg) {
    if (ts_node_is_null(root) || !reg)
        return;
    uint32_t kn = 0;
    TSNode *kids = collect_children(ctx->arena, root, &kn);

    for (uint32_t i = 0; i < kn; i++) {
        TSNode n = kids[i];
        const char *k = ts_node_type(n);
        TSNode decl = n;
        if (strcmp(k, "export_statement") == 0) {
            // Look for declaration field.
            TSNode d =
                ts_node_child_by_field_name(n, "declaration", TS_LSP_FIELD_LEN("declaration"));
            if (!ts_node_is_null(d)) {
                decl = d;
                k = ts_node_type(decl);
            }
        }

        if (strcmp(k, "type_alias_declaration") == 0) {
            TSNode name = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
            TSNode val = ts_node_child_by_field_name(decl, "value", TS_LSP_FIELD_LEN("value"));
            if (ts_node_is_null(name) || ts_node_is_null(val) || !ctx->module_qn)
                continue;
            char *nm = node_text(ctx, name);
            if (!nm)
                continue;
            const char *qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, nm);
            // alias_of: resolved to QN if it's a NAMED text we can qualify.
            char *val_text = node_text(ctx, val);
            const char *alias_qn = NULL;
            if (val_text && val_text[0] && strchr(val_text, ' ') == NULL &&
                strchr(val_text, '|') == NULL && strchr(val_text, '&') == NULL) {
                if (strchr(val_text, '.') == NULL && val_text[0] >= 'A' && val_text[0] <= 'Z') {
                    alias_qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, val_text);
                } else {
                    alias_qn = cbm_arena_strdup(ctx->arena, val_text);
                }
            }
            // Find or insert.
            bool found = false;
            for (int ti = 0; ti < reg->type_count; ti++) {
                if (reg->types[ti].qualified_name &&
                    strcmp(reg->types[ti].qualified_name, qn) == 0) {
                    if (alias_qn)
                        reg->types[ti].alias_of = alias_qn;
                    found = true;
                    break;
                }
            }
            if (!found) {
                CBMRegisteredType rt;
                memset(&rt, 0, sizeof(rt));
                rt.qualified_name = qn;
                rt.short_name = nm;
                rt.alias_of = alias_qn;
                cbm_registry_add_type(reg, rt);
            }
            continue;
        }

        if (strcmp(k, "class_declaration") != 0 && strcmp(k, "interface_declaration") != 0) {
            continue;
        }

        TSNode name_node = ts_node_child_by_field_name(decl, "name", TS_LSP_FIELD_LEN("name"));
        TSNode body = ts_node_child_by_field_name(decl, "body", TS_LSP_FIELD_LEN("body"));
        if (ts_node_is_null(name_node) || ts_node_is_null(body) || !ctx->module_qn)
            continue;
        char *cname = node_text(ctx, name_node);
        if (!cname)
            continue;
        const char *class_qn = cbm_arena_sprintf(ctx->arena, "%s.%s", ctx->module_qn, cname);

        // Find the registered type and augment with fields.
        CBMRegisteredType *rt = NULL;
        for (int ti = 0; ti < reg->type_count; ti++) {
            if (reg->types[ti].qualified_name &&
                strcmp(reg->types[ti].qualified_name, class_qn) == 0) {
                rt = &reg->types[ti];
                break;
            }
        }
        if (!rt)
            continue;

        const char *field_names[64] = {0};
        const CBMType *field_types[64] = {0};
        int field_count = 0;
        // Interface method signatures we need to register as separate funcs.
        const char *iface_method_names[64] = {0};
        const char *iface_method_qns[64] = {0};
        const CBMType *iface_method_sigs[64] = {0};
        int iface_method_count = 0;
        bool is_interface = (strcmp(k, "interface_declaration") == 0);

        uint32_t bnc = ts_node_named_child_count(body);
        for (uint32_t bi = 0; bi < bnc && field_count < 63; bi++) {
            TSNode m = ts_node_named_child(body, bi);
            if (ts_node_is_null(m))
                continue;
            const char *mk = ts_node_type(m);

            // public_field_definition: TS class fields.
            // property_signature: interface fields. Interface fields can be either
            // a bare property (string name) OR a callable property (function-type field).
            if (strcmp(mk, "public_field_definition") == 0 ||
                strcmp(mk, "property_signature") == 0) {
                TSNode fname = ts_node_child_by_field_name(m, "name", TS_LSP_FIELD_LEN("name"));
                if (ts_node_is_null(fname))
                    continue;
                char *fnm = node_text(ctx, fname);
                if (!fnm)
                    continue;
                field_names[field_count] = fnm;
                field_types[field_count] = ts_field_decl_type(ctx, m);
                field_count++;
                continue;
            }

            // Constructor parameter properties are class fields too (#514).
            if (!is_interface && strcmp(mk, "method_definition") == 0) {
                field_count =
                    ts_collect_param_properties(ctx, m, field_names, field_types, field_count, 63);
                continue;
            }

            // Interface method signature: `methodName(params): ReturnType;`
            // Or class method declaration in `.d.ts` ambient mode.
            if (is_interface && (strcmp(mk, "method_signature") == 0)) {
                if (iface_method_count >= 63)
                    continue;
                TSNode mname = ts_node_child_by_field_name(m, "name", TS_LSP_FIELD_LEN("name"));
                if (ts_node_is_null(mname))
                    continue;
                char *mnm = node_text(ctx, mname);
                if (!mnm)
                    continue;

                int min_params = -1;
                const CBMType *sig = interface_method_signature_from_ast(ctx, m, &min_params);

                const char *mqn = cbm_arena_sprintf(ctx->arena, "%s.%s", class_qn, mnm);
                iface_method_names[iface_method_count] = mnm;
                iface_method_qns[iface_method_count] = mqn;
                iface_method_sigs[iface_method_count] = sig;
                iface_method_count++;

                // Also register a CBMRegisteredFunc so cbm_registry_lookup_method picks it up.
                CBMRegisteredFunc rf;
                memset(&rf, 0, sizeof(rf));
                rf.qualified_name = mqn;
                rf.short_name = mnm;
                rf.receiver_type = class_qn;
                rf.signature = sig;
                rf.min_params = min_params;
                cbm_registry_add_func(reg, rf);
            }
        }
        if (field_count > 0) {
            const char **fn_arr = (const char **)cbm_arena_alloc(
                ctx->arena, (size_t)(field_count + 1) * sizeof(const char *));
            const CBMType **ft_arr = (const CBMType **)cbm_arena_alloc(
                ctx->arena, (size_t)(field_count + 1) * sizeof(const CBMType *));
            if (fn_arr && ft_arr) {
                for (int j = 0; j < field_count; j++) {
                    fn_arr[j] = field_names[j];
                    ft_arr[j] = field_types[j];
                }
                fn_arr[field_count] = NULL;
                ft_arr[field_count] = NULL;
                rt->field_names = fn_arr;
                rt->field_types = ft_arr;
            }
        }

        // Attach interface method names/qns to the registered type.
        if (iface_method_count > 0) {
            const char **mn_arr = (const char **)cbm_arena_alloc(
                ctx->arena, (size_t)(iface_method_count + 1) * sizeof(const char *));
            const char **mq_arr = (const char **)cbm_arena_alloc(
                ctx->arena, (size_t)(iface_method_count + 1) * sizeof(const char *));
            if (mn_arr && mq_arr) {
                for (int j = 0; j < iface_method_count; j++) {
                    mn_arr[j] = iface_method_names[j];
                    mq_arr[j] = iface_method_qns[j];
                }
                mn_arr[iface_method_count] = NULL;
                mq_arr[iface_method_count] = NULL;
                rt->method_names = mn_arr;
                rt->method_qns = mq_arr;
            }
            (void)iface_method_sigs; // sigs already attached via cbm_registry_add_func
        }
    }
}

void cbm_run_ts_lsp(CBMArena *arena, CBMFileResult *result, const char *source, int source_len,
                    TSNode root, bool js_mode, bool jsx_mode, bool dts_mode) {
    if (!arena || !result || !source || ts_node_is_null(root))
        return;
    ts_type_budget_reset((size_t)source_len);

    // Diagnostic / benchmarking knob: setting `CBM_LSP_DISABLED=1` skips the resolver.
    // This is used by the baseline-vs-LSP comparison tests to measure how many calls
    // the LSP-augmented path adds over plain tree-sitter extraction.
    const char *disabled = getenv("CBM_LSP_DISABLED");
    if (disabled && disabled[0] && disabled[0] != '0')
        return;

    CBMTypeRegistry reg;
    cbm_registry_init(&reg, arena);
    cbm_ts_stdlib_register(&reg, arena);
    const char *module_qn = result->module_qn;
    size_t scope_len = cbm_fqn_js_symbol_scope_len(module_qn);
    if (module_qn && module_qn[scope_len]) {
        module_qn = cbm_arena_strndup(arena, module_qn, scope_len);
        if (!module_qn)
            return;
    }
    register_file_defs(arena, &reg, result, module_qn);

    TSLSPContext ctx;
    ts_lsp_init(&ctx, arena, source, source_len, &reg, module_qn, js_mode, jsx_mode,
                dts_mode, &result->resolved_calls);
    ctx.usages = &result->usages;

    // Add imports early so type-resolution passes can rewrite NAMED references that
    // refer to imported symbols. ts_parse_type_node consults these via
    // resolve_type_with_imports.
    for (int i = 0; i < result->imports.count; i++) {
        const CBMImport *imp = &result->imports.items[i];
        if (imp->local_name && imp->module_path) {
            ts_lsp_add_import(&ctx, imp->local_name, imp->module_path);
        }
    }
    ts_lsp_collect_import_aliases(&ctx, root);
    ts_prepare_module_callables(&ctx, root);

    ast_sweep_shapes(&ctx, root, &reg);
    refine_ast_signatures(&ctx, root, &reg);
    apply_jsdoc_signatures(&ctx, root, &reg);
    infer_implicit_returns(&ctx, root, &reg);

    /* Hash-index the registry before the walk. Unfinalized, each method or
     * type lookup scanned the stdlib and every definition of the file, so a
     * file of n calls and n definitions cost n * n. The index answers each
     * duplicated name with its first registration, as the scan did. The
     * index lives in a scratch arena that dies with this call. */
    CBMArena idx_arena;
    cbm_arena_init(&idx_arena);
    reg.index_first_registered = true;
    cbm_registry_finalize_into(&reg, &idx_arena);
    ts_lsp_process_file(&ctx, root);
    cbm_arena_destroy(&idx_arena);
}

// ── Cross-file entry point (Phase 3) ──────────────────────────────────────────

/* Register a batch of CBMLSPDef[] into a registry. Mirrors the inline
 * loop in cbm_run_ts_lsp_cross — KEEP IN SYNC. Shared by the Tier 2
 * pre-built registry builder + per-file overlay builder. Def-driven
 * (return/field/embedded/method info from def strings). */
static void ts_register_lsp_defs(CBMArena *arena, CBMTypeRegistry *reg, CBMLSPDef *defs,
                                 int def_count) {
    for (int i = 0; i < def_count; i++) {
        const CBMLSPDef *d = &defs[i];
        if (!d->qualified_name || !d->short_name || !d->label)
            continue;

        if (strcmp(d->label, "Module") == 0 && d->alias_target) {
            if (!reg->ts_values)
                reg->ts_values = cbm_scope_push(arena, NULL);
            const char *qn = cbm_arena_sprintf(arena, "%s.default", d->qualified_name);
            cbm_scope_bind(reg->ts_values, qn, cbm_type_named(arena, d->alias_target));
            continue;
        }
        if (strcmp(d->label, "Variable") == 0 ||
            (strcmp(d->label, "Module") == 0 && (d->return_types || d->js_object_literal))) {
            if (!reg->ts_values)
                reg->ts_values = cbm_scope_push(arena, NULL);
            const CBMType *value =
                d->return_types ? parse_ts_type_text(arena, d->return_types, d->def_module_qn)
                                : cbm_type_unknown();
            if (d->js_object_literal) {
                int count = 0;
                while (d->js_object_members && d->js_object_members[count * 2])
                    count++;
                const char **names = cbm_arena_calloc(arena, ((size_t)count + 1) * sizeof(*names));
                const CBMType **types =
                    cbm_arena_calloc(arena, ((size_t)count + 1) * sizeof(*types));
                if (names && types) {
                    for (int j = 0; j < count; j++) {
                        names[j] = d->js_object_members[j * 2];
                        types[j] = cbm_type_named(arena, d->js_object_members[j * 2 + 1]);
                    }
                    value = cbm_type_object_lit(arena, names, types, NULL, NULL);
                } else {
                    value = cbm_type_unknown();
                }
            }
            cbm_scope_bind(reg->ts_values, d->qualified_name, value);
        } else if (strcmp(d->label, "Class") == 0 || strcmp(d->label, "Interface") == 0) {
            CBMRegisteredType rt;
            memset(&rt, 0, sizeof(rt));
            rt.qualified_name = d->qualified_name;
            rt.short_name = d->short_name;
            rt.is_interface = (strcmp(d->label, "Interface") == 0);
            rt.ts_value_binding_written = d->ts_value_binding_written;
            if (d->embedded_types && d->embedded_types[0]) {
                int n = 1;
                for (const char *s = d->embedded_types; *s; s++)
                    if (*s == '|')
                        n++;
                const char **arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                if (arr) {
                    int idx = 0;
                    const char *start = d->embedded_types;
                    for (const char *s = d->embedded_types;; s++) {
                        if (*s == '|' || *s == '\0') {
                            arr[idx++] = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    arr[idx] = NULL;
                    rt.embedded_types = arr;
                }
            }
            if (d->field_defs && d->field_defs[0]) {
                int n = 1;
                for (const char *s = d->field_defs; *s; s++)
                    if (*s == '|')
                        n++;
                const char **fn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                const CBMType **ft_arr = (const CBMType **)cbm_arena_alloc(
                    arena, (size_t)(n + 1) * sizeof(const CBMType *));
                if (fn_arr && ft_arr) {
                    int idx = 0;
                    const char *start = d->field_defs;
                    for (const char *s = d->field_defs;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *pair = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            char *colon = pair ? strchr(pair, ':') : NULL;
                            if (pair && colon) {
                                *colon = '\0';
                                fn_arr[idx] = pair;
                                ft_arr[idx] =
                                    parse_ts_type_text(arena, colon + 1, d->def_module_qn);
                                idx++;
                            }
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    fn_arr[idx] = NULL;
                    ft_arr[idx] = NULL;
                    rt.field_names = fn_arr;
                    rt.field_types = ft_arr;
                }
            }
            cbm_registry_add_type(reg, rt);
            if (d->method_names_str && d->method_names_str[0]) {
                int n = 1;
                for (const char *s = d->method_names_str; *s; s++)
                    if (*s == '|')
                        n++;
                const char **mn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                const char **mqn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                if (mn_arr && mqn_arr) {
                    int idx = 0;
                    const char *start = d->method_names_str;
                    for (const char *s = d->method_names_str;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *m = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            mn_arr[idx] = m;
                            mqn_arr[idx] = cbm_arena_sprintf(arena, "%s.%s", d->qualified_name, m);
                            idx++;
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    mn_arr[idx] = NULL;
                    mqn_arr[idx] = NULL;
                    if (reg->type_count > 0) {
                        CBMRegisteredType *rt_just = &reg->types[reg->type_count - 1];
                        rt_just->method_names = mn_arr;
                        rt_just->method_qns = mqn_arr;
                    }
                }
            }
        } else if (strcmp(d->label, "Function") == 0 || strcmp(d->label, "Method") == 0) {
            CBMRegisteredFunc rf;
            memset(&rf, 0, sizeof(rf));
            rf.qualified_name = d->qualified_name;
            rf.short_name = d->short_name;
            rf.min_params = -1;
            if (d->is_static)
                rf.flags |= CBM_FUNC_FLAG_STATICMETHOD;
            const CBMType **rets = NULL;
            if (d->return_types && d->return_types[0]) {
                int n = 1;
                for (const char *s = d->return_types; *s; s++)
                    if (*s == '|')
                        n++;
                rets = (const CBMType **)cbm_arena_alloc(arena,
                                                         (size_t)(n + 1) * sizeof(const CBMType *));
                if (rets) {
                    int idx = 0;
                    const char *start = d->return_types;
                    for (const char *s = d->return_types;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *part = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            rets[idx++] = parse_ts_type_text(arena, part, d->def_module_qn);
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    rets[idx] = NULL;
                }
            }
            CBMTSLSPSignatureParserContext param_parser_ctx = {d->def_module_qn};
            const CBMType **params = cbm_type_materialize_signature_params(
                arena, d->signature_param_types, d->signature_param_count,
                cbm_ts_lsp_parse_signature_param_text, &param_parser_ctx);
            rf.signature = cbm_type_func(arena, NULL, params, rets);
            if (strcmp(d->label, "Method") == 0 && d->receiver_type) {
                rf.receiver_type = d->receiver_type;
            }
            cbm_registry_add_func(reg, rf);
        }
    }
}

/* Constructor-return facts remain conditional on their class value binding.
 * Recheck after registration so cached factories see changed provider classes.
 * Hash indexes are ready here; never scan all classes for each factory. */
static void ts_prune_written_constructor_facts(CBMArena *arena, CBMTypeRegistry *reg,
                                               CBMLSPDef *defs, int count, const char *module_qn) {
    for (int i = 0; i < count; i++) {
        const CBMLSPDef *d = &defs[i];
        if (!d->ts_return_constructor || !d->qualified_name ||
            (module_qn && (!d->def_module_qn || strcmp(module_qn, d->def_module_qn) != 0)))
            continue;
        bool variable = strcmp(d->label, "Variable") == 0 || strcmp(d->label, "Module") == 0;
        const CBMVarBinding *binding =
            variable ? cbm_scope_lookup_local(reg->ts_values, d->qualified_name) : NULL;
        const CBMRegisteredFunc *f =
            !variable ? cbm_registry_lookup_func(reg, d->qualified_name) : NULL;
        const CBMType *signature = f ? f->signature : NULL;
        const CBMType *value = binding ? binding->type : NULL;
        if (signature && signature->kind == CBM_TYPE_FUNC && signature->data.func.return_types)
            value = signature->data.func.return_types[0];
        bool promise = false;
        if (value && value->kind == CBM_TYPE_TEMPLATE && value->data.template_type.template_name &&
            strcmp(value->data.template_type.template_name, "Promise") == 0 &&
            value->data.template_type.arg_count == 1 && value->data.template_type.template_args) {
            promise = true;
            value = value->data.template_type.template_args[0];
        }
        const CBMRegisteredType *type =
            value && value->kind == CBM_TYPE_NAMED
                ? cbm_registry_lookup_type(reg, value->data.named.qualified_name)
                : NULL;
        if (!type || !type->ts_value_binding_written)
            continue;
        const CBMType *replacement = cbm_type_unknown();
        if (promise) {
            const CBMType *args[] = {replacement, NULL};
            replacement = cbm_type_template(arena, "Promise", args, 1);
        }
        if (variable) {
            cbm_scope_bind(reg->ts_values, d->qualified_name, replacement);
        } else if (signature && signature->kind == CBM_TYPE_FUNC) {
            CBMRegisteredFunc *own = cbm_registry_func_for_update(reg, d->qualified_name);
            const CBMType *rets[] = {replacement, NULL};
            if (own)
                own->signature = cbm_type_func(arena, signature->data.func.param_names,
                                               signature->data.func.param_types, rets);
        }
    }
}

/* Tier 2: build a project-wide TS/JS/TSX registry ONCE from all defs
 * (filters by lang). Shared READ-ONLY *base* across resolve workers.
 * Per-file overlays (built by cbm_run_ts_lsp_cross_with_registry)
 * chain to this via the registry fallback pointer. */
CBMTypeRegistry *cbm_ts_build_cross_registry(CBMArena *arena, CBMLSPDef *defs, int def_count) {
    if (!arena)
        return NULL;
    CBMTypeRegistry *reg = (CBMTypeRegistry *)cbm_arena_alloc(arena, sizeof(*reg));
    if (!reg)
        return NULL;
    cbm_registry_init(reg, arena);
    cbm_ts_stdlib_register(reg, arena);
    /* Budget scales with the def volume this build parses type texts for. */
    ts_type_budget_reset((size_t)(def_count > 0 ? def_count : 1) * 1024);
    for (int i = 0; i < def_count; i++) {
        CBMLSPDef *d = &defs[i];
        if (d->lang != CBM_LANG_JAVASCRIPT && d->lang != CBM_LANG_TYPESCRIPT &&
            d->lang != CBM_LANG_TSX) {
            continue;
        }
        ts_register_lsp_defs(arena, reg, d, 1);
    }
    cbm_registry_finalize(reg);
    ts_prune_written_constructor_facts(arena, reg, defs, def_count, NULL);
    reg->read_only = true; /* seal: shared Tier-2 registry is read-only during resolve */
    return reg;
}

/* Tier 2 per-file resolve. Builds a SMALL per-file overlay registry P
 * containing only this file's own-module defs (so the AST refinement
 * passes — which mutate type shapes/aliases of locally-declared types
 * — operate on P, not the shared base). P chains to the shared base
 * `reg` for cross-file + stdlib lookups. This preserves the per-file
 * AST refinement quality while avoiding re-registering imported
 * modules' defs in every file. */
void cbm_run_ts_lsp_cross_with_registry(CBMArena *arena, const char *source, int source_len,
                                        const char *module_qn, bool js_mode, bool jsx_mode,
                                        bool dts_mode, CBMTypeRegistry *reg, CBMLSPDef *defs,
                                        int def_count, const char **import_names,
                                        const char **import_qns, int import_count,
                                        TSTree *cached_tree, CBMResolvedCallArray *out) {
    if (!arena || !out || !reg)
        return;

    ts_type_budget_reset((size_t)source_len);

    /* Per-file overlay: register only the file's own-module defs so the
     * AST passes can refine them. Imports/stdlib resolve via fallback. */
    CBMTypeRegistry overlay;
    cbm_registry_init(&overlay, arena);
    overlay.fallback = reg;
    for (int i = 0; i < def_count; i++) {
        CBMLSPDef *d = &defs[i];
        const char *dm = d->def_module_qn ? d->def_module_qn : "";
        if (module_qn && strcmp(dm, module_qn) == 0) {
            ts_register_lsp_defs(arena, &overlay, d, 1);
        }
    }

    TSTree *tree = cached_tree;
    bool owns_tree = false;
    if (!tree) {
        if (!source || source_len <= 0)
            return;
        TSParser *parser = ts_parser_new();
        if (!parser)
            return;
        const TSLanguage *lang =
            jsx_mode ? (js_mode ? tree_sitter_javascript() : tree_sitter_tsx())
                     : (js_mode ? tree_sitter_javascript() : tree_sitter_typescript());
        ts_parser_set_language(parser, lang);
        tree = cbm_parse_source(parser, source, (uint32_t)source_len, (TSParseOptions){0});
        ts_parser_delete(parser);
        if (!tree)
            return;
        owns_tree = true;
    }
    TSNode root = ts_tree_root_node(tree);
    if (ts_node_is_null(root)) {
        if (owns_tree)
            ts_tree_delete(tree);
        return;
    }

    cbm_registry_finalize(&overlay);
    ts_prune_written_constructor_facts(arena, &overlay, defs, def_count, module_qn);

    TSLSPContext ctx;
    ts_lsp_init(&ctx, arena, source, source_len, &overlay, module_qn, js_mode, jsx_mode, dts_mode,
                out);
    ctx.cross_file_mode = true;
    for (int i = 0; i < import_count; i++) {
        if (import_names && import_qns && import_names[i] && import_qns[i]) {
            ts_lsp_add_import(&ctx, import_names[i], import_qns[i]);
        }
    }
    ts_lsp_collect_import_aliases(&ctx, root);
    ts_prepare_module_callables(&ctx, root);

    ast_sweep_shapes(&ctx, root, &overlay);
    refine_ast_signatures(&ctx, root, &overlay);
    apply_jsdoc_signatures(&ctx, root, &overlay);
    infer_implicit_returns(&ctx, root, &overlay);

    ts_lsp_process_file(&ctx, root);

    if (owns_tree)
        ts_tree_delete(tree);
}

void cbm_run_ts_lsp_cross(CBMArena *arena, const char *source, int source_len,
                          const char *module_qn, bool js_mode, bool jsx_mode, bool dts_mode,
                          CBMLSPDef *defs, int def_count, const char **import_names,
                          const char **import_qns, int import_count, TSTree *cached_tree,
                          CBMResolvedCallArray *out) {
    if (!arena || !out)
        return;

    atomic_fetch_add(&g_ts_full_reg_builds, 1);
    ts_type_budget_reset((size_t)source_len);
    CBMTypeRegistry reg;
    cbm_registry_init(&reg, arena);
    cbm_ts_stdlib_register(&reg, arena);

    // Register cross-file defs.
    for (int i = 0; i < def_count; i++) {
        const CBMLSPDef *d = &defs[i];
        if (!d->qualified_name || !d->short_name || !d->label)
            continue;

        if (strcmp(d->label, "Variable") == 0 ||
            (strcmp(d->label, "Module") == 0 &&
             (d->return_types || d->js_object_literal || d->alias_target))) {
            ts_register_lsp_defs(arena, &reg, &defs[i], 1);
            continue;
        }

        if (strcmp(d->label, "Class") == 0 || strcmp(d->label, "Interface") == 0) {
            CBMRegisteredType rt;
            memset(&rt, 0, sizeof(rt));
            rt.qualified_name = d->qualified_name;
            rt.short_name = d->short_name;
            rt.is_interface = (strcmp(d->label, "Interface") == 0);
            rt.ts_value_binding_written = d->ts_value_binding_written;
            // Embedded types (extends list) — pipe-separated.
            if (d->embedded_types && d->embedded_types[0]) {
                int n = 1;
                for (const char *s = d->embedded_types; *s; s++)
                    if (*s == '|')
                        n++;
                const char **arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                if (arr) {
                    int idx = 0;
                    const char *start = d->embedded_types;
                    for (const char *s = d->embedded_types;; s++) {
                        if (*s == '|' || *s == '\0') {
                            arr[idx++] = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    arr[idx] = NULL;
                    rt.embedded_types = arr;
                }
            }
            // Field defs (interface members, "name:type|name:type").
            if (d->field_defs && d->field_defs[0]) {
                int n = 1;
                for (const char *s = d->field_defs; *s; s++)
                    if (*s == '|')
                        n++;
                const char **fn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                const CBMType **ft_arr = (const CBMType **)cbm_arena_alloc(
                    arena, (size_t)(n + 1) * sizeof(const CBMType *));
                if (fn_arr && ft_arr) {
                    int idx = 0;
                    const char *start = d->field_defs;
                    for (const char *s = d->field_defs;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *pair = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            char *colon = pair ? strchr(pair, ':') : NULL;
                            if (pair && colon) {
                                *colon = '\0';
                                fn_arr[idx] = pair;
                                ft_arr[idx] =
                                    parse_ts_type_text(arena, colon + 1, d->def_module_qn);
                                idx++;
                            }
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    fn_arr[idx] = NULL;
                    ft_arr[idx] = NULL;
                    rt.field_names = fn_arr;
                    rt.field_types = ft_arr;
                }
            }
            cbm_registry_add_type(&reg, rt);
            // Method names from method_names_str.
            if (d->method_names_str && d->method_names_str[0]) {
                int n = 1;
                for (const char *s = d->method_names_str; *s; s++)
                    if (*s == '|')
                        n++;
                const char **mn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                const char **mqn_arr =
                    (const char **)cbm_arena_alloc(arena, (size_t)(n + 1) * sizeof(const char *));
                if (mn_arr && mqn_arr) {
                    int idx = 0;
                    const char *start = d->method_names_str;
                    for (const char *s = d->method_names_str;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *m = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            mn_arr[idx] = m;
                            mqn_arr[idx] = cbm_arena_sprintf(arena, "%s.%s", d->qualified_name, m);
                            idx++;
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    mn_arr[idx] = NULL;
                    mqn_arr[idx] = NULL;
                    // Find the type we just inserted and attach.
                    if (reg.type_count > 0) {
                        CBMRegisteredType *rt_just = &reg.types[reg.type_count - 1];
                        rt_just->method_names = mn_arr;
                        rt_just->method_qns = mqn_arr;
                    }
                }
            }
        } else if (strcmp(d->label, "Function") == 0 || strcmp(d->label, "Method") == 0) {
            CBMRegisteredFunc rf;
            memset(&rf, 0, sizeof(rf));
            rf.qualified_name = d->qualified_name;
            rf.short_name = d->short_name;
            rf.min_params = -1;
            if (d->is_static)
                rf.flags |= CBM_FUNC_FLAG_STATICMETHOD;
            // Return types from pipe-separated return_types text.
            const CBMType **rets = NULL;
            if (d->return_types && d->return_types[0]) {
                int n = 1;
                for (const char *s = d->return_types; *s; s++)
                    if (*s == '|')
                        n++;
                rets = (const CBMType **)cbm_arena_alloc(arena,
                                                         (size_t)(n + 1) * sizeof(const CBMType *));
                if (rets) {
                    int idx = 0;
                    const char *start = d->return_types;
                    for (const char *s = d->return_types;; s++) {
                        if (*s == '|' || *s == '\0') {
                            char *part = cbm_arena_strndup(arena, start, (size_t)(s - start));
                            rets[idx++] = parse_ts_type_text(arena, part, d->def_module_qn);
                            if (*s == '\0')
                                break;
                            start = s + 1;
                        }
                    }
                    rets[idx] = NULL;
                }
            }
            CBMTSLSPSignatureParserContext param_parser_ctx = {d->def_module_qn};
            const CBMType **params = cbm_type_materialize_signature_params(
                arena, d->signature_param_types, d->signature_param_count,
                cbm_ts_lsp_parse_signature_param_text, &param_parser_ctx);
            rf.signature = cbm_type_func(arena, NULL, params, rets);
            if (strcmp(d->label, "Method") == 0 && d->receiver_type) {
                rf.receiver_type = d->receiver_type;
            }
            cbm_registry_add_func(&reg, rf);
        }
    }

    // Use cached tree if available; otherwise parse internally and own it.
    TSTree *tree = cached_tree;
    bool owns_tree = false;
    if (!tree) {
        if (!source || source_len <= 0)
            return;
        TSParser *parser = ts_parser_new();
        if (!parser)
            return;
        const TSLanguage *lang =
            jsx_mode ? (js_mode ? tree_sitter_javascript() : tree_sitter_tsx())
                     : (js_mode ? tree_sitter_javascript() : tree_sitter_typescript());
        ts_parser_set_language(parser, lang);
        tree = cbm_parse_source(parser, source, (uint32_t)source_len, (TSParseOptions){0});
        ts_parser_delete(parser);
        if (!tree)
            return;
        owns_tree = true;
    }
    TSNode root = ts_tree_root_node(tree);
    if (ts_node_is_null(root)) {
        if (owns_tree)
            ts_tree_delete(tree);
        return;
    }

    // Build a faux CBMFileResult so register_file_defs's downstream paths work; we don't
    // need it here because cross-file defs already came in as CBMLSPDef.
    // Finalize registry — O(1) lookups. See go_lsp.c "3c. Finalize"
    // comment for the rationale.
    cbm_registry_finalize(&reg);
    ts_prune_written_constructor_facts(arena, &reg, defs, def_count, NULL);

    TSLSPContext ctx;
    ts_lsp_init(&ctx, arena, source, source_len, &reg, module_qn, js_mode, jsx_mode, dts_mode, out);
    ctx.cross_file_mode = true;

    // Add imports early so type passes can resolve imported types.
    for (int i = 0; i < import_count; i++) {
        if (import_names && import_qns && import_names[i] && import_qns[i]) {
            ts_lsp_add_import(&ctx, import_names[i], import_qns[i]);
        }
    }
    ts_lsp_collect_import_aliases(&ctx, root);
    ts_prepare_module_callables(&ctx, root);

    ast_sweep_shapes(&ctx, root, &reg);
    refine_ast_signatures(&ctx, root, &reg);
    apply_jsdoc_signatures(&ctx, root, &reg);
    infer_implicit_returns(&ctx, root, &reg);

    ts_lsp_process_file(&ctx, root);

    if (owns_tree)
        ts_tree_delete(tree);
}

// ── Batch cross-file (Phase 3) ────────────────────────────────────────────────

void cbm_batch_ts_lsp_cross(CBMArena *arena, CBMBatchTSLSPFile *files, int file_count,
                            CBMResolvedCallArray *out) {
    if (!arena || !files || !out || file_count <= 0)
        return;
    // Project-scope merging happens implicitly: every file's CBMLSPDef set already
    // includes both same-file and cross-file defs (built by the caller). The plan §17
    // finding #4 fix ensures the *caller* (pass_calls.c) merges interface declarations
    // by QN before passing them in.
    for (int i = 0; i < file_count; i++) {
        CBMBatchTSLSPFile *f = &files[i];
        cbm_run_ts_lsp_cross(arena, f->source, f->source_len, f->module_qn, f->js_mode, f->jsx_mode,
                             f->dts_mode, f->defs, f->def_count, f->import_names, f->import_qns,
                             f->import_count, f->cached_tree, &out[i]);
    }
}
