/*
 * callable_overload.c — see callable_overload.h.
 */
#include "callable_overload.h"
#include "callable_sig.h"
#include "helpers.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum {
    OVL_SHAPE_CAP = 1024, /* bytes of one rendered shape; longer => unknown */
    OVL_MAX_ENTRIES = 64, /* entries the matcher compares; more => accept */
    OVL_PAIR = 2,         /* extra_props entries per key/value pair */
    OVL_GROUP_MAX = 256,  /* members of one group that get their own node */
};

/* The "unknown" shape: accepted by every match. */
static const char OVL_UNKNOWN[] = "?";

bool cbm_overload_lang(CBMLanguage lang) {
    return lang == CBM_LANG_JAVA || lang == CBM_LANG_KOTLIN;
}

/* ── Shape buffer ──────────────────────────────────────────────── */

typedef struct {
    char buf[OVL_SHAPE_CAP];
    size_t len;
    int entries;
    bool overflow;
} ovl_shape_t;

static void shape_raw(ovl_shape_t *s, const char *text, size_t n) {
    if (s->overflow || s->len + n + 1 > sizeof(s->buf)) {
        s->overflow = true;
        return;
    }
    memcpy(s->buf + s->len, text, n);
    s->len += n;
    s->buf[s->len] = '\0';
}

/* Open an entry: the separator, then the label ("_" when none). A Swift label
 * written in backticks (`default`) is the bare identifier. */
static void shape_entry(ovl_shape_t *s, const char *label, size_t n) {
    if (s->entries > 0) {
        shape_raw(s, ",", 1);
    }
    s->entries++;
    while (n > 0 && label[0] == '`') {
        label++;
        n--;
    }
    while (n > 0 && label[n - 1] == '`') {
        n--;
    }
    if (!label || n == 0) {
        shape_raw(s, "_", 1);
        return;
    }
    for (size_t i = 0; i < n; i++) {
        char ch = label[i];
        /* The grammar's separators never appear in a label; refuse rather
         * than mint an ambiguous shape. */
        if (ch == ',' || ch == '=' || ch == '~' || ch == '*' || ch == '"' || ch == '\\' ||
            (unsigned char)ch < ' ') {
            s->overflow = true;
            return;
        }
    }
    shape_raw(s, label, n);
}

static void shape_node_entry(ovl_shape_t *s, TSNode n, const char *source) {
    if (ts_node_is_null(n)) {
        shape_entry(s, NULL, 0);
        return;
    }
    uint32_t b = ts_node_start_byte(n);
    shape_entry(s, source + b, ts_node_end_byte(n) - b);
}

static const char *shape_done(CBMArena *a, const ovl_shape_t *s) {
    if (s->overflow) {
        return NULL;
    }
    return cbm_arena_strndup(a, s->buf, s->len);
}

static bool node_text_is(TSNode n, const char *source, const char *text) {
    uint32_t b = ts_node_start_byte(n);
    uint32_t e = ts_node_end_byte(n);
    size_t len = strlen(text);
    return e - b == len && memcmp(source + b, text, len) == 0;
}

static bool kind_is(TSNode n, const char *kind) {
    return strcmp(ts_node_type(n), kind) == 0;
}

static bool kind_is_comment(TSNode n) {
    const char *k = ts_node_type(n);
    return strcmp(k, "comment") == 0 || strcmp(k, "line_comment") == 0 ||
           strcmp(k, "block_comment") == 0 || strcmp(k, "multiline_comment") == 0;
}

/* ── Parameter shapes ──────────────────────────────────────────── */

static void java_params_shape(ovl_shape_t *s, TSNode func) {
    TSNode params = ts_node_child_by_field_name(func, "parameters", (uint32_t)strlen("parameters"));
    uint32_t count = ts_node_is_null(params) ? 0 : ts_node_named_child_count(params);
    for (uint32_t i = 0; i < count; i++) {
        TSNode p = ts_node_named_child(params, i);
        if (kind_is(p, "formal_parameter")) {
            shape_entry(s, NULL, 0);
        } else if (kind_is(p, "spread_parameter")) {
            shape_entry(s, NULL, 0);
            shape_raw(s, "~", 1);
        }
        /* receiver_parameter (`Foo this`) and comments are no parameters. */
    }
}

static bool kotlin_modifiers_vararg(TSNode mods, const char *source) {
    uint32_t count = ts_node_named_child_count(mods);
    for (uint32_t i = 0; i < count; i++) {
        TSNode m = ts_node_named_child(mods, i);
        if (kind_is(m, "parameter_modifier") && node_text_is(m, source, "vararg")) {
            return true;
        }
    }
    return false;
}

static void kotlin_params_shape(ovl_shape_t *s, TSNode func, const char *source) {
    TSNode params = cbm_find_child_by_kind(func, "function_value_parameters");
    uint32_t count = ts_node_is_null(params) ? 0 : ts_node_child_count(params);
    bool vararg = false;
    bool open = false; /* an entry was written and may still take '=' */
    for (uint32_t i = 0; i < count; i++) {
        TSNode ch = ts_node_child(params, i);
        if (kind_is(ch, "parameter_modifiers")) {
            vararg = vararg || kotlin_modifiers_vararg(ch, source);
        } else if (kind_is(ch, "parameter")) {
            /* The parameter name: a named argument binds by it. */
            shape_node_entry(s, cbm_find_child_by_kind(ch, "simple_identifier"), source);
            if (vararg) {
                shape_raw(s, "~", 1);
            }
            vararg = false;
            open = true;
        } else if (!ts_node_is_named(ch) && node_text_is(ch, source, "=") && open) {
            shape_raw(s, "=", 1); /* `b: String = "x"`: the default follows its parameter */
            open = false;
        } else if (!ts_node_is_named(ch) && node_text_is(ch, source, ",")) {
            open = false;
        }
    }
}

static const char *params_shape(CBMArena *a, TSNode func, const char *source, CBMLanguage lang) {
    ovl_shape_t s;
    memset(&s, 0, sizeof(s));
    switch (lang) {
    case CBM_LANG_JAVA:
        java_params_shape(&s, func);
        break;
    case CBM_LANG_KOTLIN:
        kotlin_params_shape(&s, func, source);
        break;
    default:
        return NULL;
    }
    return shape_done(a, &s);
}

void cbm_overload_describe_def(CBMArena *a, CBMDefinition *def, TSNode func_node,
                               const char *source, CBMLanguage lang) {
    if (!a || !def || !source || ts_node_is_null(func_node) || !cbm_overload_lang(lang) ||
        !def->label || (strcmp(def->label, "Function") != 0 && strcmp(def->label, "Method") != 0)) {
        return;
    }
    CBMCallableIdentity mode = CBM_CALLABLE_ID_TYPED;
    def->callable_sig = cbm_callable_sig_mode(a, func_node, source, lang, mode);
    def->callable_params = params_shape(a, func_node, source, lang);
}

/* ── Argument shapes ───────────────────────────────────────────── */

static void java_args_shape(ovl_shape_t *s, TSNode call) {
    TSNode args = ts_node_child_by_field_name(call, "arguments", (uint32_t)strlen("arguments"));
    uint32_t count = ts_node_is_null(args) ? 0 : ts_node_named_child_count(args);
    for (uint32_t i = 0; i < count; i++) {
        if (!kind_is_comment(ts_node_named_child(args, i))) {
            shape_entry(s, NULL, 0);
        }
    }
}

/* Kotlin: call_suffix holds the arguments and an optional trailing lambda. */
static void suffix_args_shape(ovl_shape_t *s, TSNode suffix, const char *source) {
    uint32_t count = ts_node_named_child_count(suffix);
    for (uint32_t i = 0; i < count; i++) {
        TSNode ch = ts_node_named_child(suffix, i);
        if (kind_is(ch, "value_arguments")) {
            uint32_t ac = ts_node_named_child_count(ch);
            for (uint32_t j = 0; j < ac; j++) {
                TSNode arg = ts_node_named_child(ch, j);
                if (!kind_is(arg, "value_argument")) {
                    continue;
                }
                TSNode label = {0};
                if (ts_node_child_count(arg) >= 3 &&
                           kind_is(ts_node_child(arg, 0), "simple_identifier") &&
                           node_text_is(ts_node_child(arg, 1), source, "=")) {
                    label = ts_node_child(arg, 0); /* Kotlin named argument `name = value` */
                }
                shape_node_entry(s, label, source);
            }
        } else if (kind_is(ch, "annotated_lambda") || kind_is(ch, "lambda_literal")) {
            if (s->entries > 0) {
                shape_raw(s, ",", 1);
            }
            s->entries++;
            shape_raw(s, "*", 1);
        }
    }
}

const char *cbm_call_args_shape(CBMArena *a, TSNode call_node, const char *source,
                                CBMLanguage lang) {
    if (!a || !source || ts_node_is_null(call_node) || !cbm_overload_lang(lang)) {
        return NULL;
    }
    ovl_shape_t s;
    memset(&s, 0, sizeof(s));
    if (lang == CBM_LANG_JAVA) {
        if (!kind_is(call_node, "method_invocation")) {
            return NULL;
        }
        java_args_shape(&s, call_node);
        return shape_done(a, &s);
    }
    if (!kind_is(call_node, "call_expression")) {
        return NULL;
    }
    TSNode suffix = cbm_find_child_by_kind(call_node, "call_suffix");
    if (ts_node_is_null(suffix)) {
        return NULL;
    }
    suffix_args_shape(&s, suffix, source);
    return shape_done(a, &s);
}

/* ── Matching ──────────────────────────────────────────────────── */

typedef struct {
    const char *label;
    size_t label_len;
    bool has_default;
    bool variadic;
    bool trailing; /* argument side: a trailing closure */
} ovl_entry_t;

/* Split a shape into entries; -1 when it has more than `cap`. */
static int shape_parse(const char *shape, ovl_entry_t *out, int cap) {
    if (!shape[0]) {
        return 0;
    }
    int n = 0;
    const char *p = shape;
    while (true) {
        const char *end = strchr(p, ',');
        size_t len = end ? (size_t)(end - p) : strlen(p);
        if (n >= cap) {
            return -1;
        }
        ovl_entry_t *e = &out[n++];
        memset(e, 0, sizeof(*e));
        while (len > 0 && (p[len - 1] == '=' || p[len - 1] == '~')) {
            if (p[len - 1] == '=') {
                e->has_default = true;
            } else {
                e->variadic = true;
            }
            len--;
        }
        e->trailing = len == 1 && p[0] == '*';
        e->label = p;
        e->label_len = len;
        if (!end) {
            break;
        }
        p = end + 1;
    }
    return n;
}

static bool label_eq(const ovl_entry_t *x, const ovl_entry_t *y) {
    return x->label_len == y->label_len && memcmp(x->label, y->label, x->label_len) == 0;
}

static bool unlabeled(const ovl_entry_t *e) {
    return e->label_len == 1 && e->label[0] == '_';
}

/* Kotlin: positional arguments fill the parameters in order (a vararg takes
 * every positional argument after it), a named argument fills the parameter
 * of that name, a trailing lambda fills the last parameter; every parameter
 * without a default or vararg must be filled, and nothing twice. */
static bool kotlin_matches(const ovl_entry_t *params, int np, const ovl_entry_t *args, int na) {
    bool filled[OVL_MAX_ENTRIES] = {false};
    int next = 0;
    for (int j = 0; j < na; j++) {
        const ovl_entry_t *a = &args[j];
        int target = -1;
        if (a->trailing) {
            target = np - 1;
        } else if (!unlabeled(a)) {
            for (int i = 0; i < np && target < 0; i++) {
                if (label_eq(&params[i], a)) {
                    target = i;
                }
            }
        } else {
            while (next < np && filled[next] && !params[next].variadic) {
                next++;
            }
            target = next < np ? next : -1;
            if (target >= 0 && !params[target].variadic) {
                next++;
            }
        }
        if (target < 0 || (filled[target] && !params[target].variadic)) {
            return false;
        }
        filled[target] = true;
    }
    for (int i = 0; i < np; i++) {
        if (!filled[i] && !params[i].has_default && !params[i].variadic) {
            return false;
        }
    }
    return true;
}

bool cbm_callable_shape_matches(const char *params, const char *args, CBMLanguage lang) {
    if (!params || !args || strcmp(params, OVL_UNKNOWN) == 0 || strcmp(args, OVL_UNKNOWN) == 0) {
        return true;
    }
    ovl_entry_t pe[OVL_MAX_ENTRIES];
    ovl_entry_t ae[OVL_MAX_ENTRIES];
    int np = shape_parse(params, pe, OVL_MAX_ENTRIES);
    int na = shape_parse(args, ae, OVL_MAX_ENTRIES);
    if (np < 0 || na < 0) {
        return true;
    }
    if (lang == CBM_LANG_KOTLIN) {
        return kotlin_matches(pe, np, ae, na);
    }
    int required = 0;
    bool variadic = false;
    for (int i = 0; i < np; i++) {
        if (pe[i].variadic) {
            variadic = true;
        } else if (!pe[i].has_default) {
            required++;
        }
    }
    return na >= required && (variadic || na <= np);
}

/* ── Splitting a file's groups ─────────────────────────────────── */

typedef struct {
    const CBMDefinition *def;
    int index; /* into result->defs */
} ovl_ref_t;

static bool split_candidate(const CBMDefinition *d) {
    return d->qualified_name && d->name && d->label && d->callable_sig && !d->qn_sig_off &&
           (strcmp(d->label, "Function") == 0 || strcmp(d->label, "Method") == 0);
}

static int split_cmp(const void *pa, const void *pb) {
    const ovl_ref_t *ra = (const ovl_ref_t *)pa;
    const ovl_ref_t *rb = (const ovl_ref_t *)pb;
    const CBMDefinition *x = ra->def;
    const CBMDefinition *y = rb->def;
    int c = strcmp(x->qualified_name, y->qualified_name);
    if (c == 0) {
        c = strcmp(x->label, y->label);
    }
    if (c == 0 && x->start_line != y->start_line) {
        c = x->start_line < y->start_line ? -1 : 1;
    }
    if (c == 0) {
        c = (ra->index > rb->index) - (ra->index < rb->index);
    }
    return c;
}

static bool same_group(const CBMDefinition *x, const CBMDefinition *y) {
    return strcmp(x->qualified_name, y->qualified_name) == 0 && strcmp(x->label, y->label) == 0;
}

/* Append key=value to a def's NULL-terminated extra_props list. */
static void add_extra_prop(CBMArena *a, CBMDefinition *d, const char *key, const char *value) {
    int n = 0;
    while (d->extra_props && d->extra_props[n]) {
        n++;
    }
    const char **list = cbm_arena_alloc(a, (size_t)(n + OVL_PAIR + 1) * sizeof(*list));
    if (!list) {
        return;
    }
    for (int i = 0; i < n; i++) {
        list[i] = d->extra_props[i];
    }
    list[n] = key;
    list[n + 1] = value;
    list[n + OVL_PAIR] = NULL;
    d->extra_props = list;
}

static void split_group(CBMArena *a, CBMFileResult *result, const ovl_ref_t *ref, int n) {
    CBMDefinition *defs = result->defs.items;
    int idx[OVL_GROUP_MAX];
    if (n > OVL_GROUP_MAX) {
        n = OVL_GROUP_MAX; /* a later member past the cap keeps the base QN */
    }
    for (int k = 0; k < n; k++) {
        idx[k] = ref[k].index;
    }
    bool distinct = false;
    for (int k = 1; k < n && !distinct; k++) {
        distinct = strcmp(defs[idx[k]].callable_sig, defs[idx[0]].callable_sig) != 0;
    }
    if (!distinct) {
        return; /* one signature written twice: variants of one definition */
    }
    const char *base = defs[idx[0]].qualified_name;
    size_t base_len = strlen(base);
    for (int k = 0; k < n; k++) {
        CBMDefinition *d = &defs[idx[k]];
        const char *params = !d->callable_params     ? OVL_UNKNOWN
                             : d->callable_params[0] ? d->callable_params
                                                     : CBM_OVERLOAD_NO_PARAMS;
        add_extra_prop(a, d, CBM_OVERLOAD_PARAMS_PROP, params);
        if (k == 0) {
            continue;
        }
        const CBMDefinition *same = NULL;
        for (int m = 0; m < k && !same; m++) {
            if (strcmp(defs[idx[m]].callable_sig, d->callable_sig) == 0) {
                same = &defs[idx[m]];
            }
        }
        if (same) {
            d->qualified_name = same->qualified_name;
            d->qn_sig_off = same->qn_sig_off;
            continue;
        }
        char *qn = cbm_arena_sprintf(a, "%s%s", base, d->callable_sig);
        if (!qn || cbm_qn_callable_base_len_named(qn, d->name) != base_len) {
            continue; /* never mint a QN the leaf splitters would misread */
        }
        d->qualified_name = qn;
        d->qn_sig_off = (uint32_t)base_len;
    }
}

void cbm_split_overloads(CBMArena *a, CBMFileResult *result, CBMLanguage lang) {
    if (!a || !result || !cbm_overload_lang(lang) || result->defs.count < 2) {
        return;
    }
    int count = result->defs.count;
    ovl_ref_t *refs = malloc((size_t)count * sizeof(*refs));
    if (!refs) {
        return;
    }
    int n = 0;
    for (int i = 0; i < count; i++) {
        if (split_candidate(&result->defs.items[i])) {
            refs[n].def = &result->defs.items[i];
            refs[n].index = i;
            n++;
        }
    }
    qsort(refs, (size_t)n, sizeof(*refs), split_cmp);
    for (int start = 0; start < n;) {
        int end = start + 1;
        while (end < n && same_group(refs[start].def, refs[end].def)) {
            end++;
        }
        if (end - start > 1) {
            split_group(a, result, refs + start, end - start);
        }
        start = end;
    }
    free(refs);
}
