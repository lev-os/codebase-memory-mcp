/*
 * call_overloads.c — bind a call that lands on a same-file overload group to
 * the members its argument shape fits (internal/cbm/callable_overload.h).
 *
 * The registry and the language resolvers keep answering with the group's
 * base QN, exactly as before the split (members 2..n are registered by QN
 * only), so every strategy and candidate count is unchanged. This step runs
 * once the target node is final, in both resolvers.
 */
#include "pipeline/pipeline_internal.h"
#include "callable_overload.h"
#include "callable_sig.h"

#include <stdlib.h>
#include <string.h>

enum { OVL_PROP_MAX = 1024 };

static const char OVL_PROP_KEY[] = "\"" CBM_OVERLOAD_PARAMS_PROP "\":\"";

/* The node's `overload_params` value copied into buf, or NULL when absent.
 * Shapes never hold '"' or '\\' (callable_overload.c), so no unescaping. */
static const char *ovl_node_params(const cbm_gbuf_node_t *node, char *buf, size_t cap) {
    const char *props = node ? node->properties_json : NULL;
    const char *at = props ? strstr(props, OVL_PROP_KEY) : NULL;
    if (!at) {
        return NULL;
    }
    at += sizeof(OVL_PROP_KEY) - 1;
    const char *end = strchr(at, '"');
    if (!end || (size_t)(end - at) >= cap) {
        return NULL;
    }
    memcpy(buf, at, (size_t)(end - at));
    buf[end - at] = '\0';
    if (strcmp(buf, CBM_OVERLOAD_NO_PARAMS) == 0) {
        buf[0] = '\0';
    }
    return buf;
}

bool cbm_node_is_split_overload(const char *qualified_name, const char *name,
                                const char *properties_json) {
    return qualified_name && name && properties_json &&
           strstr(properties_json, OVL_PROP_KEY) != NULL &&
           cbm_qn_callable_base_len_named(qualified_name, name) < strlen(qualified_name);
}

static size_t ovl_base_len(const cbm_gbuf_node_t *n) {
    return cbm_qn_callable_base_len_named(n->qualified_name, n->name);
}

static bool ovl_same_group(const cbm_gbuf_node_t *target, size_t base_len,
                           const cbm_gbuf_node_t *n) {
    return n->label && target->label && strcmp(n->label, target->label) == 0 && n->file_path &&
           target->file_path && strcmp(n->file_path, target->file_path) == 0 &&
           ovl_base_len(n) == base_len &&
           strncmp(n->qualified_name, target->qualified_name, base_len) == 0;
}

static int ovl_node_cmp(const void *pa, const void *pb) {
    const cbm_gbuf_node_t *x = *(const cbm_gbuf_node_t *const *)pa;
    const cbm_gbuf_node_t *y = *(const cbm_gbuf_node_t *const *)pb;
    if (x->start_line != y->start_line) {
        return x->start_line < y->start_line ? -1 : 1;
    }
    return strcmp(x->qualified_name, y->qualified_name);
}

int cbm_pipeline_overload_targets(const cbm_gbuf_t *gb, const cbm_gbuf_node_t *target,
                                  const CBMCall *call, CBMLanguage lang,
                                  const cbm_gbuf_node_t **out, int cap) {
    char params[OVL_PROP_MAX];
    if (!gb || !target || !call || !out || cap < 1 || !cbm_overload_lang(lang) || !target->name ||
        !target->qualified_name || !ovl_node_params(target, params, sizeof(params))) {
        return 0;
    }
    const cbm_gbuf_node_t **same = NULL;
    int same_count = 0;
    if (cbm_gbuf_find_by_name(gb, target->name, (const cbm_gbuf_node_t ***)&same, &same_count) !=
            0 ||
        same_count < 1) {
        return 0;
    }
    size_t base_len = ovl_base_len(target);
    const cbm_gbuf_node_t **group = malloc((size_t)same_count * sizeof(*group));
    if (!group) {
        return 0;
    }
    int members = 0;
    for (int i = 0; i < same_count; i++) {
        const cbm_gbuf_node_t *n = same[i];
        /* The name index may still list a node an incremental run replaced. */
        if (n && n->qualified_name && ovl_same_group(target, base_len, n) &&
            cbm_gbuf_find_by_qn(gb, n->qualified_name) == n &&
            ovl_node_params(n, params, sizeof(params))) {
            group[members++] = n;
        }
    }
    if (members < 2) {
        free(group);
        return 0;
    }
    qsort(group, (size_t)members, sizeof(*group), ovl_node_cmp);
    /* The members whose parameter shape accepts the call's arguments. */
    int fit = 0;
    bool target_fits = false;
    for (int i = 0; i < members; i++) {
        const char *p = ovl_node_params(group[i], params, sizeof(params));
        if (cbm_callable_shape_matches(p, call->arg_shape, lang)) {
            group[fit++] = group[i];
            target_fits = target_fits || group[i] == target;
        }
    }
    int n = 0;
    if (fit == 1) {
        out[n++] = group[0];
    } else if (fit > 1 && target_fits && ovl_base_len(target) < strlen(target->qualified_name)) {
        /* A resolver that named one later member (a suffixed QN) chose it. */
        out[n++] = target;
    } else {
        /* Several fit, or none does (an argument the shape cannot count):
         * every candidate, never one picked silently. */
        if (fit == 0) {
            int all = 0;
            for (int i = 0; i < same_count; i++) {
                const cbm_gbuf_node_t *m = same[i];
                if (m && m->qualified_name && ovl_same_group(target, base_len, m) &&
                    cbm_gbuf_find_by_qn(gb, m->qualified_name) == m &&
                    ovl_node_params(m, params, sizeof(params))) {
                    group[all++] = m;
                }
            }
            qsort(group, (size_t)all, sizeof(*group), ovl_node_cmp);
            fit = all;
        }
        for (int i = 0; i < fit && n < cap; i++) {
            out[n++] = group[i];
        }
    }
    free(group);
    return n;
}
