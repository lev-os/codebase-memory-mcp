/* Shared ECMAScript declaration scope rules for identity and call extraction. */
#ifndef CBM_JS_SCOPE_H
#define CBM_JS_SCOPE_H
#include "tree_sitter/api.h"
#include <stdbool.h>
#include <string.h>

static inline bool cbm_js_bodied_kind(const char *kind) {
    return strcmp(kind, "function_declaration") == 0 ||
           strcmp(kind, "generator_function_declaration") == 0 ||
           strcmp(kind, "function_expression") == 0 || strcmp(kind, "function") == 0 ||
           strcmp(kind, "generator_function") == 0 || strcmp(kind, "arrow_function") == 0 ||
           strcmp(kind, "method_definition") == 0;
}

/* var belongs to the callable BODY, outside the parameter-default scope.
 * let/const belong to the nearest block, including a loop's header/body. */
static inline TSNode cbm_js_scope_node(TSNode node, bool var_scope) {
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "program") == 0 || strcmp(kind, "class_static_block") == 0)
        return node;
    if (var_scope && cbm_js_bodied_kind(kind)) {
        TSNode body = ts_node_child_by_field_name(node, "body", 4);
        return ts_node_is_null(body) ? node : body;
    }
    if (!var_scope && (strcmp(kind, "statement_block") == 0 ||
                       strcmp(kind, "switch_body") == 0 ||
                       strcmp(kind, "for_statement") == 0 ||
                       strcmp(kind, "for_in_statement") == 0))
        return node;
    return (TSNode){0};
}
#endif
