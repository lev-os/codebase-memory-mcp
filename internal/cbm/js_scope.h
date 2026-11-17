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
/* One pattern model for both same-name declarations and lexical bindings.
 * Keys and default-value expressions are not binding patterns. */
static inline bool cbm_js_pattern_container(const char *kind) {
    return strcmp(kind, "formal_parameters") == 0 || strcmp(kind, "object_pattern") == 0 ||
           strcmp(kind, "array_pattern") == 0 || strcmp(kind, "rest_pattern") == 0;
}
static inline TSNode cbm_js_pattern_child(TSNode node) {
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "required_parameter") == 0 || strcmp(kind, "optional_parameter") == 0)
        return ts_node_child_by_field_name(node, "pattern", 7);
    if (strcmp(kind, "assignment_pattern") == 0 || strcmp(kind, "object_assignment_pattern") == 0)
        return ts_node_child_by_field_name(node, "left", 4);
    if (strcmp(kind, "pair_pattern") == 0)
        return ts_node_child_by_field_name(node, "value", 5);
    return (TSNode){0};
}
static inline bool cbm_js_pattern_binds(TSNode pattern, TSNode leaf, int depth) {
    if (ts_node_is_null(pattern) || depth > 32) return false;
    const char *kind = ts_node_type(pattern);
    if (strcmp(kind, "identifier") == 0 ||
        strcmp(kind, "shorthand_property_identifier_pattern") == 0)
        return ts_node_eq(pattern, leaf);
    if (cbm_js_pattern_container(kind)) {
        for (uint32_t i = 0; i < ts_node_named_child_count(pattern); i++)
            if (cbm_js_pattern_binds(ts_node_named_child(pattern, i), leaf, depth + 1)) return true;
        return false;
    }
    return cbm_js_pattern_binds(cbm_js_pattern_child(pattern), leaf, depth + 1);
}


static inline bool cbm_js_program_is_module(TSNode root) {
    for (uint32_t i = 0; i < ts_node_named_child_count(root); i++) {
        const char *kind = ts_node_type(ts_node_named_child(root, i));
        if (strcmp(kind, "import_statement") == 0 || strcmp(kind, "export_statement") == 0)
            return true;
    }
    return false;
}

#endif
