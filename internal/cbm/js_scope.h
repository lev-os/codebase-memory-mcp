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

/* Only declarations: `for (run of xs)` writes a name, it declares none. */
static inline TSNode cbm_js_header_binding(TSNode leaf) {
    for (TSNode parent = ts_node_parent(leaf); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        const char *kind = ts_node_type(parent);
        TSNode pattern = {0};
        if (strcmp(kind, "catch_clause") == 0)
            pattern = ts_node_child_by_field_name(parent, "parameter", 9);
        else if (strcmp(kind, "for_in_statement") == 0 &&
                 !ts_node_is_null(ts_node_child_by_field_name(parent, "kind", 4)))
            pattern = ts_node_child_by_field_name(parent, "left", 4);
        else if (strcmp(kind, "variable_declarator") == 0 || cbm_js_bodied_kind(kind))
            return (TSNode){0};
        if (!ts_node_is_null(pattern))
            return cbm_js_pattern_binds(pattern, leaf, 0) ? parent : (TSNode){0};
    }
    return (TSNode){0};
}

#endif
