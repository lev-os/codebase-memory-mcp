/* Shared syntax boundaries for conservative JS/TS return inference. */
#ifndef CBM_TS_PROOF_H
#define CBM_TS_PROOF_H

#include "tree_sitter/api.h"
#include <string.h>

/* A binding or write target that can hide a constructor. The caller walks
 * nested patterns too; property keys can only cause a conservative rejection. */
static inline TSNode cbm_ts_return_binding(TSNode node) {
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "variable_declarator") == 0 ||
        strcmp(kind, "class_declaration") == 0 || strcmp(kind, "class") == 0 ||
        strcmp(kind, "function_declaration") == 0 || strcmp(kind, "function_expression") == 0 ||
        strcmp(kind, "function") == 0 || strstr(kind, "generator"))
        return ts_node_child_by_field_name(node, "name", 4);
    if (strcmp(kind, "required_parameter") == 0 || strcmp(kind, "optional_parameter") == 0)
        return ts_node_child_by_field_name(node, "pattern", 7);
    if (strcmp(kind, "arrow_function") == 0)
        return ts_node_child_by_field_name(node, "parameter", 9);
    if (strcmp(kind, "assignment_expression") == 0 ||
        strcmp(kind, "augmented_assignment_expression") == 0 ||
        (strcmp(kind, "for_in_statement") == 0 &&
         !ts_node_is_null(ts_node_child_by_field_name(node, "kind", 4))))
        return ts_node_child_by_field_name(node, "left", 4);
    if (strcmp(kind, "update_expression") == 0)
        return ts_node_named_child(node, 0);
    if (strcmp(kind, "catch_clause") == 0)
        return ts_node_child_by_field_name(node, "parameter", 9);
    if (strcmp(kind, "formal_parameters") == 0)
        return node;
    TSNode parent = ts_node_parent(node);
    if (!ts_node_is_null(parent) && strcmp(ts_node_type(parent), "formal_parameters") == 0 &&
        strcmp(kind, "identifier") == 0)
        return node;
    return (TSNode){0};
}

/* Prove that control cannot reach the end normally. Unsupported control flow
 * withholds inference; returning and throwing both terminate a normal path. */
static inline bool cbm_ts_returns_on_normal_exit(TSNode node, int depth) {
    if (ts_node_is_null(node) || depth > 64)
        return false;
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "return_statement") == 0 || strcmp(kind, "throw_statement") == 0)
        return true;
    if (strcmp(kind, "if_statement") == 0)
        return cbm_ts_returns_on_normal_exit(ts_node_child_by_field_name(node, "consequence", 11),
                                             depth + 1) &&
               cbm_ts_returns_on_normal_exit(ts_node_child_by_field_name(node, "alternative", 11),
                                             depth + 1);
    if (strcmp(kind, "else_clause") == 0)
        return cbm_ts_returns_on_normal_exit(ts_node_named_child(node, 0), depth + 1);
    if (strcmp(kind, "statement_block") == 0) {
        uint32_t count = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < count; i++)
            if (cbm_ts_returns_on_normal_exit(ts_node_named_child(node, i), depth + 1))
                return true;
    }
    return false;
}

/* Parentheses and compile-time assertions preserve the runtime value. */
static inline TSNode cbm_ts_unwrap_value(TSNode node) {
    for (int depth = 0; depth < 64 && !ts_node_is_null(node); depth++) {
        const char *kind = ts_node_type(node);
        if (strcmp(kind, "parenthesized_expression") != 0 && strcmp(kind, "as_expression") != 0 &&
            strcmp(kind, "satisfies_expression") != 0)
            return node;
        node = ts_node_named_child(node, 0);
    }
    return (TSNode){0};
}

/* Only lexical bindings visible at this call hide the intrinsic eval. */
static inline bool cbm_ts_pattern_name_at(TSNode node, const char *source, const char *name, int depth) {
    if (ts_node_is_null(node) || depth > 64)
        return false;
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "identifier") == 0 || strcmp(kind, "type_identifier") == 0 ||
        strcmp(kind, "shorthand_property_identifier_pattern") == 0)
        return ts_node_end_byte(node) - ts_node_start_byte(node) == strlen(name) &&
               memcmp(source + ts_node_start_byte(node), name, strlen(name)) == 0;
    if (strcmp(kind, "pair_pattern") == 0)
        return cbm_ts_pattern_name_at(ts_node_child_by_field_name(node, "value", 5), source, name, depth + 1);
    if (strcmp(kind, "assignment_pattern") == 0 || strcmp(kind, "object_assignment_pattern") == 0)
        return cbm_ts_pattern_name_at(ts_node_child_by_field_name(node, "left", 4), source, name, depth + 1);
    if (strcmp(kind, "required_parameter") == 0 || strcmp(kind, "optional_parameter") == 0)
        return cbm_ts_pattern_name_at(ts_node_child_by_field_name(node, "pattern", 7), source, name, depth + 1);
    if (strcmp(kind, "formal_parameters") != 0 && strcmp(kind, "object_pattern") != 0 &&
        strcmp(kind, "array_pattern") != 0 && strcmp(kind, "rest_pattern") != 0)
        return false;
    uint32_t n = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < n; i++)
        if (cbm_ts_pattern_name_at(ts_node_named_child(node, i), source, name, depth + 1))
            return true;
    return false;
}

static inline bool cbm_ts_pattern_name(TSNode node, const char *source, const char *name) {
    return cbm_ts_pattern_name_at(node, source, name, 0);
}

static inline bool cbm_ts_eval_function(TSNode node) {
    const char *kind = ts_node_type(node);
    return strcmp(kind, "function_declaration") == 0 || strcmp(kind, "function_expression") == 0 ||
           strcmp(kind, "function") == 0 || strcmp(kind, "arrow_function") == 0 ||
           strcmp(kind, "method_definition") == 0 || strstr(kind, "generator");
}

/* Return one visible syntax declaration. Ambiguity leaves identity unproved. */
static inline TSNode cbm_ts_lexical_binding_at(TSNode site, const char *source, const char *name, bool *bound) {
    TSNode root = site;
    while (!ts_node_is_null(ts_node_parent(root)))
        root = ts_node_parent(root);
    TSNode found = {0};
    uint32_t width = UINT32_MAX;
    bool ambiguous = false;
    TSTreeCursor cursor = ts_tree_cursor_new(root);
    for (;;) {
        TSNode node = ts_tree_cursor_current_node(&cursor), binding = {0};
        const char *kind = ts_node_type(node);
        bool var = false, own = false;
        if (strcmp(kind, "variable_declarator") == 0) {
            binding = ts_node_child_by_field_name(node, "name", 4);
            var = strcmp(ts_node_type(ts_node_parent(node)), "variable_declaration") == 0;
        } else if (strcmp(kind, "function_declaration") == 0 ||
                   strcmp(kind, "generator_function_declaration") == 0 ||
                   strcmp(kind, "class_declaration") == 0 || strcmp(kind, "enum_declaration") == 0 ||
                   strcmp(kind, "internal_module") == 0 || strcmp(kind, "import_alias") == 0 ||
                   strcmp(kind, "import_require_clause") == 0) {
            binding = ts_node_child_by_field_name(node, "name", 4);
            if (ts_node_is_null(binding) && (strcmp(kind, "import_alias") == 0 ||
                                            strcmp(kind, "import_require_clause") == 0))
                binding = ts_node_named_child(node, 0);
        } else if (strcmp(kind, "function_expression") == 0 || strcmp(kind, "function") == 0 ||
                   strcmp(kind, "generator_function") == 0 || strcmp(kind, "class") == 0) {
            binding = ts_node_child_by_field_name(node, "name", 4);
            own = true;
        } else if (strcmp(kind, "formal_parameters") == 0) {
            binding = node;
        } else if (strcmp(kind, "arrow_function") == 0) {
            binding = ts_node_child_by_field_name(node, "parameter", 9);
            own = true;
        } else if (strcmp(kind, "catch_clause") == 0) {
            binding = ts_node_child_by_field_name(node, "parameter", 9);
            own = true;
        } else if (strcmp(kind, "import_specifier") == 0) {
            binding = ts_node_child_by_field_name(node, "alias", 5);
            if (ts_node_is_null(binding)) binding = ts_node_child_by_field_name(node, "name", 4);
        } else if (strcmp(kind, "namespace_import") == 0 || strcmp(kind, "import_clause") == 0) {
            for (uint32_t i = 0; i < ts_node_named_child_count(node); i++) {
                TSNode child = ts_node_named_child(node, i);
                if (strcmp(ts_node_type(child), "identifier") == 0) binding = child;
            }
        }
        if (cbm_ts_pattern_name(binding, source, name)) {
            TSNode scope = own ? node : ts_node_parent(node);
            for (; !ts_node_is_null(scope); scope = ts_node_parent(scope)) {
                const char *sk = ts_node_type(scope);
                if (cbm_ts_eval_function(scope) || strcmp(sk, "program") == 0 ||
                    (!var && (strcmp(sk, "statement_block") == 0 ||
                              strcmp(sk, "for_statement") == 0 || strcmp(sk, "for_in_statement") == 0 ||
                              strcmp(sk, "catch_clause") == 0 || strcmp(sk, "switch_body") == 0)) ||
                    own)
                    break;
            }
            if (!ts_node_is_null(scope) && ts_node_start_byte(scope) <= ts_node_start_byte(site) &&
                ts_node_end_byte(site) <= ts_node_end_byte(scope)) {
                uint32_t size = ts_node_end_byte(scope) - ts_node_start_byte(scope);
                if (size < width) {
                    width = size;
                    found = node;
                    ambiguous = false;
                } else if (size == width && !ts_node_eq(found, node)) {
                    ambiguous = true;
                }
            }
        }
        if (ts_tree_cursor_goto_first_child(&cursor)) continue;
        while (!ts_tree_cursor_goto_next_sibling(&cursor)) {
            if (!ts_tree_cursor_goto_parent(&cursor)) goto done;
        }
    }
done:
    ts_tree_cursor_delete(&cursor);
    if (bound)
        *bound = !ts_node_is_null(found);
    return ambiguous ? (TSNode){0} : found;
}

static inline bool cbm_ts_direct_eval(TSNode call, const char *source) {
    if (strcmp(ts_node_type(call), "call_expression") != 0)
        return false;
    TSNode callee = ts_node_child_by_field_name(call, "function", 8);
    while (!ts_node_is_null(callee) && strcmp(ts_node_type(callee), "parenthesized_expression") == 0)
        callee = ts_node_named_child(callee, 0);
    if (ts_node_is_null(callee) || strcmp(ts_node_type(callee), "identifier") != 0 ||
        ts_node_end_byte(callee) - ts_node_start_byte(callee) != 4 ||
        memcmp(source + ts_node_start_byte(callee), "eval", 4) != 0)
        return false;
    bool bound = false;
    (void)cbm_ts_lexical_binding_at(call, source, "eval", &bound);
    return !bound;
}

static inline bool cbm_ts_plain_object(TSNode node) {
    if (ts_node_is_null(node) || strcmp(ts_node_type(node), "object") != 0)
        return false;
    uint32_t count = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < count; i++)
        if (strcmp(ts_node_type(ts_node_named_child(node, i)), "spread_element") == 0)
            return false;
    return true;
}

#endif
