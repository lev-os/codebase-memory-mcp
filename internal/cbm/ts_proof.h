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
