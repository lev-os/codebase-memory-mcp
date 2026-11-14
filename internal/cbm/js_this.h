#ifndef CBM_JS_THIS_H
#define CBM_JS_THIS_H

#include "cbm.h"
#include <string.h>

/* Whether a class member node (a method, a field, a static block) carries
 * the `static` keyword. */
static inline bool cbm_js_member_is_static(TSNode member) {
    if (strcmp(ts_node_type(member), "class_static_block") == 0) {
        return true;
    }
    uint32_t n = ts_node_child_count(member);
    for (uint32_t i = 0; i < n; i++) {
        if (strcmp(ts_node_type(ts_node_child(member, i)), "static") == 0) {
            return true;
        }
    }
    return false;
}

static inline bool js_this_binder_function(const char *k) {
    return strcmp(k, "function_declaration") == 0 ||
           strcmp(k, "generator_function_declaration") == 0 ||
           strcmp(k, "function_expression") == 0 || strcmp(k, "function") == 0 ||
           strcmp(k, "generator_function") == 0;
}

static inline bool js_this_binder_member(const char *k) {
    return strcmp(k, "method_definition") == 0 || strcmp(k, "public_field_definition") == 0 ||
           strcmp(k, "field_definition") == 0 || strcmp(k, "class_static_block") == 0;
}

/* The nearest JS/TS `this` binder, shared by call extraction and type
 * resolution. Arrows are transparent. A class member binds the instance
 * or the static side; ordinary functions and object methods do not bind
 * the surrounding class. An unnamed class is still a boundary. */
static inline CBMJsThis cbm_js_this_binding(TSNode node, TSNode *class_node) {
    *class_node = (TSNode){0};
    for (TSNode cur = ts_node_parent(node); !ts_node_is_null(cur); cur = ts_node_parent(cur)) {
        const char *k = ts_node_type(cur);
        bool member = js_this_binder_member(k);
        if (!member && !js_this_binder_function(k)) {
            if (strcmp(k, "program") == 0 || strcmp(k, "class_body") == 0)
                return CBM_JS_THIS_NONE;
            continue;
        }
        TSNode parent = ts_node_parent(cur);
        if (member && !ts_node_is_null(parent) && strcmp(ts_node_type(parent), "class_body") == 0) {
            *class_node = ts_node_parent(parent);
            return cbm_js_member_is_static(cur) ? CBM_JS_THIS_STATIC : CBM_JS_THIS_INSTANCE;
        }
        for (TSNode up = parent; !ts_node_is_null(up); up = ts_node_parent(up)) {
            if (strcmp(ts_node_type(up), "class_body") == 0)
                return CBM_JS_THIS_OTHER;
        }
        return CBM_JS_THIS_NONE;
    }
    return CBM_JS_THIS_NONE;
}

#endif
