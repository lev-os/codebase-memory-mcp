/* Read trace_path's public JSON response without depending on its text layout. */
#ifndef REPRO_TRACE_H
#define REPRO_TRACE_H

#include <yyjson/yyjson.h>
#include <string.h>

static inline yyjson_doc *rh_trace_json(const char *response) {
    yyjson_doc *envelope = response ? yyjson_read(response, strlen(response), 0) : NULL;
    yyjson_val *root = yyjson_doc_get_root(envelope);
    yyjson_val *content = yyjson_arr_get_first(yyjson_obj_get(root, "content"));
    const char *text = yyjson_get_str(yyjson_obj_get(content, "text"));
    yyjson_doc *result = !yyjson_get_bool(yyjson_obj_get(root, "isError")) && text
                             ? yyjson_read(text, strlen(text), 0) : NULL;
    yyjson_doc_free(envelope);
    return result;
}

/* Reconstruct the documented qualified name from each group prefix and row.
 * Returning a row requires a real hop, not a name echoed in an error or hint. */
static inline yyjson_val *rh_trace_row(yyjson_val *leg, const char *qualified_name) {
    yyjson_val *groups = yyjson_obj_get(leg, "groups");
    size_t i, count;
    yyjson_val *group;
    yyjson_arr_foreach(groups, i, count, group) {
        const char *prefix = yyjson_get_str(yyjson_obj_get(group, "qn_prefix"));
        if (!prefix)
            continue;
        size_t len = strlen(prefix);
        const char *name = qualified_name;
        if (len) {
            if (strncmp(qualified_name, prefix, len) != 0 || qualified_name[len] != '.')
                continue;
            name += len + 1;
        }
        size_t j, rows_count;
        yyjson_val *row;
        yyjson_arr_foreach(yyjson_obj_get(group, "rows"), j, rows_count, row) {
            const char *row_name = yyjson_get_str(yyjson_arr_get(row, 0));
            if (row_name && strcmp(row_name, name) == 0 &&
                yyjson_is_int(yyjson_arr_get(row, 1)))
                return row;
        }
    }
    return NULL;
}

#endif
