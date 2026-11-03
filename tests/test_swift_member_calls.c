/*
 * test_swift_member_calls.c — Swift member calls whose callee text does not
 * name the receiver's type get a CALLS edge to the project method the source
 * does name.
 *
 * Swift has no semantic resolver here: the registry binds a call by its
 * callee text. Three shapes lost their edge:
 *   - a SwiftUI modifier on a view expression, `.tagged("id")` on the line
 *     after the view: the callee text was the whole multi-line chain, which
 *     the receiver-chain guard refused, so a project `extension View` modifier
 *     had no callers;
 *   - `super.m()`: bound by name to whichever same-named override was
 *     nearest instead of the base class's method;
 *   - a cast receiver, `(x as? T)?.m()` or `let y = x as? T; y?.m()`.
 * Each fixture method has a same-named decoy on another type.
 */
#include "../src/foundation/compat.h"
#include "test_framework.h"
#include "test_helpers.h"
#include "cbm.h"
#include "pipeline/pipeline.h"
#include "sqlite3.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int swc_has_call(CBMFileResult *r, const char *callee) {
    for (int i = 0; i < r->calls.count; i++) {
        if (r->calls.items[i].callee_name && strcmp(r->calls.items[i].callee_name, callee) == 0) {
            return 1;
        }
    }
    return 0;
}

static const char SWC_VIEW_SRC[] =
    "import SwiftUI\n\n"
    "struct Card: View {\n"
    "    var body: some View {\n"
    "        VStack {\n            Text(\"a\")\n        }\n"
    "        .frame(width: 1)\n"
    "        .tagged(\"card\")\n"
    "    }\n"
    "}\n\n"
    "class Child: Base {\n"
    "    override func refresh(host: Int) {\n"
    "        super.refresh(host: host)\n"
    "        let other = item as? Base\n"
    "        other?.refresh(host: 1)\n"
    "        (item as? Base)?.refresh(host: 2)\n"
    "        if let again = item as? Base { again.refresh(host: 3) }\n"
    "        helper.run()\n"
    "    }\n"
    "}\n";

TEST(swift_member_callee_names_receiver_type) {
    CBMFileResult *r = cbm_extract_file(SWC_VIEW_SRC, (int)strlen(SWC_VIEW_SRC), CBM_LANG_SWIFT,
                                        "t", "Card.swift", 0, NULL, NULL);
    ASSERT_NOT_NULL(r);
    ASSERT_FALSE(r->has_error);
    /* A leading-dot modifier on a view expression is a View member. */
    ASSERT(swc_has_call(r, "View.tagged"));
    ASSERT(swc_has_call(r, "View.frame"));
    /* super. names the first inherited type. */
    ASSERT(swc_has_call(r, "Base.refresh"));
    ASSERT_FALSE(swc_has_call(r, "super.refresh"));
    /* Cast receivers name the cast type. */
    ASSERT_FALSE(swc_has_call(r, "other?.refresh"));
    ASSERT_FALSE(swc_has_call(r, "again.refresh"));
    /* A plain name receiver keeps its text. */
    ASSERT(swc_has_call(r, "helper.run"));
    cbm_free_result(r);
    PASS();
}

static const char *const SWC_FILES[][2] = {
    {"App/Ext/View+Ext.swift",
     "import SwiftUI\n\nextension View {\n"
     "    public func tagged(_ id: String) -> some View {\n        return accessibilityIdentifier(id)\n    }\n}\n"},
    {"App/Model/Label.swift",
     "struct Label {\n    func tagged(_ id: String) -> Label { return self }\n}\n"},
    {"App/UI/Card.swift",
     "import SwiftUI\n\nstruct Card: View {\n    var body: some View {\n"
     "        VStack {\n            Text(\"a\")\n        }\n        .padding(1)\n"
     "        .tagged(\"card\")\n    }\n}\n"},
    {"App/VM/BaseVM.swift",
     "class BaseVM {\n    func refresh(host: Int) {}\n}\n"},
    {"App/VM/OtherVM.swift",
     "class OtherVM {\n    func refresh(host: Int) {}\n}\n"},
    {"App/VM/ChildVM.swift",
     "class ChildVM: BaseVM {\n"
     "    var items: [Any] = []\n"
     "    override func refresh(host: Int) {\n"
     "        super.refresh(host: host)\n"
     "    }\n"
     "    func each(item: Any) {\n"
     "        let vm = item as? BaseVM\n"
     "        vm?.refresh(host: 1)\n"
     "    }\n"
     "}\n"},
};

/* Distinct target QNs of CALLS edges onto a node named `leaf` from the nodes
 * of file `src` or from the node whose QN ends `.<src>`, one per line;
 * returns the count. (A computed property such as a view's `body` has no node
 * of its own, so there the file is the caller unit.) */
static int swc_targets(sqlite3 *db, const char *src_file, const char *leaf, char *out,
                       size_t cap) {
    out[0] = '\0';
    static const char sql[] =
        "SELECT DISTINCT t.qualified_name FROM edges e JOIN nodes s ON s.id = e.source_id "
        "JOIN nodes t ON t.id = e.target_id WHERE e.type = 'CALLS' "
        "AND (s.file_path = ?1 OR s.qualified_name LIKE '%.' || ?1) AND t.name = ?2 ORDER BY 1";
    sqlite3_stmt *st = NULL;
    if (sqlite3_prepare_v2(db, sql, -1, &st, NULL) != SQLITE_OK) {
        return -1;
    }
    sqlite3_bind_text(st, 1, src_file, -1, SQLITE_STATIC);
    sqlite3_bind_text(st, 2, leaf, -1, SQLITE_STATIC);
    int n = 0;
    while (sqlite3_step(st) == SQLITE_ROW) {
        const char *qn = (const char *)sqlite3_column_text(st, 0);
        size_t used = strlen(out);
        snprintf(out + used, cap - used, "%s\n", qn ? qn : "");
        n++;
    }
    sqlite3_finalize(st);
    return n;
}

static int swc_expect_one(sqlite3 *db, const char *src_file, const char *leaf,
                          const char *want_tail) {
    char got[1024];
    int n = swc_targets(db, src_file, leaf, got, sizeof(got));
    size_t gl = strlen(got);
    size_t wl = strlen(want_tail);
    if (n == 1 && gl > wl + 1 && got[gl - wl - 2] == '.' &&
        strncmp(got + gl - wl - 1, want_tail, wl) == 0) {
        return 1;
    }
    printf("\n  %s -> %s: want one edge to ...%s, have %d:\n%s", src_file, leaf, want_tail, n,
           got);
    return 0;
}

TEST(swift_member_calls_bind_named_receiver_type) {
    char *dir = th_mktempdir("cbm_swift_member");
    ASSERT_NOT_NULL(dir);
    int wrote = 0;
    for (size_t i = 0; i < sizeof(SWC_FILES) / sizeof(SWC_FILES[0]); i++) {
        wrote |= th_write_file(TH_PATH(dir, SWC_FILES[i][0]), SWC_FILES[i][1]);
    }
    if (wrote != 0) {
        th_cleanup(dir);
        FAIL("fixture");
    }
    char db_path[512];
    snprintf(db_path, sizeof(db_path), "%s/swc.db", dir);
    int rc = -1;
    cbm_pipeline_t *p = cbm_pipeline_new(dir, db_path, CBM_MODE_FULL);
    if (p) {
        rc = cbm_pipeline_run(p);
        cbm_pipeline_free(p);
    }
    sqlite3 *db = NULL;
    if (rc != 0 || sqlite3_open_v2(db_path, &db, SQLITE_OPEN_READONLY, NULL) != SQLITE_OK) {
        if (db) {
            sqlite3_close(db);
        }
        th_cleanup(dir);
        FAIL("index");
    }
    int ok = 1;
    ok &= swc_expect_one(db, "App/UI/Card.swift", "tagged", "View.tagged");
    /* super.refresh, and the cast receiver vm?.refresh. */
    ok &= swc_expect_one(db, "ChildVM.refresh", "refresh", "BaseVM.refresh");
    ok &= swc_expect_one(db, "ChildVM.each", "refresh", "BaseVM.refresh");
    sqlite3_close(db);
    th_cleanup(dir);
    ASSERT_TRUE(ok);
    PASS();
}

SUITE(swift_member_calls) {
    RUN_TEST(swift_member_callee_names_receiver_type);
    RUN_TEST(swift_member_calls_bind_named_receiver_type);
}
