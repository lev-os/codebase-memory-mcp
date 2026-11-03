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

/* A member the receiver's type inherits: Square -> Polygon -> Shape, where only
 * Shape declares redraw. `super.redraw` in Square is the callee Polygon.redraw
 * and `(item as? Polygon)?.redraw` is Polygon.redraw too; both bind Shape's,
 * not the decoy Sketch.redraw. Ring -> Disc -> Circle -> Shape, where Circle
 * overrides redraw: the nearest declaration wins. */
static const char *const SWB_FILES[][2] = {
    {"App/Geo/Shape.swift", "class Shape {\n    func redraw(scale: Int) {}\n}\n"},
    {"App/Geo/Polygon.swift",
     "class Polygon: Shape {\n    func corners() -> Int { return 0 }\n}\n"},
    {"App/Geo/Square.swift",
     "class Square: Polygon {\n"
     "    override func redraw(scale: Int) {\n"
     "        super.redraw(scale: scale)\n"
     "    }\n"
     "    func paint(item: Any) {\n"
     "        (item as? Polygon)?.redraw(scale: 2)\n"
     "    }\n"
     "}\n"},
    {"App/Geo/Circle.swift",
     "class Circle: Shape {\n    override func redraw(scale: Int) {}\n}\n"},
    {"App/Geo/Disc.swift", "class Disc: Circle {\n    func area() -> Int { return 0 }\n}\n"},
    {"App/Geo/Ring.swift",
     "class Ring: Disc {\n"
     "    func spin() {\n"
     "        super.redraw(scale: 3)\n"
     "    }\n"
     "}\n"},
    {"App/Sketch/Sketch.swift", "class Sketch {\n    func redraw(scale: Int) {}\n}\n"},
};

TEST(swift_member_calls_bind_inherited_member) {
    char *dir = th_mktempdir("cbm_swift_base");
    ASSERT_NOT_NULL(dir);
    int wrote = 0;
    for (size_t i = 0; i < sizeof(SWB_FILES) / sizeof(SWB_FILES[0]); i++) {
        wrote |= th_write_file(TH_PATH(dir, SWB_FILES[i][0]), SWB_FILES[i][1]);
    }
    if (wrote != 0) {
        th_cleanup(dir);
        FAIL("fixture");
    }
    char db_path[512];
    snprintf(db_path, sizeof(db_path), "%s/swb.db", dir);
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
    ok &= swc_expect_one(db, "Square.redraw", "redraw", "Shape.redraw");
    ok &= swc_expect_one(db, "Square.paint", "redraw", "Shape.redraw");
    ok &= swc_expect_one(db, "Ring.spin", "redraw", "Circle.redraw");
    /* The decoy gets no caller at all. */
    static const char decoy_sql[] =
        "SELECT count(*) FROM edges e JOIN nodes t ON t.id = e.target_id "
        "WHERE e.type = 'CALLS' AND t.qualified_name LIKE '%.Sketch.redraw'";
    sqlite3_stmt *st = NULL;
    int decoy = -1;
    if (sqlite3_prepare_v2(db, decoy_sql, -1, &st, NULL) == SQLITE_OK &&
        sqlite3_step(st) == SQLITE_ROW) {
        decoy = sqlite3_column_int(st, 0);
    }
    sqlite3_finalize(st);
    if (decoy != 0) {
        printf("\n  Sketch.redraw: want no callers, have %d\n", decoy);
        ok = 0;
    }
    sqlite3_close(db);
    th_cleanup(dir);
    ASSERT_TRUE(ok);
    PASS();
}

static void swb_type(cbm_registry_t *r, const char *qn, const char *name, const char *base) {
    const char *bases[] = {base, NULL};
    cbm_registry_add_lang_in_module(r, name, qn, "Class", CBM_LANG_SWIFT, 0);
    if (base) {
        cbm_registry_add_supertypes(r, name, bases, CBM_LANG_SWIFT);
    }
}

static int swb_resolves_to(cbm_registry_t *r, const char *callee, CBMLanguage lang,
                           const char *want) {
    cbm_resolution_t res = cbm_registry_resolve_inherited_member(r, callee, lang);
    const char *got = res.qualified_name && res.qualified_name[0] ? res.qualified_name : NULL;
    if ((!want && !got) || (want && got && strcmp(want, got) == 0)) {
        return 1;
    }
    printf("\n  %s: want %s, have %s\n", callee, want ? want : "(none)", got ? got : "(none)");
    return 0;
}

TEST(swift_inherited_member_registry_rules) {
    cbm_registry_t *r = cbm_registry_new();
    ASSERT_NOT_NULL(r);
    /* Leaf -> Mid -> Root; only Root declares m. A decoy Other.m. */
    swb_type(r, "p.a.Root", "Root", NULL);
    swb_type(r, "p.a.Mid", "Mid", "a.Root<Int>");
    swb_type(r, "p.a.Leaf", "Leaf", "Mid");
    cbm_registry_add_lang_in_module(r, "m", "p.a.Root.m", "Method", CBM_LANG_SWIFT, 0);
    cbm_registry_add_lang_in_module(r, "m", "p.z.Other.m", "Method", CBM_LANG_SWIFT, 0);
    /* Mid declares n itself: the climb leaves it to the chain. */
    cbm_registry_add_lang_in_module(r, "n", "p.a.Mid.n", "Method", CBM_LANG_SWIFT, 0);
    cbm_registry_add_lang_in_module(r, "n", "p.a.Root.n", "Method", CBM_LANG_SWIFT, 0);
    /* Two same-named roots of Twin both declare k: ambiguous. */
    swb_type(r, "p.b.Twin", "Twin", "Pair");
    cbm_registry_add_lang_in_module(r, "k", "p.b.Pair.k", "Method", CBM_LANG_SWIFT, 0);
    cbm_registry_add_lang_in_module(r, "k", "p.c.Pair.k", "Method", CBM_LANG_SWIFT, 0);
    /* A chain ten deep: T0 -> T1 -> ... -> T9, only T9 declares deep. */
    for (int i = 0; i < 10; i++) {
        char qn[64], name[16], base[16];
        snprintf(qn, sizeof(qn), "p.d.T%d", i);
        snprintf(name, sizeof(name), "T%d", i);
        snprintf(base, sizeof(base), "T%d", i + 1);
        swb_type(r, qn, name, i < 9 ? base : NULL);
    }
    cbm_registry_add_lang_in_module(r, "deep", "p.d.T9.deep", "Method", CBM_LANG_SWIFT, 0);
    /* A cycle must end. */
    swb_type(r, "p.e.Loop", "Loop", "Pool");
    swb_type(r, "p.e.Pool", "Pool", "Loop");

    int ok = 1;
    ok &= swb_resolves_to(r, "Leaf.m", CBM_LANG_SWIFT, "p.a.Root.m");
    ok &= swb_resolves_to(r, "Mid.m", CBM_LANG_SWIFT, "p.a.Root.m");
    ok &= swb_resolves_to(r, "Leaf.n", CBM_LANG_SWIFT, "p.a.Mid.n");
    ok &= swb_resolves_to(r, "Mid.n", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "Root.m", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "Twin.k", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "T2.deep", CBM_LANG_SWIFT, "p.d.T9.deep");
    ok &= swb_resolves_to(r, "T0.deep", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "Loop.m", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "leaf.m", CBM_LANG_SWIFT, NULL);
    ok &= swb_resolves_to(r, "Leaf.m", CBM_LANG_KOTLIN, NULL);
    cbm_registry_free(r);
    /* Kotlin records nothing. */
    cbm_registry_t *k = cbm_registry_new();
    const char *kb[] = {"Root", NULL};
    cbm_registry_add_lang_in_module(k, "m", "p.a.Root.m", "Method", CBM_LANG_KOTLIN, 0);
    cbm_registry_add_supertypes(k, "Leaf", kb, CBM_LANG_KOTLIN);
    ok &= swb_resolves_to(k, "Leaf.m", CBM_LANG_SWIFT, NULL);
    cbm_registry_free(k);
    ASSERT_TRUE(ok);
    PASS();
}

SUITE(swift_member_calls) {
    RUN_TEST(swift_member_callee_names_receiver_type);
    RUN_TEST(swift_member_calls_bind_named_receiver_type);
    RUN_TEST(swift_member_calls_bind_inherited_member);
    RUN_TEST(swift_inherited_member_registry_rules);
}
