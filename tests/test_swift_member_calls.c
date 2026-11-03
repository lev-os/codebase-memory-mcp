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
#include "pipeline/pipeline_internal.h"
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
    {"App/Ext/View+Ext.swift", "import SwiftUI\n\nextension View {\n"
                               "    public func tagged(_ id: String) -> some View {\n        "
                               "return accessibilityIdentifier(id)\n    }\n}\n"},
    {"App/Model/Label.swift",
     "struct Label {\n    func tagged(_ id: String) -> Label { return self }\n}\n"},
    {"App/UI/Card.swift",
     "import SwiftUI\n\nstruct Card: View {\n    var body: some View {\n"
     "        VStack {\n            Text(\"a\")\n        }\n        .padding(1)\n"
     "        .tagged(\"card\")\n    }\n}\n"},
    {"App/VM/BaseVM.swift", "class BaseVM {\n    func refresh(host: Int) {}\n}\n"},
    {"App/VM/OtherVM.swift", "class OtherVM {\n    func refresh(host: Int) {}\n}\n"},
    {"App/VM/ChildVM.swift", "class ChildVM: BaseVM {\n"
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
static int swc_targets(sqlite3 *db, const char *src_file, const char *leaf, char *out, size_t cap) {
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
    printf("\n  %s -> %s: want one edge to ...%s, have %d:\n%s", src_file, leaf, want_tail, n, got);
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
    {"App/Geo/Square.swift", "class Square: Polygon {\n"
                             "    override func redraw(scale: Int) {\n"
                             "        super.redraw(scale: scale)\n"
                             "    }\n"
                             "    func paint(item: Any) {\n"
                             "        (item as? Polygon)?.redraw(scale: 2)\n"
                             "    }\n"
                             "}\n"},
    {"App/Geo/Circle.swift", "class Circle: Shape {\n    override func redraw(scale: Int) {}\n}\n"},
    {"App/Geo/Disc.swift", "class Disc: Circle {\n    func area() -> Int { return 0 }\n}\n"},
    {"App/Geo/Ring.swift", "class Ring: Disc {\n"
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

/* Every edge except OVERRIDE as "TYPE source -> target" lines without the
 * project prefix, sorted; NULL when the database cannot be read (the caller
 * frees). OVERRIDE is left out: the override pass (pass_semantic.c) climbs
 * the INHERITS and DEFINES_METHOD edges of unchanged ancestors, which the
 * closure-repair graph does not hold, so an incremental run drops
 * Square.redraw -> Shape.redraw. That gap is separate from the supertype
 * table this test pins. */
static char *swb_edge_set(const char *db_path) {
    sqlite3 *db = NULL;
    sqlite3_stmt *st = NULL;
    if (sqlite3_open_v2(db_path, &db, SQLITE_OPEN_READONLY, NULL) != SQLITE_OK ||
        sqlite3_prepare_v2(db,
                           "SELECT e.type || ' ' || replace(s.qualified_name, e.project || '.', '') "
                           "|| ' -> ' || replace(t.qualified_name, e.project || '.', '') "
                           "FROM edges e JOIN nodes s ON s.id = e.source_id "
                           "JOIN nodes t ON t.id = e.target_id WHERE e.type <> 'OVERRIDE' "
                           "ORDER BY 1",
                           -1, &st, NULL) != SQLITE_OK) {
        sqlite3_close(db);
        return NULL;
    }
    size_t cap = 4096;
    size_t len = 0;
    char *buf = malloc(cap);
    if (buf) {
        buf[0] = '\0';
    }
    while (buf && sqlite3_step(st) == SQLITE_ROW) {
        const char *line = (const char *)sqlite3_column_text(st, 0);
        size_t l = line ? strlen(line) : 0;
        if (len + l + 2 > cap) {
            cap = (len + l + 2) * 2;
            char *grown = realloc(buf, cap);
            if (!grown) {
                free(buf);
                buf = NULL;
                break;
            }
            buf = grown;
        }
        memcpy(buf + len, line, l);
        len += l;
        buf[len++] = '\n';
        buf[len] = '\0';
    }
    sqlite3_finalize(st);
    sqlite3_close(db);
    return buf;
}

static int swb_index(const char *dir, const char *db_path) {
    cbm_pipeline_t *p = cbm_pipeline_new(dir, db_path, CBM_MODE_FULL);
    int rc = p ? cbm_pipeline_run(p) : -1;
    if (p) {
        cbm_pipeline_free(p);
    }
    return rc;
}

/* A body-only edit of a caller re-resolves it on the closure-repair route,
 * against proxies of the unchanged types. Their declared supertypes must
 * reach the registry there too, or every inherited-member edge to an
 * unchanged type disappears: the edge set must equal a fresh full index
 * (OVERRIDE aside, see swb_edge_set). */
TEST(swift_inherited_member_incremental_matches_full) {
    char *dir = th_mktempdir("cbm_swift_base_incr");
    ASSERT_NOT_NULL(dir);
    char repo[512];
    snprintf(repo, sizeof(repo), "%s/repo", dir);
    int wrote = 0;
    for (size_t i = 0; i < sizeof(SWB_FILES) / sizeof(SWB_FILES[0]); i++) {
        wrote |= th_write_file(TH_PATH(repo, SWB_FILES[i][0]), SWB_FILES[i][1]);
    }
    char inc_db[600];
    char full_db[600];
    snprintf(inc_db, sizeof(inc_db), "%s/inc.db", dir);
    snprintf(full_db, sizeof(full_db), "%s/full.db", dir);
    int route = -1;
    char *inc = NULL;
    char *full = NULL;
    if (wrote == 0 && swb_index(repo, inc_db) == 0 &&
        th_write_file(TH_PATH(repo, "App/Geo/Square.swift"),
                      "class Square: Polygon {\n"
                      "    override func redraw(scale: Int) {\n"
                      "        super.redraw(scale: scale)\n"
                      "        super.redraw(scale: scale + 1)\n"
                      "    }\n"
                      "    func paint(item: Any) {\n"
                      "        (item as? Polygon)?.redraw(scale: 2)\n"
                      "        (item as? Polygon)?.redraw(scale: 4)\n"
                      "    }\n"
                      "}\n") == 0) {
        cbm_pipeline_incremental_test_reset_faults();
        if (swb_index(repo, inc_db) == 0) {
            route = (int)cbm_pipeline_incremental_test_last_route();
            if (swb_index(repo, full_db) == 0) {
                inc = swb_edge_set(inc_db);
                full = swb_edge_set(full_db);
            }
        }
    }
    static const char want[] =
        "CALLS App.Geo.Square.Square.paint -> App.Geo.Shape.Shape.redraw\n";
    int ok = inc && full && strcmp(inc, full) == 0 && strstr(full, want) &&
             route == (int)CBM_INCREMENTAL_ROUTE_CLOSURE_REPAIR;
    if (!ok) {
        printf("\n  route %d (want %d), want edge [%s]\n--- incremental\n%s--- full\n%s", route,
               (int)CBM_INCREMENTAL_ROUTE_CLOSURE_REPAIR, want, inc ? inc : "(null)",
               full ? full : "(null)");
    }
    free(inc);
    free(full);
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

/* A leading-dot call is View.m only on a view chain. A chain rooted in a
 * plain call (`make()\n    .resume()`: URLSession, Combine, RxSwift) keeps
 * its source text, so it binds like the one-line `make().resume()`. */
static const char SWC_CHAIN_SRC[] = "import SwiftUI\n\n"
                                    "final class Job { func resume() {} }\n"
                                    "final class Runner {\n"
                                    "    func make() -> Job { return Job() }\n"
                                    "    func run() {\n"
                                    "        make()\n"
                                    "            .resume()\n"
                                    "    }\n"
                                    "}\n"
                                    "struct Row: View {\n"
                                    "    var body: some View {\n"
                                    "        Text(\"a\")\n"
                                    "            .stamped(1)\n"
                                    "    }\n"
                                    "    func wrap(content: Content) -> some View {\n"
                                    "        content.padding()\n"
                                    "            .stamped(2)\n"
                                    "    }\n"
                                    "    func badge() -> some View {\n"
                                    "        Kit.Badge()\n"
                                    "            .stamped(3)\n"
                                    "    }\n"
                                    "    func listen() {\n"
                                    "        feed()\n"
                                    "            .receive(on: main)\n"
                                    "            .sink { _ in }\n"
                                    "    }\n"
                                    "}\n";

TEST(swift_leading_dot_chain_needs_view_root) {
    CBMFileResult *r = cbm_extract_file(SWC_CHAIN_SRC, (int)strlen(SWC_CHAIN_SRC), CBM_LANG_SWIFT,
                                        "t", "Runner.swift", 0, NULL, NULL);
    ASSERT_NOT_NULL(r);
    ASSERT_FALSE(r->has_error);
    ASSERT_FALSE(swc_has_call(r, "View.resume"));
    /* The callee is the navigation text, as on every other member call. */
    ASSERT(swc_has_call(r, "make()\n            .resume"));
    /* A Combine-style operator chain is not a view either. */
    ASSERT_FALSE(swc_has_call(r, "View.sink"));
    ASSERT_FALSE(swc_has_call(r, "View.receive"));
    /* A capitalised (or qualified) constructor root, and a chain that
     * applies a known modifier. */
    int stamped = 0;
    for (int i = 0; i < r->calls.count; i++) {
        const char *c = r->calls.items[i].callee_name;
        stamped += c && strcmp(c, "View.stamped") == 0;
    }
    ASSERT_EQ(stamped, 3);
    cbm_free_result(r);
    PASS();
}

static const char *const SWC_CHAIN_FILES[][2] = {
    {"Net/Job.swift", "final class Job {\n    func resume() {}\n}\n"},
    {"Net/Runner.swift", "final class Runner {\n    func make() -> Job { return Job() }\n"
                         "    func run() {\n        make()\n            .resume()\n    }\n}\n"},
};

TEST(swift_leading_dot_non_view_chain_binds) {
    char *dir = th_mktempdir("cbm_swift_chain");
    ASSERT_NOT_NULL(dir);
    int wrote = 0;
    for (size_t i = 0; i < sizeof(SWC_CHAIN_FILES) / sizeof(SWC_CHAIN_FILES[0]); i++) {
        wrote |= th_write_file(TH_PATH(dir, SWC_CHAIN_FILES[i][0]), SWC_CHAIN_FILES[i][1]);
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
    int ok = swc_expect_one(db, "Runner.run", "resume", "Job.resume");
    sqlite3_close(db);
    th_cleanup(dir);
    ASSERT_TRUE(ok);
    PASS();
}

/* One function of n pairs `if let a<i> = v as? Job { a<i>.resume() }` and
 * `let b<i> = v as? Job; b<i>?.resume()`. */
static char *swc_big_function(int n) {
    size_t cap = (size_t)n * 128 + 256;
    char *buf = malloc(cap);
    if (!buf) {
        return NULL;
    }
    size_t used =
        (size_t)snprintf(buf, cap, "final class Job { func resume() {} }\nfunc big(_ v: Any) {\n");
    for (int i = 0; i < n; i++) {
        used += (size_t)snprintf(buf + used, cap - used,
                                 "    if let a%d = v as? Job { a%d.resume() }\n"
                                 "    let b%d = v as? Job; b%d?.resume()\n",
                                 i, i, i, i);
    }
    snprintf(buf + used, cap - used, "}\n");
    return buf;
}

/* CPU seconds to extract swc_big_function(n); -1 when the calls are wrong. */
static double swc_extract_cpu(int n) {
    char *src = swc_big_function(n);
    if (!src) {
        return -1;
    }
    uint64_t t0 = cbm_thread_cpu_time_ns();
    CBMFileResult *r =
        cbm_extract_file(src, (int)strlen(src), CBM_LANG_SWIFT, "t", "Big.swift", 0, NULL, NULL);
    uint64_t t1 = cbm_thread_cpu_time_ns();
    int typed = 0;
    if (r) {
        for (int i = 0; i < r->calls.count; i++) {
            const char *c = r->calls.items[i].callee_name;
            typed += c && strcmp(c, "Job.resume") == 0;
        }
        cbm_free_result(r);
    }
    free(src);
    if (typed != 2 * n) {
        printf("\n  n=%d: %d of %d cast-receiver calls named Job.resume\n", n, typed, 2 * n);
        return -1;
    }
    return (double)(t1 - t0) / 1e9;
}

/* Cast-receiver lookup is linear in the function: 8x the bindings and calls
 * costs about 8x, not 64x. (A walk of the body per call made 8k lines cost
 * 46 s.) The ratio is of thread CPU time, so a busy host does not skew it. */
TEST(swift_cast_receiver_lookup_is_linear) {
    double small = swc_extract_cpu(500);
    double large = swc_extract_cpu(4000);
    ASSERT_TRUE(small > 0 && large > 0);
    double ratio = large / (small > 1e-3 ? small : 1e-3);
    if (ratio >= 20.0) {
        printf("\n  extract: n=500 %.3fs, n=4000 %.3fs, ratio %.1f\n", small, large, ratio);
    }
    ASSERT_TRUE(ratio < 20.0);
    PASS();
}

SUITE(swift_member_calls) {
    RUN_TEST(swift_member_callee_names_receiver_type);
    RUN_TEST(swift_member_calls_bind_named_receiver_type);
    RUN_TEST(swift_member_calls_bind_inherited_member);
    RUN_TEST(swift_inherited_member_incremental_matches_full);
    RUN_TEST(swift_inherited_member_registry_rules);
    RUN_TEST(swift_leading_dot_chain_needs_view_root);
    RUN_TEST(swift_leading_dot_non_view_chain_binds);
    RUN_TEST(swift_cast_receiver_lookup_is_linear);
}
