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

/* A leading-dot call is View.m only on a view chain. A chain rooted in a
 * plain call (`make()\n    .resume()`: URLSession, Combine, RxSwift) keeps
 * its source text, so it binds like the one-line `make().resume()`. */
static const char SWC_CHAIN_SRC[] =
    "import SwiftUI\n\n"
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
    {"Net/Runner.swift",
     "final class Runner {\n    func make() -> Job { return Job() }\n"
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
    size_t used = (size_t)snprintf(buf, cap,
                                   "final class Job { func resume() {} }\nfunc big(_ v: Any) {\n");
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
    RUN_TEST(swift_leading_dot_chain_needs_view_root);
    RUN_TEST(swift_leading_dot_non_view_chain_binds);
    RUN_TEST(swift_cast_receiver_lookup_is_linear);
}
