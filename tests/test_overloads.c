/*
 * test_overloads.c — same-file overloads are separate nodes, and a call binds
 * to the overload its arguments fit (internal/cbm/callable_overload.h).
 *
 * Every fixture is made up. A class `Store` declares three `action`
 * overloads and one plain method `solo`; callers in another file call each
 * overload once. Before the split, the three overloads were one node (the
 * last one's span) that collected every caller.
 */
#include "../src/foundation/compat.h"
#include "test_framework.h"
#include "test_helpers.h"
#include "callable_overload.h"
#include "foundation/arena.h"
#include <foundation/compat_fs.h>
#include <pipeline/pipeline.h>
#include <pipeline/pipeline_internal.h>
#include <store/store.h>
#include <sqlite3.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── The matcher ───────────────────────────────────────────────── */

TEST(overload_shape_swift_labels) {
    /* func action(_ id: Int), action(named: String), action(_ id: Int, to: String = "") */
    ASSERT_TRUE(cbm_callable_shape_matches("_", "_", CBM_LANG_SWIFT));
    ASSERT_FALSE(cbm_callable_shape_matches("_", "named", CBM_LANG_SWIFT));
    ASSERT_TRUE(cbm_callable_shape_matches("named", "named", CBM_LANG_SWIFT));
    ASSERT_FALSE(cbm_callable_shape_matches("named", "_", CBM_LANG_SWIFT));
    ASSERT_TRUE(cbm_callable_shape_matches("_,to=", "_", CBM_LANG_SWIFT));
    ASSERT_TRUE(cbm_callable_shape_matches("_,to=", "_,to", CBM_LANG_SWIFT));
    ASSERT_FALSE(cbm_callable_shape_matches("_,to", "_", CBM_LANG_SWIFT));
    ASSERT_FALSE(cbm_callable_shape_matches("_,to", "_,from", CBM_LANG_SWIFT));
    /* variadic takes the unlabeled arguments that follow it */
    ASSERT_TRUE(cbm_callable_shape_matches("_~", "_,_,_", CBM_LANG_SWIFT));
    ASSERT_TRUE(cbm_callable_shape_matches("_~", "", CBM_LANG_SWIFT));
    /* a trailing closure fills the closure parameter */
    ASSERT_TRUE(cbm_callable_shape_matches("named,completion", "named,*", CBM_LANG_SWIFT));
    ASSERT_FALSE(cbm_callable_shape_matches("named", "named,*", CBM_LANG_SWIFT));
    PASS();
}

TEST(overload_shape_counts) {
    ASSERT_TRUE(cbm_callable_shape_matches("_,_", "_,_", CBM_LANG_JAVA));
    ASSERT_FALSE(cbm_callable_shape_matches("_,_", "_", CBM_LANG_JAVA));
    ASSERT_FALSE(cbm_callable_shape_matches("_", "_,_", CBM_LANG_JAVA));
    ASSERT_TRUE(cbm_callable_shape_matches("_,_~", "_", CBM_LANG_JAVA));
    ASSERT_TRUE(cbm_callable_shape_matches("_,_~", "_,_,_,_", CBM_LANG_JAVA));
    ASSERT_TRUE(cbm_callable_shape_matches("", "", CBM_LANG_JAVA));
    /* Kotlin defaults and a trailing lambda */
    ASSERT_TRUE(cbm_callable_shape_matches("_,_,_=", "_,_", CBM_LANG_KOTLIN));
    ASSERT_TRUE(cbm_callable_shape_matches("_,_,_=", "_,_,_", CBM_LANG_KOTLIN));
    ASSERT_FALSE(cbm_callable_shape_matches("_,_,_=", "_", CBM_LANG_KOTLIN));
    ASSERT_TRUE(cbm_callable_shape_matches("_,_", "_,*", CBM_LANG_KOTLIN));
    /* Kotlin named arguments bind by parameter name */
    ASSERT_TRUE(cbm_callable_shape_matches("id,target=,done", "_,done", CBM_LANG_KOTLIN));
    ASSERT_TRUE(cbm_callable_shape_matches("id,target=,done=", "_,*", CBM_LANG_KOTLIN));
    ASSERT_FALSE(cbm_callable_shape_matches("id,target=", "_,done", CBM_LANG_KOTLIN));
    ASSERT_FALSE(cbm_callable_shape_matches("id,target", "_,id", CBM_LANG_KOTLIN));
    /* an unknown side never rules a member out */
    ASSERT_TRUE(cbm_callable_shape_matches("?", "_,_", CBM_LANG_JAVA));
    ASSERT_TRUE(cbm_callable_shape_matches("_", NULL, CBM_LANG_JAVA));
    PASS();
}

/* ── Extraction: the split and the stable QNs ──────────────────── */

static const CBMDefinition *ovl_def_at(const CBMFileResult *r, const char *name, uint32_t line) {
    for (int i = 0; i < r->defs.count; i++) {
        const CBMDefinition *d = &r->defs.items[i];
        if (d->name && strcmp(d->name, name) == 0 && d->start_line == line) {
            return d;
        }
    }
    return NULL;
}

static const char *ovl_prop(const CBMDefinition *d, const char *key) {
    for (const char **kv = d->extra_props; kv && kv[0] && kv[1]; kv += 2) {
        if (strcmp(kv[0], key) == 0) {
            return kv[1];
        }
    }
    return NULL;
}

TEST(overload_extract_java_split_keeps_plain_qns) {
    static const char src[] = "package demo;\n"
                              "public class Store {\n"
                              "    public void action(int id) {}\n"
                              "    public void action(int id, String target) {}\n"
                              "    public void action(int id, String target, boolean flag) {}\n"
                              "    public void solo() {}\n"
                              "    public void action() {}\n"
                              "}\n";
    CBMFileResult *r = cbm_extract_file(src, (int)strlen(src), CBM_LANG_JAVA, "p",
                                        "demo/Store.java", 0, NULL, NULL);
    ASSERT_NOT_NULL(r);
    const CBMDefinition *a1 = ovl_def_at(r, "action", 3);
    const CBMDefinition *a2 = ovl_def_at(r, "action", 4);
    const CBMDefinition *a3 = ovl_def_at(r, "action", 5);
    const CBMDefinition *solo = ovl_def_at(r, "solo", 6);
    ASSERT_NOT_NULL(a1);
    ASSERT_NOT_NULL(a2);
    ASSERT_NOT_NULL(a3);
    ASSERT_NOT_NULL(solo);
    /* the first overload and the plain method keep their historical QN */
    ASSERT_EQ(a1->qn_sig_off, 0);
    ASSERT_NULL(strchr(a1->qualified_name, '('));
    ASSERT_EQ(solo->qn_sig_off, 0);
    ASSERT_NULL(strchr(solo->qualified_name, '('));
    ASSERT_NULL(ovl_prop(solo, CBM_OVERLOAD_PARAMS_PROP));
    /* the later ones: base QN + signature */
    ASSERT_STR_EQ(a2->qualified_name + a2->qn_sig_off, "(int,String)");
    ASSERT_STR_EQ(a3->qualified_name + a3->qn_sig_off, "(int,String,boolean)");
    ASSERT_EQ(strncmp(a2->qualified_name, a1->qualified_name, a2->qn_sig_off), 0);
    ASSERT_STR_EQ(ovl_prop(a1, CBM_OVERLOAD_PARAMS_PROP), "_");
    ASSERT_STR_EQ(ovl_prop(a3, CBM_OVERLOAD_PARAMS_PROP), "_,_,_");
    const CBMDefinition *a0 = ovl_def_at(r, "action", 7);
    ASSERT_NOT_NULL(a0);
    ASSERT_STR_EQ(a0->qualified_name + a0->qn_sig_off, "()");
    ASSERT_STR_EQ(ovl_prop(a0, CBM_OVERLOAD_PARAMS_PROP), CBM_OVERLOAD_NO_PARAMS);
    cbm_free_result(r);
    PASS();
}

TEST(overload_extract_swift_same_signature_stays_one_qn) {
    /* #if twins with one signature are one definition; a different label is
     * an overload. */
    static const char src[] = "class Store {\n"
                              "#if os(iOS)\n"
                              "    func pick(_ id: Int) {}\n"
                              "#else\n"
                              "    func pick(_ id: Int) {}\n"
                              "#endif\n"
                              "    func pick(named: String, to target: String = \"\") {}\n"
                              "}\n";
    CBMFileResult *r = cbm_extract_file(src, (int)strlen(src), CBM_LANG_SWIFT, "p",
                                        "Store.swift", 0, NULL, NULL);
    ASSERT_NOT_NULL(r);
    const CBMDefinition *p1 = ovl_def_at(r, "pick", 3);
    const CBMDefinition *p2 = ovl_def_at(r, "pick", 5);
    const CBMDefinition *p3 = ovl_def_at(r, "pick", 7);
    ASSERT_NOT_NULL(p1);
    ASSERT_NOT_NULL(p2);
    ASSERT_NOT_NULL(p3);
    ASSERT_STR_EQ(p1->qualified_name, p2->qualified_name);
    ASSERT_STR_EQ(p3->qualified_name + p3->qn_sig_off, "(named:String,to:String)");
    ASSERT_STR_EQ(ovl_prop(p3, CBM_OVERLOAD_PARAMS_PROP), "named,to=");
    cbm_free_result(r);
    PASS();
}

/* ── End to end: each caller binds to its overload ─────────────── */

typedef struct {
    const char *path;
    const char *content;
} ovl_file_t;

typedef struct {
    const char *lang;
    const ovl_file_t *files;
    int file_count;
    const char *pad_fmt; /* filler file content, %d = index */
    const char *pad_path_fmt;
    int lines[3];          /* start lines of the three overloads */
    const char *callers[3]; /* caller i calls overload i */
    int solo_line;
} ovl_case_t;

static bool ovl_write(const char *root, const char *rel, const char *content) {
    char path[700];
    snprintf(path, sizeof(path), "%s/%s", root, rel);
    char *slash = strrchr(path, '/');
    if (slash && slash > path + strlen(root)) {
        *slash = '\0';
        cbm_mkdir_p(path, 0755);
        *slash = '/';
    }
    return th_write_file(path, content) == 0;
}

/* CALLS edges from the method `caller` into the `callee` node at `line`. */
static int ovl_calls(sqlite3 *db, const char *project, const char *caller, const char *callee,
                     int line) {
    sqlite3_stmt *st = NULL;
    if (sqlite3_prepare_v2(db,
                           "SELECT COUNT(*) FROM edges e JOIN nodes s ON s.id=e.source_id "
                           "JOIN nodes t ON t.id=e.target_id WHERE e.project=?1 AND "
                           "e.type='CALLS' AND s.name=?2 AND t.name=?3 AND t.start_line=?4",
                           -1, &st, NULL) != SQLITE_OK) {
        return -1;
    }
    sqlite3_bind_text(st, 1, project, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(st, 2, caller, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(st, 3, callee, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(st, 4, line);
    int n = sqlite3_step(st) == SQLITE_ROW ? sqlite3_column_int(st, 0) : -1;
    sqlite3_finalize(st);
    return n;
}

static int ovl_int(sqlite3 *db, const char *sql, const char *project, const char *name) {
    sqlite3_stmt *st = NULL;
    if (sqlite3_prepare_v2(db, sql, -1, &st, NULL) != SQLITE_OK) {
        return -1;
    }
    sqlite3_bind_text(st, 1, project, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(st, 2, name, -1, SQLITE_TRANSIENT);
    int n = sqlite3_step(st) == SQLITE_ROW ? sqlite3_column_int(st, 0) : -1;
    sqlite3_finalize(st);
    return n;
}

typedef struct {
    char *workers;
    char *single;
} ovl_env_t;

static ovl_env_t ovl_env_select(bool parallel) {
    ovl_env_t save = {0};
    const char *w = getenv("CBM_WORKERS");
    const char *s = getenv("CBM_INDEX_SINGLE_THREAD");
    save.workers = w ? strdup(w) : NULL;
    save.single = s ? strdup(s) : NULL;
    if (parallel) {
        cbm_unsetenv("CBM_INDEX_SINGLE_THREAD");
        cbm_setenv("CBM_WORKERS", "4", 1);
    } else {
        cbm_setenv("CBM_INDEX_SINGLE_THREAD", "1", 1);
    }
    return save;
}

static void ovl_env_restore(ovl_env_t *save) {
    if (save->workers) {
        cbm_setenv("CBM_WORKERS", save->workers, 1);
    } else {
        cbm_unsetenv("CBM_WORKERS");
    }
    if (save->single) {
        cbm_setenv("CBM_INDEX_SINGLE_THREAD", save->single, 1);
    } else {
        cbm_unsetenv("CBM_INDEX_SINGLE_THREAD");
    }
    free(save->workers);
    free(save->single);
}

/* 0 when every caller binds to its own overload only, the three overloads
 * are three nodes, and `solo` keeps a plain QN; else prints what it saw. */
static int ovl_run(const ovl_case_t *c, bool parallel) {
    char tmp[256];
    snprintf(tmp, sizeof(tmp), "/tmp/cbm_ovl_XXXXXX");
    if (!cbm_mkdtemp(tmp)) {
        return 1;
    }
    bool ok = true;
    for (int i = 0; i < c->file_count && ok; i++) {
        ok = ovl_write(tmp, c->files[i].path, c->files[i].content);
    }
    for (int i = 0; parallel && i < 55 && ok; i++) {
        char rel[256];
        char src[512];
        snprintf(rel, sizeof(rel), c->pad_path_fmt, i);
        snprintf(src, sizeof(src), c->pad_fmt, i, i);
        ok = ovl_write(tmp, rel, src);
    }
    int got[3][3];
    memset(got, -1, sizeof(got));
    int action_nodes = -1;
    int plain_action = -1;
    int plain_solo = -1;
    int rc = -1;
    if (ok) {
        ovl_env_t save = ovl_env_select(parallel);
        char db_path[512];
        snprintf(db_path, sizeof(db_path), "%s/ovl.db", tmp);
        cbm_pipeline_t *pipeline = cbm_pipeline_new(tmp, db_path, CBM_MODE_FULL);
        if (pipeline) {
            rc = cbm_pipeline_run(pipeline);
            const char *project = cbm_pipeline_project_name(pipeline);
            cbm_store_t *store = cbm_store_open_path(db_path);
            sqlite3 *db = store ? cbm_store_get_db(store) : NULL;
            if (db && project) {
                for (int k = 0; k < 3; k++) {
                    for (int o = 0; o < 3; o++) {
                        got[k][o] = ovl_calls(db, project, c->callers[k], "action", c->lines[o]);
                    }
                }
                action_nodes = ovl_int(db,
                                       "SELECT COUNT(DISTINCT qualified_name) FROM nodes WHERE "
                                       "project=?1 AND name=?2 AND label='Method'",
                                       project, "action");
                plain_action = ovl_int(db,
                                       "SELECT COUNT(*) FROM nodes WHERE project=?1 AND name=?2 "
                                       "AND label='Method' AND instr(qualified_name,'(')=0",
                                       project, "action");
                plain_solo = ovl_int(db,
                                     "SELECT COUNT(*) FROM nodes WHERE project=?1 AND name=?2 "
                                     "AND label='Method' AND instr(qualified_name,'(')=0 AND "
                                     "instr(properties,'overload_params')=0",
                                     project, "solo");
            }
            if (store) {
                cbm_store_close(store);
            }
            cbm_pipeline_free(pipeline);
        }
        ovl_env_restore(&save);
    }
    th_rmtree(tmp);
    for (int k = 0; k < 3; k++) {
        for (int o = 0; o < 3; o++) {
            ok = ok && got[k][o] == (k == o ? 1 : 0);
        }
    }
    ok = ok && rc == 0 && action_nodes == 3 && plain_action == 1 && plain_solo == 1;
    if (!ok) {
        fprintf(stderr,
                "  [%s %s] rc=%d nodes=%d plain=%d solo=%d calls a:%d/%d/%d b:%d/%d/%d "
                "c:%d/%d/%d\n",
                c->lang, parallel ? "parallel" : "sequential", rc, action_nodes, plain_action,
                plain_solo, got[0][0], got[0][1], got[0][2], got[1][0], got[1][1], got[1][2],
                got[2][0], got[2][1], got[2][2]);
    }
    return ok ? 0 : 1;
}

static const ovl_file_t k_java_files[] = {
    {"src/demo/Store.java", "package demo;\n"
                            "public class Store {\n"
                            "    public void action(int id) {}\n"
                            "    public void action(int id, String target) {}\n"
                            "    public void action(int id, String target, boolean flag) {}\n"
                            "    public void solo() {}\n"
                            "}\n"},
    {"src/demo/Use.java", "package demo;\n"
                          "public class Use {\n"
                          "    private final Store store = new Store();\n"
                          "    void one() { store.action(1); }\n"
                          "    void two() { store.action(1, \"x\"); }\n"
                          "    void three() { store.action(1, \"x\", true); store.solo(); }\n"
                          "}\n"},
};

static const ovl_case_t k_java = {
    "java",
    k_java_files,
    2,
    "package demo.pad;\npublic class Pad%02d {\n    int v() { return %d; }\n}\n",
    "src/demo/pad/Pad%02d.java",
    {3, 4, 5},
    {"one", "two", "three"},
    6,
};

static const ovl_file_t k_kotlin_files[] = {
    {"src/demo/Store.kt", "package demo\n"
                          "class Store {\n"
                          "    fun action(id: Int) {}\n"
                          "    fun action(id: Int, target: String) {}\n"
                          "    fun action(id: Int, target: String, flag: Boolean) {}\n"
                          "    fun solo() {}\n"
                          "}\n"},
    {"src/demo/Use.kt", "package demo\n"
                        "class Use {\n"
                        "    private val store = Store()\n"
                        "    fun one() { store.action(1) }\n"
                        "    fun two() { store.action(1, \"x\") }\n"
                        "    fun three() { store.action(1, \"x\", true); store.solo() }\n"
                        "}\n"},
};

static const ovl_case_t k_kotlin = {
    "kotlin",
    k_kotlin_files,
    2,
    "package demo.pad\nclass Pad%02d {\n    fun v(): Int = %d\n}\n",
    "src/demo/pad/Pad%02d.kt",
    {3, 4, 5},
    {"one", "two", "three"},
    6,
};

static const ovl_file_t k_swift_files[] = {
    {"Sources/Demo/Store.swift", "class Store {\n"
                                 "    func action(_ id: Int) {}\n"
                                 "    func action(named: String) {}\n"
                                 "    func action(_ id: Int, to target: String) {}\n"
                                 "    func solo() {}\n"
                                 "}\n"},
    {"Sources/Demo/Use.swift", "class Use {\n"
                               "    let store = Store()\n"
                               "    func one() { store.action(1) }\n"
                               "    func two() { store.action(named: \"x\") }\n"
                               "    func three() { store.action(1, to: \"y\"); store.solo() }\n"
                               "}\n"},
};

static const ovl_case_t k_swift = {
    "swift",
    k_swift_files,
    2,
    "class Pad%02d {\n    func v() -> Int { return %d }\n}\n",
    "Sources/Demo/Pad%02d.swift",
    {2, 3, 4},
    {"one", "two", "three"},
    5,
};

TEST(overload_calls_java_sequential) {
    ASSERT_EQ(ovl_run(&k_java, false), 0);
    PASS();
}

TEST(overload_calls_java_parallel) {
    ASSERT_EQ(ovl_run(&k_java, true), 0);
    PASS();
}

TEST(overload_calls_kotlin_sequential) {
    ASSERT_EQ(ovl_run(&k_kotlin, false), 0);
    PASS();
}

TEST(overload_calls_kotlin_parallel) {
    ASSERT_EQ(ovl_run(&k_kotlin, true), 0);
    PASS();
}

TEST(overload_calls_swift_sequential) {
    ASSERT_EQ(ovl_run(&k_swift, false), 0);
    PASS();
}

TEST(overload_calls_swift_parallel) {
    ASSERT_EQ(ovl_run(&k_swift, true), 0);
    PASS();
}

/* A call whose argument count two overloads accept binds to both, with the
 * ambiguous strategy, never to one of them silently. */
TEST(overload_calls_ambiguous_binds_every_candidate) {
    static const ovl_file_t files[] = {
        {"src/demo/Store.kt", "package demo\n"
                              "class Store {\n"
                              "    fun action(id: Int) {}\n"
                              "    fun action(id: Int, target: String = \"\") {}\n"
                              "    fun action(name: String, flag: Boolean, extra: Int) {}\n"
                              "}\n"},
        {"src/demo/Use.kt", "package demo\n"
                            "class Use {\n"
                            "    private val store = Store()\n"
                            "    fun one() { store.action(1) }\n"
                            "}\n"},
    };
    char tmp[256];
    snprintf(tmp, sizeof(tmp), "/tmp/cbm_ovl_amb_XXXXXX");
    ASSERT_NOT_NULL(cbm_mkdtemp(tmp));
    ASSERT_TRUE(ovl_write(tmp, files[0].path, files[0].content));
    ASSERT_TRUE(ovl_write(tmp, files[1].path, files[1].content));
    ovl_env_t save = ovl_env_select(false);
    char db_path[512];
    snprintf(db_path, sizeof(db_path), "%s/ovl.db", tmp);
    cbm_pipeline_t *pipeline = cbm_pipeline_new(tmp, db_path, CBM_MODE_FULL);
    int rc = pipeline ? cbm_pipeline_run(pipeline) : -1;
    int to3 = -1, to4 = -1, to5 = -1, ambiguous = -1;
    if (pipeline) {
        const char *project = cbm_pipeline_project_name(pipeline);
        cbm_store_t *store = cbm_store_open_path(db_path);
        sqlite3 *db = store ? cbm_store_get_db(store) : NULL;
        if (db && project) {
            to3 = ovl_calls(db, project, "one", "action", 3);
            to4 = ovl_calls(db, project, "one", "action", 4);
            to5 = ovl_calls(db, project, "one", "action", 5);
            ambiguous = ovl_int(db,
                                "SELECT COUNT(*) FROM edges e JOIN nodes s ON s.id=e.source_id "
                                "WHERE e.project=?1 AND e.type='CALLS' AND s.name=?2 AND "
                                "json_extract(e.properties,'$.strategy')='overload_ambiguous'",
                                project, "one");
        }
        if (store) {
            cbm_store_close(store);
        }
        cbm_pipeline_free(pipeline);
    }
    ovl_env_restore(&save);
    th_rmtree(tmp);
    if (rc != 0 || to3 != 1 || to4 != 1 || to5 != 0 || ambiguous != 2) {
        fprintf(stderr, "  rc=%d ->3=%d ->4=%d ->5=%d ambiguous=%d\n", rc, to3, to4, to5,
                ambiguous);
    }
    ASSERT_EQ(rc, 0);
    ASSERT_EQ(to3, 1);
    ASSERT_EQ(to4, 1);
    ASSERT_EQ(to5, 0);
    ASSERT_EQ(ambiguous, 2);
    PASS();
}

/* ── Incremental == full ───────────────────────────────────────── */

/* Every edge of the project as "TYPE source -> target" lines with the
 * project's QN prefix removed, sorted; NULL when the database cannot be read
 * (the caller frees). */
static char *ovl_edge_set(const char *db_path) {
    cbm_store_t *store = cbm_store_open_path(db_path);
    sqlite3 *db = store ? cbm_store_get_db(store) : NULL;
    sqlite3_stmt *st = NULL;
    if (!db ||
        sqlite3_prepare_v2(db,
                           "SELECT e.type || ' ' || replace(s.qualified_name, e.project || '.', '') "
                           "|| ' -> ' || replace(t.qualified_name, e.project || '.', '') "
                           "FROM edges e JOIN nodes s ON s.id=e.source_id "
                           "JOIN nodes t ON t.id=e.target_id ORDER BY 1",
                           -1, &st, NULL) != SQLITE_OK) {
        if (store) {
            cbm_store_close(store);
        }
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
    cbm_store_close(store);
    return buf;
}

static int ovl_index(const char *repo, const char *db_path) {
    cbm_pipeline_t *pipeline = cbm_pipeline_new(repo, db_path, CBM_MODE_FULL);
    int rc = pipeline ? cbm_pipeline_run(pipeline) : -1;
    if (pipeline) {
        cbm_pipeline_free(pipeline);
    }
    return rc;
}

/* Index `files`, rewrite only `files[1]` (the caller) as `edited`, re-index
 * incrementally, and require the closure-repair route, the same edge set as a
 * fresh full index of the edited tree, and `want` among those edges. */
static int ovl_incremental_matches_full(const ovl_file_t files[2], const char *edited,
                                        const char *want) {
    char tmp[256];
    snprintf(tmp, sizeof(tmp), "/tmp/cbm_ovl_incr_XXXXXX");
    if (!cbm_mkdtemp(tmp)) {
        return 1;
    }
    char repo[300];
    snprintf(repo, sizeof(repo), "%s/repo", tmp);
    char inc_db[400];
    char full_db[400];
    snprintf(inc_db, sizeof(inc_db), "%s/inc.db", tmp);
    snprintf(full_db, sizeof(full_db), "%s/full.db", tmp);
    ovl_env_t save = ovl_env_select(false);
    int rc = 1;
    char *inc = NULL;
    char *full = NULL;
    int route = -1;
    if (ovl_write(repo, files[0].path, files[0].content) &&
        ovl_write(repo, files[1].path, files[1].content) && ovl_index(repo, inc_db) == 0 &&
        ovl_write(repo, files[1].path, edited)) {
        cbm_pipeline_incremental_test_reset_faults();
        if (ovl_index(repo, inc_db) == 0) {
            route = (int)cbm_pipeline_incremental_test_last_route();
            if (ovl_index(repo, full_db) == 0) {
                inc = ovl_edge_set(inc_db);
                full = ovl_edge_set(full_db);
            }
        }
    }
    ovl_env_restore(&save);
    if (inc && full && strcmp(inc, full) == 0 && strstr(full, want) &&
        route == (int)CBM_INCREMENTAL_ROUTE_CLOSURE_REPAIR) {
        rc = 0;
    } else {
        fprintf(stderr, "  route %d (want %d), want edge [%s]\n--- incremental\n%s--- full\n%s",
                route, (int)CBM_INCREMENTAL_ROUTE_CLOSURE_REPAIR, want, inc ? inc : "(null)",
                full ? full : "(null)");
    }
    free(inc);
    free(full);
    th_rmtree(tmp);
    return rc;
}

/* The reviewer's case: an edit to the caller file alone re-resolves its calls
 * against proxies of the unchanged overloads, which must bind exactly as a
 * full index does (each call to the member its arguments fit). */
TEST(overload_incremental_java_matches_full) {
    static const ovl_file_t files[] = {
        {"src/demo/Foo.java", "package demo;\n"
                              "public class Foo {\n"
                              "    public void m(int a) {}\n"
                              "    public void m(String s) {}\n"
                              "    public void m(int a, int b) {}\n"
                              "}\n"},
        {"src/demo/Caller.java", "package demo;\n"
                                 "public class Caller {\n"
                                 "    private final Foo f = new Foo();\n"
                                 "    void run() { f.m(1); f.m(1, 2); }\n"
                                 "}\n"},
    };
    static const char edited[] = "package demo;\n"
                                 "public class Caller {\n"
                                 "    private final Foo f = new Foo();\n"
                                 "    void run() { f.m(1); f.m(1, 2); f.m(\"s\"); }\n"
                                 "}\n";
    ASSERT_EQ(ovl_incremental_matches_full(
                  files, edited, "CALLS src.demo.Caller.run -> src.demo.Foo.m(int,int)\n"),
              0);
    PASS();
}

TEST(overload_incremental_kotlin_matches_full) {
    static const ovl_file_t files[] = {
        {"src/demo/Foo.kt", "package demo\n"
                            "class Foo {\n"
                            "    fun m(a: Int) {}\n"
                            "    fun m(s: String) {}\n"
                            "    fun m(a: Int, b: Int) {}\n"
                            "}\n"},
        {"src/demo/Caller.kt", "package demo\n"
                               "class Caller {\n"
                               "    private val f = Foo()\n"
                               "    fun run() { f.m(1); f.m(1, 2) }\n"
                               "}\n"},
    };
    static const char edited[] = "package demo\n"
                                 "class Caller {\n"
                                 "    private val f = Foo()\n"
                                 "    fun run() { f.m(1); f.m(1, 2); f.m(\"s\") }\n"
                                 "}\n";
    ASSERT_EQ(ovl_incremental_matches_full(files, edited,
                                           "CALLS src.demo.Caller.Caller.run -> "
                                           "src.demo.Foo.Foo.m(Int,Int)\n"),
              0);
    PASS();
}

TEST(overload_incremental_swift_matches_full) {
    static const ovl_file_t files[] = {
        {"Sources/Demo/Foo.swift", "class Foo {\n"
                                   "    func m(_ a: Int) {}\n"
                                   "    func m(named: String) {}\n"
                                   "    func m(_ a: Int, to b: Int) {}\n"
                                   "}\n"},
        {"Sources/Demo/Caller.swift", "class Caller {\n"
                                      "    let f = Foo()\n"
                                      "    func run() { f.m(1); f.m(1, to: 2) }\n"
                                      "}\n"},
    };
    static const char edited[] = "class Caller {\n"
                                 "    let f = Foo()\n"
                                 "    func run() { f.m(1); f.m(1, to: 2); f.m(named: \"x\") }\n"
                                 "}\n";
    ASSERT_EQ(ovl_incremental_matches_full(files, edited,
                                           "CALLS Sources.Demo.Caller.Caller.run -> "
                                           "Sources.Demo.Foo.Foo.m(named:String)\n"),
              0);
    PASS();
}

SUITE(overloads) {
    RUN_TEST(overload_shape_swift_labels);
    RUN_TEST(overload_shape_counts);
    RUN_TEST(overload_extract_java_split_keeps_plain_qns);
    RUN_TEST(overload_extract_swift_same_signature_stays_one_qn);
    RUN_TEST(overload_calls_java_sequential);
    RUN_TEST(overload_calls_java_parallel);
    RUN_TEST(overload_calls_kotlin_sequential);
    RUN_TEST(overload_calls_kotlin_parallel);
    RUN_TEST(overload_calls_swift_sequential);
    RUN_TEST(overload_calls_swift_parallel);
    RUN_TEST(overload_calls_ambiguous_binds_every_candidate);
    RUN_TEST(overload_incremental_java_matches_full);
    RUN_TEST(overload_incremental_kotlin_matches_full);
    RUN_TEST(overload_incremental_swift_matches_full);
}
