/*
 * test_kotlin_library_receivers.c — a Kotlin member call on a library
 * receiver never binds by name to a same-named project method.
 *
 * When the Kotlin LSP cannot bind a member call, the registry's name guess
 * (unique_name / suffix_match) used to attach it to any project method that
 * shares the leaf: `lifecycleScope.launch {}` (the kotlinx.coroutines builder)
 * became a call of a project ScreenModel.launch, and
 * `progressDialog?.dismiss()` a call of an unrelated project `dismiss`. Two
 * pieces of evidence now refuse that guess:
 *   - the file imports the leaf name from a package the tree does not declare
 *     (`import kotlinx.coroutines.launch`);
 *   - the cross-file Kotlin LSP typed the receiver as a type no project type
 *     names (`pd: ProgressDialog?`, `scope: CoroutineScope`).
 * Real project receivers keep their edges: a typed `vm.launch {}`, a bare
 * `launch {}` inside a subclass, and a project extension function called on a
 * library-typed receiver (`word.shout()` with `fun String.shout()`). The
 * fixture is padded past MIN_FILES_FOR_PARALLEL and indexed through both
 * resolvers.
 */
#include "../src/foundation/compat.h"
#include "test_framework.h"
#include "test_helpers.h"
#include "pipeline/pipeline.h"
#include "sqlite3.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *const KLR_FILES[][2] = {
    {"src/main/kotlin/com/acme/vm/ScreenModel.kt",
     "package com.acme.vm\n\nabstract class ScreenModel {\n"
     "    fun launch(block: () -> Unit): Int = 1\n}\n\n"
     "class HomeVm : ScreenModel() {\n    fun load(): Int = launch { }\n}\n"},
    {"src/main/kotlin/com/acme/ui/Holder.kt",
     "package com.acme.ui\n\nclass Holder {\n    fun dismiss(): Int = 0\n}\n"},
    /* A project extension on a library type stays callable on it. */
    {"src/main/kotlin/com/acme/text/Words.kt",
     "package com.acme.text\n\nfun String.shout(): String = this + \"!\"\n"},
    {"src/main/kotlin/com/acme/text/Use.kt",
     "package com.acme.text\n\nclass Use(private val word: String) {\n"
     "    fun loud(): String = word.shout()\n}\n"},
    {"src/main/kotlin/com/acme/screen/Screen.kt",
     "package com.acme.screen\n\nimport android.app.ProgressDialog\n"
     "import androidx.lifecycle.lifecycleScope\nimport com.acme.vm.ScreenModel\n"
     "import kotlinx.coroutines.CoroutineScope\nimport kotlinx.coroutines.launch\n\n"
     "class Screen(private val scope: CoroutineScope, private val vm: ScreenModel) {\n"
     "    private var pd: ProgressDialog? = null\n\n"
     "    fun start() {\n        lifecycleScope.launch { }\n    }\n\n"
     "    fun startTyped() {\n        scope.launch { }\n    }\n\n"
     "    fun close() {\n        pd?.dismiss()\n    }\n\n"
     "    fun real(): Int = vm.launch { }\n}\n"},
};

/* CALLS edges whose source QN ends in `.<src_tail>` onto a node named
 * `leaf`; the target QNs go to out, one per line. */
static int klr_targets(sqlite3 *db, const char *src_tail, const char *leaf, char *out,
                       size_t cap) {
    out[0] = '\0';
    static const char sql[] =
        "SELECT t.qualified_name FROM edges e JOIN nodes s ON s.id = e.source_id "
        "JOIN nodes t ON t.id = e.target_id WHERE e.type = 'CALLS' "
        "AND s.qualified_name LIKE '%.' || ?1 AND t.name = ?2 ORDER BY 1";
    sqlite3_stmt *st = NULL;
    if (sqlite3_prepare_v2(db, sql, -1, &st, NULL) != SQLITE_OK) {
        return -1;
    }
    sqlite3_bind_text(st, 1, src_tail, -1, SQLITE_STATIC);
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

static int klr_expect_none(sqlite3 *db, const char *venue, const char *src_tail,
                           const char *leaf) {
    char got[1024];
    int n = klr_targets(db, src_tail, leaf, got, sizeof(got));
    if (n == 0) {
        return 1;
    }
    printf("\n  [%s] %s -> %s: want no edge, have %d:\n%s", venue, src_tail, leaf, n, got);
    return 0;
}

static int klr_expect_one(sqlite3 *db, const char *venue, const char *src_tail, const char *leaf,
                          const char *want_tail) {
    char got[1024];
    int n = klr_targets(db, src_tail, leaf, got, sizeof(got));
    size_t gl = strlen(got);
    size_t wl = strlen(want_tail);
    if (n == 1 && gl > wl + 1 && got[gl - wl - 2] == '.' &&
        strncmp(got + gl - wl - 1, want_tail, wl) == 0) {
        return 1;
    }
    printf("\n  [%s] %s -> %s: want one edge to ...%s, have %d:\n%s", venue, src_tail, leaf,
           want_tail, n, got);
    return 0;
}

static int klr_index(const char *dir, const char *db_name, bool single_thread, char *db_out,
                     size_t cap) {
    snprintf(db_out, cap, "%s/%s", dir, db_name);
    char *old_single = getenv("CBM_INDEX_SINGLE_THREAD");
    char *saved_single = old_single ? strdup(old_single) : NULL;
    char *old_workers = getenv("CBM_WORKERS");
    char *saved_workers = old_workers ? strdup(old_workers) : NULL;
    if (single_thread) {
        cbm_setenv("CBM_INDEX_SINGLE_THREAD", "1", 1);
    } else {
        cbm_unsetenv("CBM_INDEX_SINGLE_THREAD");
        cbm_setenv("CBM_WORKERS", "4", 1);
    }
    int rc = -1;
    cbm_pipeline_t *p = cbm_pipeline_new(dir, db_out, CBM_MODE_FULL);
    if (p) {
        rc = cbm_pipeline_run(p);
        cbm_pipeline_free(p);
    }
    if (saved_single) {
        cbm_setenv("CBM_INDEX_SINGLE_THREAD", saved_single, 1);
        free(saved_single);
    } else {
        cbm_unsetenv("CBM_INDEX_SINGLE_THREAD");
    }
    if (saved_workers) {
        cbm_setenv("CBM_WORKERS", saved_workers, 1);
        free(saved_workers);
    } else {
        cbm_unsetenv("CBM_WORKERS");
    }
    return rc;
}

static int klr_check_venue(const char *dir, const char *venue, bool single_thread) {
    char db_path[512];
    char name[64];
    snprintf(name, sizeof(name), "klr-%s.db", venue);
    if (klr_index(dir, name, single_thread, db_path, sizeof(db_path)) != 0) {
        printf("\n  [%s] index failed\n", venue);
        return 0;
    }
    sqlite3 *db = NULL;
    if (sqlite3_open_v2(db_path, &db, SQLITE_OPEN_READONLY, NULL) != SQLITE_OK) {
        if (db) {
            sqlite3_close(db);
        }
        return 0;
    }
    int ok = 1;
    /* Untyped receiver, leaf imported from a library package. */
    ok &= klr_expect_none(db, venue, "Screen.start", "launch");
    /* Receivers the LSP typed as library types. */
    ok &= klr_expect_none(db, venue, "Screen.startTyped", "launch");
    ok &= klr_expect_none(db, venue, "Screen.close", "dismiss");
    /* Project receivers keep their edges. */
    ok &= klr_expect_one(db, venue, "Screen.real", "launch", "ScreenModel.launch");
    ok &= klr_expect_one(db, venue, "HomeVm.load", "launch", "ScreenModel.launch");
    ok &= klr_expect_one(db, venue, "Use.loud", "shout", "Words.shout");
    sqlite3_close(db);
    return ok;
}

TEST(kotlin_library_receiver_never_binds_project_method_both_venues) {
    char *dir = th_mktempdir("cbm_kt_lib_recv");
    ASSERT_NOT_NULL(dir);
    int wrote = 0;
    for (size_t i = 0; i < sizeof(KLR_FILES) / sizeof(KLR_FILES[0]); i++) {
        wrote |= th_write_file(TH_PATH(dir, KLR_FILES[i][0]), KLR_FILES[i][1]);
    }
    /* Past MIN_FILES_FOR_PARALLEL (50): the parallel venue is selected. */
    for (int i = 0; i < 55 && wrote == 0; i++) {
        char rel[96];
        char body[128];
        snprintf(rel, sizeof(rel), "src/main/kotlin/com/acme/pad/Pad%d.kt", i);
        snprintf(body, sizeof(body),
                 "package com.acme.pad\n\nclass Pad%d {\n    fun v%d(): Int = %d\n}\n", i, i, i);
        wrote |= th_write_file(TH_PATH(dir, rel), body);
    }
    if (wrote != 0) {
        th_cleanup(dir);
        FAIL("fixture");
    }
    int seq = klr_check_venue(dir, "seq", true);
    int par = klr_check_venue(dir, "par", false);
    th_cleanup(dir);
    ASSERT_TRUE(seq);
    ASSERT_TRUE(par);
    PASS();
}

SUITE(kotlin_library_receivers) {
    RUN_TEST(kotlin_library_receiver_never_binds_project_method_both_venues);
}
