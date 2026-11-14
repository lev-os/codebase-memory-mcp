/*
 * Regression guard for #409: an upgraded installer-owned hook must use the
 * non-blocking augmenter. The installer now recognizes owned bytes instead
 * of overwriting any file at the reserved path (#1387). First prove that the
 * old synthetic blocking script is preserved as unowned; then migrate the
 * released augmenter script and check the current search-hook wiring.
 */

#include <foundation/compat.h>
#include "test_framework.h"
#include "test_helpers.h"
#include <cli/cli.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>

/* ── Local helpers (mirror the helpers in test_cli.c) ──────────────── */

static int rp409_write_file(const char *path, const char *content) {
    FILE *f = fopen(path, "w");
    if (!f)
        return -1;
    fprintf(f, "%s", content);
    fclose(f);
    return 0;
}

static const char *rp409_read_file(const char *path) {
    static char buf[16384];
    FILE *f = fopen(path, "r");
    if (!f)
        return NULL;
    size_t n = fread(buf, 1, sizeof(buf) - 1, f);
    fclose(f);
    buf[n] = '\0';
    return buf;
}

/* Recursively create directory (simple two-level: parent + child). */
static int rp409_mkdirp(const char *path) {
    char tmp[1024];
    snprintf(tmp, sizeof(tmp), "%s", path);
    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            cbm_mkdir(tmp);
            *p = '/';
        }
    }
    return cbm_mkdir(tmp) == 0 || errno == EEXIST ? 0 : -1;
}

/* ── Test ──────────────────────────────────────────────────────────── */

/*
 * repro_issue409_install_wires_hook_augment_not_blocking_gate
 *
 * Simulates an upgrade from a pre-v0.7.0 install:
 *   - The hooks dir already contains the OLD blocking gate script
 *     (containing $PPID and exit 2).
 *   - settings.json already contains a stale CMM hook with the old matcher
 *     "Grep|Glob|Read" and an old inline command.
 *
 * After calling cbm_upsert_claude_hooks + cbm_install_hook_gate_script
 * (the actual install/update flow), asserts that:
 *   1. The gate script is OVERWRITTEN with the non-blocking shim
 *      (contains "hook-augment", does NOT contain "PPID" or "exit 2").
 *   2. settings.json PreToolUse command references "cbm-code-discovery-gate"
 *      (the shim path), not inline blocking code.
 *   3. settings.json uses the current non-blocking matcher "Grep|Glob"
 *      (not the old "Grep|Glob|Read" that was silently upgrading Read-gating
 *      behaviour).
 *
 * RED if:
 *   - The gate script still contains "PPID"  (old blocking logic not cleared)
 *   - The gate script still contains "exit 2" (old blocking exit not cleared)
 *   - The gate script does NOT contain "hook-augment" (shim not written)
 *   - settings.json does NOT contain "cbm-code-discovery-gate" (wrong command)
 *
 * Oracle used: cbm_upsert_claude_hooks(settings_path) +
 *              cbm_install_hook_gate_script(home, binary_path)
 * (the same two calls made by install_claude_code_config in cli.c).
 */
/* Keep an inherited CLAUDE_CONFIG_DIR from redirecting this fixture. */
static bool rp409_install_gate(const char *home, const char *binary) {
    const char *prior = getenv("CLAUDE_CONFIG_DIR");
    char *saved = prior ? cbm_strdup(prior) : NULL;
    if (prior && !saved)
        return false;
    char config[512];
    snprintf(config, sizeof(config), "%s/.claude", home);
    cbm_setenv("CLAUDE_CONFIG_DIR", config, 1);
    bool ok = cbm_install_hook_gate_script(home, binary);
    if (saved) {
        cbm_setenv("CLAUDE_CONFIG_DIR", saved, 1);
        free(saved);
    } else {
        cbm_unsetenv("CLAUDE_CONFIG_DIR");
    }
    return ok;
}

TEST(repro_issue409_install_wires_hook_augment_not_blocking_gate) {
    /* Create a private installation directory. */
    char tmpdir[256];
    snprintf(tmpdir, sizeof(tmpdir), "/tmp/rp409-XXXXXX");
    if (!cbm_mkdtemp(tmpdir))
        FAIL("cbm_mkdtemp failed");

    /* Create <home>/.claude/hooks/ (mirrors real Claude Code layout). */
    char hooks_dir[512];
    snprintf(hooks_dir, sizeof(hooks_dir), "%s/.claude/hooks", tmpdir);
    if (rp409_mkdirp(hooks_dir) != 0)
        FAIL("mkdirp hooks_dir failed");

    char script_path[512];
    snprintf(script_path, sizeof(script_path), "%s/cbm-code-discovery-gate", hooks_dir);
    const char *binary = "/usr/local/bin/codebase-memory-mcp";
    static const char unowned[] =
        "#!/bin/bash\n"
        "GATE=/tmp/cbm-code-discovery-gate-$PPID\n"
        "if [ -f \"$GATE\" ]; then exit 0; fi\n"
        "touch \"$GATE\"\n"
        "exit 2\n";
    ASSERT_EQ(rp409_write_file(script_path, unowned), 0);
    ASSERT_FALSE(rp409_install_gate(tmpdir, binary));
    ASSERT_STR_EQ(rp409_read_file(script_path), unowned);

    /* Exact released installer bytes, also covered by the CLI upgrade tests.
     * A hand-written approximation is deliberately not an owned document. */
    static const char released[] =
        "#!/usr/bin/env bash\n"
        "# codebase-memory-mcp search augmenter (Claude Code PreToolUse).\n"
        "# NOTE: the legacy filename is kept for zero-migration upgrades.\n"
        "# Despite the name this NEVER blocks a tool call - it only adds\n"
        "# graph context. Any failure is silent (exit 0, no output).\n"
        "BIN=\"/usr/local/bin/codebase-memory-mcp\"\n"
        "[ -x \"$BIN\" ] || exit 0\n"
        "\"$BIN\" hook-augment 2>/dev/null\n"
        "exit 0\n";
    ASSERT_EQ(rp409_write_file(script_path, released), 0);

    /* Pre-seed settings.json with a stale CMM hook entry (old matcher). */
    char settings_path[512];
    snprintf(settings_path, sizeof(settings_path),
             "%s/.claude/settings.json", tmpdir);
    rp409_write_file(settings_path,
        "{\"hooks\":{\"PreToolUse\":["
        "{\"matcher\":\"Grep|Glob|Read\","
        "\"hooks\":[{\"type\":\"command\","
        "\"command\":\"~/.claude/hooks/cbm-code-discovery-gate\"}]}]}}");

    /* Run the actual install/update hook wiring (same two calls as
     * install_claude_code_config in src/cli/cli.c lines 3045-3046). */
    int rc = cbm_upsert_claude_hooks(settings_path);
    ASSERT_EQ(rc, 0);
    ASSERT_TRUE(rp409_install_gate(tmpdir, binary));
#ifdef _WIN32
    snprintf(script_path, sizeof(script_path), "%s/cbm-code-discovery-gate.cmd", hooks_dir);
#endif

    /* ── Assert the gate script was OVERWRITTEN with the non-blocking shim ── */
    const char *script_data = rp409_read_file(script_path);
    ASSERT_NOT_NULL(script_data);
    ASSERT_STR_NEQ(script_data, released);

    /* MUST NOT contain $PPID: the old blocking gate used
     * /tmp/cbm-code-discovery-gate-$PPID as a per-invocation state file.
     * If present, the blocking gate was not overwritten -> RED for #409. */
    ASSERT(strstr(script_data, "PPID") == NULL);

    /* MUST NOT contain "exit 2": the old gate blocked tool calls with exit 2.
     * If present, the installer still emits the blocking exit code -> RED. */
    ASSERT(strstr(script_data, "exit 2") == NULL);

    /* MUST contain "hook-augment": the non-blocking shim delegates to the
     * compiled augmenter via `"$BIN" hook-augment 2>/dev/null`.
     * If absent, install did not write the correct shim -> RED for #409. */
    ASSERT(strstr(script_data, "hook-augment") != NULL);

    /* ── Assert settings.json was updated to the correct non-blocking config ── */
    const char *settings_data = rp409_read_file(settings_path);
    ASSERT_NOT_NULL(settings_data);

    /* The PreToolUse command must reference the shim (by its well-known name),
     * not an inline blocking script. */
    ASSERT(strstr(settings_data, "cbm-code-discovery-gate") != NULL);

    /* The old "Grep|Glob|Read" matcher (which gated Read calls, breaking
     * the read-before-edit invariant per issue #362) must have been replaced
     * with the current "Grep|Glob|Bash" search matcher. */
    ASSERT(strstr(settings_data, "\"Grep|Glob|Bash\"") != NULL);
    ASSERT(strstr(settings_data, "Glob|Read") == NULL);

    th_rmtree(tmpdir);
    PASS();
}

/* ── Suite ──────────────────────────────────────────────────────────── */
SUITE(repro_issue409) {
    RUN_TEST(repro_issue409_install_wires_hook_augment_not_blocking_gate);
}
