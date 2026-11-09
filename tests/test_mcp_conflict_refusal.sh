#!/usr/bin/env bash
# A new MCP session next to a daemon of a DIFFERENT build must answer MCP with
# the reason, and soon: clients give up on `initialize` after a few seconds
# (Codex after 10 s by default). The session waits at most
# MAIN_MCP_CONFLICT_WAIT_MS (5 s) for the other build to leave, then answers
# initialize with the reason as instructions and every tools/call as a tool
# error carrying it. Requires a TEST_SEAMS=1 binary: CBM_TEST_MCP_CLIENT_BUILD
# forces the client fingerprint.
#
# Local-only, like tests/test_hook_conflict_notice.sh: on upstream CI legs a
# forced fingerprint has been seen to join without a cohort conflict. Run it by
# hand:  make -f Makefile.cbm cbm TEST_SEAMS=1 && bash tests/test_mcp_conflict_refusal.sh
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BINARY="${CBM_TEST_BINARY:-${ROOT}/build/c/codebase-memory-mcp}"
if [[ ! -x "${BINARY}" && -x "${BINARY}.exe" ]]; then
  BINARY="${BINARY}.exe"
fi
if [[ ! -x "${BINARY}" ]]; then
  echo "missing binary: ${BINARY}" >&2
  exit 2
fi
if ! LC_ALL=C grep -a -q -F 'CBM_TEST_MCP_CLIENT_BUILD' "${BINARY}"; then
  echo "binary lacks the MCP-client build seam: ${BINARY}" >&2
  echo "  rebuild it with:  make -f Makefile.cbm cbm TEST_SEAMS=1" >&2
  exit 2
fi

# shellcheck source=../scripts/test-runtime.sh
source "${ROOT}/scripts/test-runtime.sh"
cbm_test_runtime_init
tmpdir="${CBM_TEST_RUNTIME_ROOT}"
cleanup() {
  CBM_CACHE_DIR="${tmpdir}/cache" "${BINARY}" daemon stop >/dev/null 2>&1 || true
  cbm_test_runtime_cleanup "${BINARY}"
}
trap cleanup EXIT

if ! CBM_CACHE_DIR="${tmpdir}/cache" "${BINARY}" daemon start >"${tmpdir}/daemon-start.log" 2>&1; then
  echo "daemon start failed on this host - cannot exercise the conflict path" >&2
  cat "${tmpdir}/daemon-start.log" >&2
  exit 2
fi

forced_build="eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
requests='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"conflict-test","version":"1"}}}
{"jsonrpc":"2.0","method":"notifications/initialized"}
{"jsonrpc":"2.0","id":2,"method":"tools/list"}
{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"list_projects","arguments":{}}}'

# The daemon's cohort join completes asynchronously after `daemon start`
# returns: retry until a session observes the conflict, with a bounded backstop.
out=""
elapsed=0
for _attempt in $(seq 1 10); do
  start=${SECONDS}
  set +e
  out="$(printf '%s\n' "${requests}" | CBM_CACHE_DIR="${tmpdir}/cache" \
    CBM_TEST_MCP_CLIENT_BUILD="${forced_build}" \
    "${BINARY}" 2>"${tmpdir}/session.err")"
  rc=$?
  set -e
  elapsed=$((SECONDS - start))
  if grep -q "conflicting CBM process" "${tmpdir}/session.err"; then
    break
  fi
  sleep 0.5
done

if ! grep -q "conflicting CBM process" "${tmpdir}/session.err"; then
  echo "no session observed the build conflict - the daemon cohort never became active" >&2
  cat "${tmpdir}/session.err" >&2
  CBM_CACHE_DIR="${tmpdir}/cache" "${BINARY}" daemon status >&2 2>&1 || true
  exit 2
fi
fail() {
  echo "$1" >&2
  echo "--- stdout ---" >&2
  printf '%s\n' "${out}" >&2
  echo "--- stderr ---" >&2
  cat "${tmpdir}/session.err" >&2
  exit 1
}
[[ ${rc} -ne 0 ]] || fail "a refused session must exit non-zero; got 0"
# 5 s wait, plus process start and the remedy probe; 30 s was the old wait.
[[ ${elapsed} -le 12 ]] || fail "the refusal took ${elapsed} s; it must come within the 5 s window"
init="$(printf '%s\n' "${out}" | grep '"id":1' || true)"
list="$(printf '%s\n' "${out}" | grep '"id":2' || true)"
call="$(printf '%s\n' "${out}" | grep '"id":3' || true)"
printf '%s' "${init}" | grep -q 'is unavailable in this session' ||
  fail "initialize must carry the reason as instructions"
printf '%s' "${list}" | grep -q 'cbm_unavailable' ||
  fail "tools/list must offer only cbm_unavailable"
printf '%s' "${call}" | grep -q '"isError":true' || fail "tools/call must be a tool error"
printf '%s' "${call}" | grep -q 'conflicting CBM process' || fail "tools/call must carry the reason"
printf '%s' "${call}" | grep -q 'daemon stop' || fail "the reason must name the way out"
echo "mcp conflict refusal: answered in ${elapsed} s with the reason"
