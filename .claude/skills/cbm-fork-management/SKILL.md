---
name: cbm-fork-management
description: Use when changing our copy of codebase-memory-mcp (the lev branch on lev-os), landing a fix there, adopting an upstream issue or pull request, sending a change upstream, pulling upstream main in, or validating a change. Selectors: --status, --land, --update-from-prs, --contribute, --sync-upstream, --validate.
---

# cbm-fork-management

Our copy lives first. Upstream is a courtesy that follows its own rules. Validation is many short runs, never one long one.

## Facts

| Thing | Value |
|---|---|
| Upstream | `DeusData/codebase-memory-mcp`, remote `origin`, branch `main`. Only @DeusData merges and speaks for the project. |
| Our copy | `lev-os/codebase-memory-mcp`, remote `lev-os`, integration branch `lev`. |
| Work branches | `fix/<topic>`, `np/<topic>`, `carry/<upstream number>-<topic>`, in `.worktrees/<name>` inside this repository. |
| This skill, fast-build tools, any build or CI config we change | `lev` only. Never in a branch that goes upstream. |

Confirm the remotes with `git remote -v` before any push. Never rebase, stash, or `git add -A`. Stage named paths only.

## Rules (JP, 2026-11-13)

1. **Land in our copy at once.** A change that passed its checks and a review merges into `lev` the same day. It never waits for an upstream merge.
2. **Upstream only on request, and by the book.** Send a change upstream when the maintainer asked for it or JP said yes. Then follow `CONTRIBUTING.md` on `origin/main` to the letter; re-read it each time.
3. **Adopt what we agree with.** Open upstream issues and pull requests that fix a fault we measure get carried into `lev` and tested here, with or without an upstream merge.
4. **Fork-only means fork-only.** Anything that changes build config, CI, scripts or agent files for our own speed stays on `lev`.
5. **No prayer runs.** A run longer than 10 minutes starts only after runs of 1, 2 and 5 minutes passed on the same tree.

## --status

Print one table, then stop:

- `lev` against `lev-os/lev` and against `origin/main` (ahead, behind).
- Each work branch: merged into `lev` or not, pushed or not, checks run.
- Each open upstream pull request of ours: head, checks, last maintainer comment, what it waits for.
- Carried upstream items not yet merged upstream.

## --validate (the ladder)

The upstream test build compiles every source in one compiler command: one changed line costs about 15 minutes. Do not use it to iterate.

| Step | Budget | What |
|---|---|---|
| 1 | 1 min | Rebuild only changed files into objects, link, run the one test: `CBM_TEST_ONLY=<suite>:<test> <runner> <suite>`. |
| 2 | 2 min | Red proof: same test with the fix removed must fail. Swap the one production file, rebuild that object, swap back, confirm with `cmp`. |
| 3 | 5 min | The suites that cover the changed files. |
| 4 | 10 min | Neighbour suites, each as its own process, in parallel within the machine's load limit. |
| 5 | long | The wide run, once, at the final commit, only after 1 to 4 pass. Split it so no part exceeds a tool time limit. |

- Each step writes a log and a one-line result. A claim in a pull request cites a log that exists.
- Use a short private runtime folder under `/tmp` (socket paths hold 103 bytes on macOS) and a private cache folder.
- If a step exceeds its budget, stop and find out why before starting the next one.
- A reviewer that only reads cannot settle a run claim. The owner reruns every program check and every planted fault once at the final commit.

## --land `<branch>`

1. Checks: ladder steps 1 to 4 pass on the branch head.
2. Review: a fresh reader on another model reads the diff with a rubric the maker never saw. Blockers are repaired, then read again. Never approve your own work.
3. Merge into `lev`: `git merge --no-ff -s <branch>` with subject `Merge <branch>: <one plain sentence of what now works>`.
4. Ladder step 3 on the merged tree, then `git push lev-os lev`.
5. Record what landed and what it measured in the project's ledger.

A branch that also goes upstream is cut from `origin/main`, so merging it into `lev` may conflict. Resolve in the merge commit; never rewrite the branch.

## --update-from-prs

1. List candidates: `gh issue list` and `gh pr list` on upstream, open, sorted by recent activity, filtered to the languages and passes we measure.
2. For each candidate, decide **adopt**, **watch** or **skip** with one line of reason. Adopt needs a fault we can reproduce or measure here.
3. Adopt: branch `carry/<number>-<topic>` from `lev`, cherry-pick the author's commits with authorship and sign-off kept, add a failing-first test if the item has none.
4. Run `--validate`, then `--land`.
5. Keep a carry table (upstream number, our branch, landed commit, upstream state). When upstream merges the item, drop our carry at the next `--sync-upstream`.

Do not comment on another person's upstream pull request unless JP says so.

## --contribute `<branch>`

Only when rule 2 holds. Before the push, every line here is true:

- A tracking issue exists and the pull request references it (`Fixes #N`, or say plainly why it does not close it).
- One issue for each pull request. Under 500 changed lines. C only. No fork-only file in the diff.
- The branch is cut from current `origin/main`. Merge main in; never rebase a pushed branch.
- Every commit has a `Signed-off-by` that matches its author: `scripts/check-dco.sh origin/main..HEAD` passes. Another person's commit keeps their authorship and sign-off.
- Conventional subjects. No attribution trailer, no process trailer, no link to a chat or agent session, no wording about our private setup.
- The first line of the pull request text discloses the AI agent and names the accountable person.
- Every claim is checkable: the failing test on main, the command, the counts, the machine. Each number comes from a log of the final commit.
- Known limits are named. What was not run locally is named.
- Format: the project formats `src/` and headers only. Never reformat test files whole.
- The branch already landed in `lev` (rule 1), and a fresh reviewer read the final commit before the push, not after.

After opening or pushing: link the pull request in the session, then report its checks. A maintainer request becomes a new `--land` then `--contribute` round. Do not open a second pull request for a fix the maintainer did not ask to see apart.

## --sync-upstream

1. `git fetch origin`, then `git merge --no-ff -s origin/main` into `lev` on a work branch first.
2. Conflicts: read both sides and keep both meanings. A new upstream field or flag must be set by our code paths too.
3. Drop carries that upstream merged. Run `--validate` steps 3 to 5, then `--land`.

## Stop and ask JP

A new upstream pull request or comment that the maintainer did not ask for; closing an upstream item; anything from a private code base in a fixture, commit or public text; a release of our build to other people.
