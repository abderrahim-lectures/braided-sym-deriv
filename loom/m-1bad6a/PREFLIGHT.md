# Preflight for braided-sym-deriv (2026-11-03T16:59:30Z)

| Check | Result | Detail | If it failed |
|---|---|---|---|
| pack matches the repo version (else STOP: ask the owner for a new pack) | PASS | pack v79 = repo v79 | - |
| the pack's folders are git-ignored (.git/info/exclude) | FAIL | no repository at /workspace/nucleus/work/projects/p-03b54f00731940169d85066d71c6eb04/repo/.loom/m-1bad6a/integration | append .skill/loom-*/, loom-pack/ and .loom/ to .git/info/exclude |
| git hooks installed (scope check and rules digest on every loom/* commit) | PASS | core.hooksPath set to loom-toolchain/githooks (acts only on loom/* branches) | - |
| git | PASS | git version 2.53.0 | - |
| reach the paper repo (read only; a push is tested by pushing) | PASS | da260805c920ddca0f392e2303ec18b765046295	HEAD | - |
| python3 | PASS | Python 3.12.14 | - |
| latexmk | PASS | Latexmk, John Collins, 15 June 2025. Version 4.87 | - |
| paper builds from the pack | PASS | /tmp/loom-preflight-m-1bad6a/braided-sym-deriv-v79.pdf | - |
| lake and elan (run in the directory that holds lean-toolchain) | PASS | Lake version 5.0.0-src+b35cb10 (Lean version 4.36.0-rc2) | - |
| the project's Lean toolchain has leantar (needed for lake exe cache get) | PASS | leanprover/lean4:v4.36.0-rc2 has leantar | - |
| skills match the pack (SKILLS.sha256) | PASS | ok | - |
| repository gate tools/papercheck.py present | PASS | /workspace/nucleus/work/projects/p-03b54f00731940169d85066d71c6eb04/repo/.loom/m-1bad6a/integration/tools/papercheck.py | - |
| the pack files match manifest.sha256 | PASS | ok | - |
| uvx (the platform has none; the pack uses a venv instead) | FAIL | uvx is not installed | use python3 -m venv for lean-lsp-mcp |
| plugin interpreter /usr/bin/python3 | PASS | Python 3.14.4 | - |
| git identity | PASS | review-bot | - |
| wordfreq in loom-pack/.pylib (installed here if missing) | PASS | wordfreq in loom-pack/.pylib | - |
| every skill of the pack is in .skill/ | PASS | all 14 loom skills present | - |
| the guard works (task_status returns its answer) | PASS | guard ok | - |
| network: TheoremSearch | PASS | 200 | - |
| network: Lean releases | PASS | 200 | - |
| network: Mathlib | PASS | 200 | - |
| network: TauCeti | PASS | 200 | - |
| network: Loogle | PASS | 200 | - |
| disk space (2 GB free) | PASS | ok | - |

## Answer these in loom/<model>/REPORT.md (a script cannot test them)
- Run github_status: is the paper repository connected? (If github_not_connected, stop and tell the owner.)
- Can you start sub-agents? How many at once?
- Did the platform load the `.skill/` skills (list your skills)?
- Can `plugin_start` and `mcp_connect` run? Which servers connected?
- Can you push a branch to the paper repo, and does a push wait for an approval? (Try pushing the branch loom/preflight with a one-line file.)

## Plan from the result
- Any essential FAIL: fix it or use its fallback before phase 1; name it in the report.
- No sub-agents: do the groups in order text, sources, Lean.
- No Lean toolchain: the Lean part is BLOCKED with that named blocker; do the rest.
