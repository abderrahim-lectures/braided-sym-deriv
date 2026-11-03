# REPORT — model kimi-k3, pack braided-sym-deriv v79

## 1. Summary

- **Model id**: `kimi-k3` (registered with `loom model --as 'Kimi K3'`; sanitised by the tool).
- **Toolchain**: v23 at `~/.loom`; `loom check` — all 10 rows PASS after installing from the project
  root's `loom-toolchain-v23.zip`.
- **Pack**: `loom-pack/` at the root, `version v79` = repository `\paperversion` 79; `TASKS.md` carries
  **one** task, T1 (reference row 15, Pierce 1982). The brief that started the run also named T2
  (abstract sentence 5) and T3 (the origins' first sources); both verdicts are PASS in `verdicts.md`,
  so both are answered in `REPORT-sources.md` as checks with evidence and no claim rows.
- **Members**: none (no sub-agents were started; the one task and the four LEAN-TASK bindings were done
  directly). Worktrees: `sources-1`, `lean-1`, `integration`.
- **BLOCKED**: none. **UNVERIFIED**: `Pierce1982` (see the source report).
- **Review written**: `loom/kimi-k3/REVIEW-m-1bad6a-integration.md` — verdict `ok with findings`
  (one bookkeeping finding: a wrong commit field in one claims row). My own branches carry no review
  yet: they are labelled `needs-review`.
- **Platform skills used**: none directly. Repository skills: `bsd-exact-algebra` and
  `paper-review-gate` (used by the v79 deep review this session, whose output feeds the T2/T3 checks);
  the `loom-*` skills of the toolchain (rules, report, git-delivery, guard, health, collaborate) guided the run.
- **Versions**: Lean `v4.36.0-rc2` (= mathlib master's current toolchain), Mathlib `bf20166d9391`.
  Nothing bumped, nothing upgraded.

## 2. Per task

### T1 [references] — `UNVERIFIED Pierce1982`

Full evidence and quotations in `loom/kimi-k3/REPORT-sources.md`. Every route was tried with its
command and answer: Crossref (DOI/book confirmed), Unpaywall (closed), OpenAlex (closed), archive.org
metadata API (no response in 18 s), SpringerLink (HTTP 200 cookie-wall HTML, no PDF). The one open
copy — an 11-page front-matter scan at a University of Naples repository — was downloaded to
`.scratch/kimi-k3/sources-1/`, its TOC and preface read myself: `3.5 Wedderburn's Structure Theorem
(p. 49)`, `4.4 The Radical of an Artinian Algebra (p. 61)`, `12.6 The Noether–Skolem Theorem
(p. 230)`, `10.7 Separable Algebras over Fields (p. 190)`. Section titles fit all four uses;
no passage was read, so the row stays `UNVERIFIED` and the citations stay untouched. The pack's
`references.tsv` was not edited (the refs tool's fetch row append breaks the pack manifest; observed
today by another model whose repair I verified — `loom refs check` is clean).

Commands and their last lines are in `REPORT-sources.md`'s table; claim row in `claims.tsv`
(`T1 · unverified · 9a50a32`).

### The Lean task (`loom-pack/lean/LEAN-TASK.md`)

`loom/kimi-k3/REPORT-lean.md` + `loom/kimi-k3/BINDINGS.tsv`: all four own results are bound to
declarations already in the tree; no new `.lean` file was needed or written. Independent-versus-audit
positions (the m-1bad6a audit, `loom/m-1bad6a/AUDIT.md`, was read in full and judged):
`prop:defect`, `cor:twisted-semiprime`, `thm:twisted-commutative` **stronger**; `prop:twisted`
**weaker** (no set-level non-inclusion theorems, no `Ring` structure on `TW.V`). Build/audit evidence
is quoted at its level: my own repository-gate run on the identical tree (`lake build` green, 173-
declaration axiom audit, trust scan 5/5, `GATE: PASS`) — the v80 review's PR #9 carries the output.

## 3. Per Lean result

No new Lean result was created. The four rows of `BINDINGS.tsv` name the existing declarations and
their axiom-footprint expectations (`{propext, Classical.choice, Quot.sound}`; `sorry` count: 0 —
none was added).

## 4. Sources

Every source opened is listed with what it said in `REPORT-sources.md` §T1 and §T3, and in
`new-references.tsv` (one row: the open front-matter scan, for the owner's `loom refs add`). The one
source that could not be read is `Pierce1982` — plainly, with the attempts.

## 5. Files changed

Must equal `git diff --name-only main...HEAD`:

```
loom/kimi-k3/BINDINGS.tsv
loom/kimi-k3/ISSUES.md
loom/kimi-k3/REPORT-lean.md
loom/kimi-k3/REPORT-sources.md
loom/kimi-k3/REPORT.md
loom/kimi-k3/REVIEW-m-1bad6a-integration.md
loom/kimi-k3/STATE.md
loom/kimi-k3/claims.tsv
loom/kimi-k3/new-references.tsv
```

No file of `paper/`, `lean/`, `pdf/`, `README.md`, `formalization.yaml` changed.

## 6. Friction

1. The toolchain moved twice mid-day (v12 → v18 → v23). This run is wholly v23; earlier work of this
   session under v12 used the session-derived id `m-1bad6a`, which collided with another model's run —
   see the loom-guard log note and my v12-era caution in `.scratch/m-1bad6a/verify/STATE-mine.md`
   (not committed). v23's named ids close that hole.
2. `loom merge` refused `main` as a base argument once (base must be a commit or another branch is
   used silently — the v23 preamble's own trap); the correct call worktree-created the integration
   branch cleanly afterward.
3. My first `loom/plugins` attempt passed a stray non-ASCII character in the `env` field of one
   `plugin_start` call; the error was `permission_denied`. Re-sent with `compute`; all four plugins run.
4. `loom merge` conflicts on `claims.tsv`/`STATE.md` when two member branches each create them;
   resolved by union (both reports' rows), as expected.

## 7. Doubts

- archive.org's lending-copy status is quoted from m-1bad6a's report, not re-established (their
  metadata item; my own curl got no response in 18 s).
- The `m-1bad6a` identity of the parallel run: the v12 derivation printed the same id for two sessions.
  Under v23 that other model registers its own name; their branch stays `m-1bad6a` and is treated as
  theirs throughout.
- PR #9 (`review/v80-citations`, the v79 deep-review fixes v80) is outside the loom branch economy:
  no `claims.tsv`, no `loom review` possible. It is labelled `needs-review` for the team.

## 8. Checks in place of the owner-only gate

- `guard_all` (this integration worktree, after the last commit): pasted below at push time.
- Pack preflight: `bash loom-pack/preflight.sh braided-sym-deriv "$PWD"` from the project root —
  output pasted below at push time.
- `loom agree loom/v79/m-1bad6a/integration`: N/A until my finding is answered (review says
  `ok with findings`; agreement converts when the commit field is fixed at a new tip).
