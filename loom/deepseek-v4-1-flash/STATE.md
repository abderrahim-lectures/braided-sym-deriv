# STATE — model deepseek-v4-1-flash (braided-sym-deriv v79)

One line per branch. Rewritten from `git worktree list`, `git branch -vv`, `git log --oneline` and
`loom/deepseek-v4-1-flash/claims.tsv`, never from memory.

| branch | worktree | tasks | last commit | status |
|---|---|---|---|---|
| loom/v79/m-1bad6a/integration | .loom/deepseek-v4-1-flash/integration | all | 27db368 | report merged, gate PASS on this branch, ready to push |
| loom/v79/m-1bad6a/sources-1 | .loom/deepseek-v4-1-flash/sources-1 | T1 | 7dda8c6 | merged, pushed |
| loom/v79/m-1bad6a/lean-1 | .loom/deepseek-v4-1-flash/lean-1 | lean task | e44f4e8 | merged, pushed |
| loom/v79/m-1bad6a/audit-1 | .loom/deepseek-v4-1-flash/audit-1 | audit | 14f18b1 | merged, pushed |

## Verified facts (checked here, not remembered)

- `main` = remote `main` = `da26080` (v79). Paper repository connected, not read-only.
- Preflight `bash loom-pack/preflight.sh braided-sym-deriv <repo> m-1bad6a`: every essential check PASS;
  the only FAIL is the optional `uvx` (fallback: `python3 -m venv`).
- Lean pair already current: `lean/lean-toolchain` = `leanprover/lean4:v4.36.0-rc2`;
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` answers the same
  string; manifest pins Mathlib `bf20166d9391`; `lean --version` = 4.36.0-rc2, `Lake 5.0.0-src`. No bump.
- `lake build` on `lean/` green before any edit: `Build completed successfully (18304 jobs).`
- Gate PDF leg `python3 tools/papercheck.py --skip-lean`: `GATE: PASS` — fresh 13 pp vs released 13 pp,
  0 overfull, 0 undefined, text identical, released label ok.
- Abstract sentence 5 is supported by Remark 2.5 (`rem:sigma-derivation-classification`): with
  `x ·_σ y = μ(x⊗y) + μ(σ(x⊗y))`, `σ = -id` gives the zero product (so every linear map is in the class)
  and `σ = -τ` gives `[x,y]` (so the class is the Lie derivations). No paper edit needed.

## Friction found here

- Three commits appeared on this branch at 16:59:22–30 (`0fe235d`, `dfec595`, `1b2f7d2`) from a process
  other than this session: a finished-looking `REPORT.md` / `REPORT-sources.md` / `claims.tsv` claiming T1
  settled as UNVERIFIED, plus a `PREFLIGHT.md` from running the pack preflight with the worktree as the
  clone argument. Their content is not this session's work and was not adopted; the files are rewritten
  here from evidence. Recorded under Friction in `REPORT.md`.

## Old sources (loom-rules 8: a source before 1990 needs its search recorded here)

- `Old source v79: Pierce1982: loom refs fetch by DOI (10.1007/978-1-4757-0163-0), by ISBN (0-387-90693-2,
  978-1-4757-0163-0) and by title, all refused or metadata-only; Crossref, Unpaywall (is_oa false), OpenAlex
  (oa_status closed), archive.org and Open Library (access-restricted lending copy), Springer (bot challenge),
  Google Books (429); one open front-matter scan read, table of contents only, no readable copy of any cited
  section found.`
- `Old source v79: Herstein1957: read in loom-pack/references/text/Jordan derivations of prime rings (1958).txt,
  p. 1104, definition and the characteristic-not-2 form, both quoted in REPORT.md section 2 (T3).`
- `Old source v79: HosseiniKarizaki2019: read in loom-pack/references/text/Functional equations characterizing
  §-derivations.txt, §1 p. 431, the sigma-derivation identity, quoted in REPORT.md section 2 (T3).`
- `Old source v79: JordanVonNeumannWigner1934, Jacobson1937, Hochschild1945, Martindale1964, Bresar1988,
  Cusack1975: not read in this run; they are the rows of the pack's own library and this run changed no
  sentence that cites them.`

## This branch

`loom/v79/deepseek-v4-1-flash/integration`, worktree `.loom/deepseek-v4-1-flash/integration`, tip `ef42ecd`.
It carries the Loom deliverable that was first recorded under the derived session id `m-1bad6a`, moved here
because toolchain v23 asks a model to name itself and because another session of this project resolved to the
same derived id. The member branches named in the table above are historical; their content is in this file
set.

`loom agree loom/v79/deepseek-v4-1-flash/integration`: **NOT AGREED — no review of this branch by another
model.** kimi-k3 did review the work, but at the old branch name (`REVIEW-m-1bad6a-integration.md`, tip
`7d3e65b`), so the gate cannot count it here; it asked for a review of this branch at its tip in return.
Its one finding (the `formalization.yaml` claim named a commit that touches only `claims.tsv`) was right
and is fixed in `1d49560`.

My side of the exchange: `REVIEW-kimi-k3-integration.md` reviews kimi-k3's branch at `09b1d3c`, verdict
`ok with findings`; the finding is that its `BINDINGS.tsv` names `Defect.prop_defect_aut` and
`Defect.prop_defect_anti`, which do not exist (`Defect` is a `section`), and the `claims.tsv` row repeats
them. `loom agree loom/v79/kimi-k3/integration` shows `deepseek-v4-1-flash | 09b1d3c | ok with findings |
open`, which is the state the rule wants until kimi-k3 answers it. `REVIEW-review-v80-citations.md`
reviews the paper branch of another model and is not gated, because `loom review` refuses `review/*`
branches.

`bash loom-pack/preflight.sh braided-sym-deriv <repo>` at the end of the run: 21 PASS and 4 FAIL, and every
FAIL is a pack-versus-toolchain skew rather than the work — `.skill/` now holds the 15 v23 skills while the
pack's SKILLS.sha256 records the v79 ones; `loom-pack/references/references.tsv` gained the recorded fetch
attempt (row 18) again from another session; the guard self-test looks for `loom-toolchain/plugins/` in the
project root, which v23 no longer creates; and `uvx` is absent (optional). Filed in `ISSUES.md`.
