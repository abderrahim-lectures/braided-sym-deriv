# STATE — model m-1bad6a (braided-sym-deriv v79)

One line per branch. Rewritten from `git worktree list`, `git branch -vv`, `git log --oneline` and
`loom/m-1bad6a/claims.tsv`, never from memory.

| branch | worktree | tasks | last commit | status |
|---|---|---|---|---|
| loom/v79/m-1bad6a/integration | .loom/m-1bad6a/integration | all | this commit | report and claims being written |
| loom/v79/m-1bad6a/sources-1 | .loom/m-1bad6a/sources-1 | T1 | da26080 | agent running |
| loom/v79/m-1bad6a/lean-1 | .loom/m-1bad6a/lean-1 | lean task of LEAN-TASK.md | da26080 | agent running |
| loom/v79/m-1bad6a/audit-1 | .loom/m-1bad6a/audit-1 | audit of the bound results | da26080 | not started |

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
