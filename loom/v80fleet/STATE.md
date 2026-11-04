# STATE — model v80fleet

Run: full-width review of v81, requested 2026-11-04 ("review again and load loom skills").

| item | value |
|---|---|
| artifact under review | branch `fix/v81-paper-fixes` @ `338c593`, paper `paper/braided-sym-deriv.tex`, `\paperversion` 81 (699 lines), released `pdf/braided-sym-deriv-v81.pdf` |
| baseline | `main` @ `6919724` (v80) |
| fleet | Ultramath swarm `smw1yoi3w`, 16 members, one perspective each (loom-review-fleet), started 2026-11-04 |
| member files | `.scratch/review/v81/<perspective>.md`, one per perspective |
| merged review | `loom/v80fleet/REVIEW-paper-v81.md` (to be written) |
| report | `loom/v80fleet/REPORT.md` (to be written) |
| toolchain | loom v68, model id `v80fleet` |
| open | 16 members running; nothing merged yet |

Branches carried by this model: `fix/v81-paper-fixes` (v81 text + .gitignore, f3a8002, 338c593),
`fix/ledger-results` (4619a5e, lean/RESULTS.md repairs). Neither is pushed yet.

## Closed 2026-11-04

Fleet `smw1yoi3w` ended solved: 15 accepted, 1 abandoned (p6 citations, budget).
Merged review: `loom/v80fleet/REVIEW-paper-v81.md` (52 rows, R-01..R-54, 0 CRITICAL).
Run report: `loom/v80fleet/REPORT.md` (fix list in §4, not applied — the verdicts are at `338c593`).
Judge's own review of v80/v81: `results/review-braided-sym-deriv-v80-additional-review.md`.

## Fixes applied 2026-11-04 (owner: "apply fixes*")

Branch `fix/v82-paper-fixes` @ `03226ca` (renamed from `fix/v81-paper-fixes`; unpushed).
v82 = v81 + 13 paper lines + 3 pins + README/.gitignore + 2 gate fixes in `tools/papercheck.py`.
Gate: PASS at the tip, 14 pp, text identical. Mutation-tested: stale jobname now FAILs; scan catches
`admit` and indented `axiom`. Not applied: R-25, R-45, R-17/R-18, R-39/R-40 (reasons in REPORT §8).

## Branch reorganisation 2026-11-04 (owner: "fix and remove unrelated things")

* `fix/v82-paper-fixes` @ `eee8dd2` — paper + release only: `paper/braided-sym-deriv.tex`,
  `paper/latexmkrc`, `formalization.yaml`, README (version, changelog, pdf row), the three Lean
  version pins, `pdf/braided-sym-deriv-v8{1,2}.pdf`. `.gitignore` and `tools/papercheck.py` are back
  at `main`'s version at the tip; the history still records them and the tip reverts them.
* `fix/housekeeping` @ `22af45d` — `.gitignore` (`*.djvu`, `paper/build.log`) and the two
  `tools/papercheck.py` repairs. Gate PASS on that branch too.
* `fix/ledger-results` @ `4619a5e` — `lean/RESULTS.md` only.
* Removed from the tree: my `.scratch/djvu/` extraction, `paper/build.log`, and the `/tmp` files.
  Left alone: other sessions' untracked files and the root archives (not mine).

## Paper pruned 2026-11-04 (owner: "remove unrelated things in the paper")

`fix/v82-paper-fixes` @ `90c6fd3`: two dead passages removed — the `HH^n(A,A)` notation at line 329
(nothing after it uses it; the cocycle vocabulary around it is used in Theorem 4.1's proof) and the
closing of Remark 3.3 (`Inn_alpha`, the quotient called *twisted outer derivations*; the `ad_g`
criterion above it is kept for Example 4.5(a)). 13 pages, gate PASS, text identical to the released PDF.
