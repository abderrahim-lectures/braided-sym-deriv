# REPORT-audit — statement-fidelity audit of the four Lean results, braided-sym-deriv v79

Agent `audit-1`. Worktree `.loom/m-1bad6a/audit-1`, branch `loom/v79/m-1bad6a/audit-1`.
Base commit at the start of the run: `da26080`.
The full audit, one row per result with the five required fields, is in
`loom/m-1bad6a/AUDIT.md`.

## 1. Summary

Platform skills used. `lean-statement-audit` (read at `.skill/lean-statement-audit/SKILL.md` in the
worktree): its method is the one I applied, comparing every binder with the source, expanding
project predicates that hide premises, and reporting source correspondence apart from proof status.
`loom-rules`, `loom-lean-formalize` and `loom-report` read with `cat` from `/workspace/nucleus/work/home/.loom/skills/`,
as the prompt asks; `loom-lean-formalize`'s "Statement audit" section names the same method and the
`#print axioms` step.

Tasks done: the audit of the four results that `loom-pack/lean/LEAN-TASK.md` names, `prop:defect`,
`cor:twisted-semiprime`, `thm:twisted-commutative`, `prop:twisted`. No `BLOCKED`. No `UNVERIFIED`
citation; `lean-statement-audit` has no citation to check. No extra work.

Versions. The repository pins `leanprover/lean4:v4.36.0-rc2` (`lean/lean-toolchain`) and Mathlib at
`master` (`lean/lake-manifest.json`). I did not build, so I name no built version.

Verdicts: `stronger` for rows 1 to 3, `weaker` for row 4. Counts: `same statement` 0, `stronger` 3,
`weaker` 1, `different statement` 0. No row is called a pass, and nothing here says a judge passes.

## 2. The four rows in one line each

| paper label | Lean declarations | verdict |
|---|---|---|
| `prop:defect` (Prop 3.2) | `prop_defect_aut`, `prop_defect_anti`, `BSDGeneral.bsd_iff_automorphism`, `bsd_iff_antiautomorphism`, `derivation_iff_commutes`, `AntiAutomorphism.der_twisted_iff_comm_anti` | stronger |
| `cor:twisted-semiprime` (Cor 3.5) | `BSD.corollary_3_5_unconditional`, `AntiAutomorphism.corollary_3_5_anti_unconditional` | stronger |
| `thm:twisted-commutative` (Thm 4.1) | `BSD.theorem_4_1`, `twisted_commutative`, `BSDGeneral.thm41_core` | stronger |
| `prop:twisted` (Prop 4.4) | `TW.D1_*`, `TW.dd_*`, `Closures.TW_*_all` | weaker |

The reasons, the exact types and the exact missing strength are in `AUDIT.md`, one row per result.

## 3. Sources read

- `paper/braided-sym-deriv.tex`, lines 337-347 (`prop:defect`), 436-439 (`cor:twisted-semiprime`),
  453-456 (`thm:twisted-commutative`), 531-539 (`prop:twisted`), and the definitional passages
  lines 1-300 and 300-336 (defect, twisted product, `BSDer`, reduced, semiprime, 2-torsion-free).
- `lean/Research/BraidedSymDeriv/TwistedCommutative.lean`, `General.lean`, `Paper.lean`,
  `AntiAutomorphism.lean`, `Closures.lean`, `BraidedSymmetric.lean`, `Bresar1988.lean`;
  `lean/Background/JordanHerstein.lean`.
- `lean/RESULTS.md` (statement ledger), `formalization.yaml`, `loom/m-1bad6a/BINDINGS.tsv` on branch
  `loom/v79/m-1bad6a/lean-1`.
- Mathlib `Mathlib/Algebra/GroupWithZero/Basic.lean` at `/opt/mathlib` for `IsReduced`.
- `/workspace/nucleus/work/home/.loom/skills/{loom-rules,loom-lean-formalize,loom-report}/SKILL.md`,
  `/workspace/nucleus/work/home/.loom/checks/CHECKS.md`, `claim.sh`, `scope.default.json`.

No source was unreachable, and I added no citation.

## 4. Commands run, with what came back

- `cat` of the three skill files and of `loom-pack/lean/LEAN-TASK.md`: I read them; this report does not
  reproduce them.
- `rg -n -A12 "<declaration>" lean/Research/BraidedSymDeriv/*.lean`, `sed -n` on the paper: the source
  text quoted in `AUDIT.md`.
- `rg -c "sorry|admit|native_decide"` on the six modules: five hits, all inside comments that say the
  development has none; no `sorry`, `admit` or `native_decide` in the code.
- `git -C <repo> log --oneline -3 loom/v79/m-1bad6a/lean-1`: tip `da26080`, the same commit as this
  worktree's base, so no newer Lean text was on the branch when I audited.
- `git -C <repo> show loom/v79/m-1bad6a/lean-1:loom/m-1bad6a/BINDINGS.tsv`: status `proved` for all
  four rows.
- `bash <LOOM>/checks/check-plain-prose.sh loom/m-1bad6a/AUDIT.md`: 0 antithesis findings, 0 vocabulary
  findings. `bash <LOOM>/checks/english.sh loom/m-1bad6a/AUDIT.md`: it reports long "sentences" and rare
  words, and both counts are dominated by the Lean code blocks and the formulas, which the checker reads
  as prose; I split the genuine long sentences. I did not build and did not run Lean.

## 5. Files changed

- `loom/m-1bad6a/AUDIT.md` (new): the audit, one row per result with the five fields.
- `loom/m-1bad6a/REPORT-audit.md` (this file, new).
- `loom/m-1bad6a/claims.tsv`: one appended line, through `claim.sh`.
- `loom/m-1bad6a/guard.audit-audit-1.log`: written by the guard. I did not write it.

`git diff --name-only main...HEAD` on this branch should show the first two, plus whatever the branch
base already carried. I edited no `.lean` file, no `BINDINGS.tsv` and no `RESULTS.md`.

## 6. Friction

- The platform skill `lean-statement-audit` is not under `/workspace/nucleus/work/home/.loom/skills/`, so
  reading skills with `cat` from there does not find it. It is in the worktree at
  `.skill/lean-statement-audit/SKILL.md`. That is worth a line in the toolchain's own documentation.
- The orchestrator told me to run `#print axioms` through the project's toolchain, and also not to build.
  I followed the second. The footprints I report come from the Lean agent's own
  `.scratch/m-1bad6a/lean-1/check_m1.out`, and `AUDIT.md` says so.
- `lean/lean-toolchain` pins v4.36.0-rc2 while the Mathlib source I can read on this machine is v4.33.1.
  For `IsReduced` I cross-checked against the in-tree use of `IsReduced.eq_zero`, which is the version
  that counts.

## 7. Doubts

- I did not reproduce the `#print axioms` output, so the "no `sorryAx`" reading is the Lean agent's run.
- Whether `TW.V` with `TW.mul` is the algebra `F_3[ε]/(ε^3)` is true on inspection (truncated convolution)
  and is not proved in the development. `AUDIT.md` reports that as a carrier difference, not as a defect
  of the mathematics.
- `BINDINGS.tsv` status `proved` for `prop:twisted` does not match my verdict `weaker`. I wrote that in
  `AUDIT.md` and did not edit the file, which is outside my edit list.

## PROPOSE

- `PROPOSE:` add to `Closures.lean` one declaration
  `TW_dd_twisted_all : ∀ a b : TW.V, TW.dd (TW.tmul a b) = TW.tmul (TW.dd a) b + TW.tmul a (TW.dd b)`
  by `decide` over the 81 pairs. That one declaration, plus `TW.D1_alphader_all`, `TW.D1_not_twisted`
  and `TW.dd_not_alphader`, makes Proposition 4.4 follow in the model with no further step, and removes
  the only gap I found.
- `PROPOSE:` in `RESULTS.md`, correct the names `TwistedCommutative.prop_defect_aut` and
  `TwistedCommutative.TW.D1_alphader` to `prop_defect_aut` and `TW.D1_alphader`. No namespace
  `TwistedCommutative` exists in `TwistedCommutative.lean`.
