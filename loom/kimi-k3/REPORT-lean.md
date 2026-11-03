# REPORT-lean — model kimi-k3, pack braided-sym-deriv v79

Lean agent: this session itself. No new Lean code was needed and none was written: the task of
`loom-pack/lean/LEAN-TASK.md` is to bind the four own results, and every declaration they bind to
already exists in the tree at `main` (`da26080`). A task that needs no new proof produces a
`BINDINGS.tsv`, not a `.lean` file.

## Step 0 (loom-lean-latest)

- `lean/lean-toolchain` pins `leanprover/lean4:v4.36.0-rc2`. Checked against
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` today:
  the same string. Nothing to bump; nothing downgraded; no `lake update`, no `lake clean`.
- `lean/lake-manifest.json` pins Mathlib `bf20166d9391945becb69bd9e211b6a5383d9b78`.
- TauCeti: previous sessions established it holds only an unrelated `LeftInvariantDerivation`;
  not re-explored.
- The repo's own search: `lean/RESULTS.md` and `formalization.yaml` were read; each declaration I
  name was confirmed to exist in the tree by grep (twenty-two names, all present; the two
  `TwistedCommutative.*`-namespaced spellings printed by `lean/RESULTS.md` do **not** resolve —
  the real names lack that namespace, and this is filed in `loom/kimi-k3/ISSUES.md`).

## The four bindings

See `loom/kimi-k3/BINDINGS.tsv` (four rows, all `proved`, each with its hypothesis differences).
Positions adopted, independently and against the m-1bad6a audit (`loom/m-1bad6a/AUDIT.md`,
read in full): `prop:defect`, `cor:twisted-semiprime`, `thm:twisted-commutative` are **stronger**
than the paper's sentences (additive maps, and hypotheses dropped where the proof does not use
them); `prop:twisted` is **weaker** in one named respect — the Lean states the six witness facts
and the all-elements closures, not the paper's two set-level non-inclusion sentences as their own
theorems, and the model carries no `Ring` structure on `TW.V`. Every fact it does state is
kernel-checked. One declaration `Closures.TW_dd_twisted_all`-style for the twisted rule would
make the second witness match the first; it is an idea, not an omission, and is filed as
`PROPOSE` here and in the m-1bad6a report.

## Build and audit evidence (levels, stated exactly)

- I did **not** run `lake build` in this worktree. Earlier this session, on the identical tree
  (`main` at `da26080`), I ran the repository gate as the v80 review: `lake build` green
  (0 modules rebuilt), `lake env lean check_axioms.lean` — 173 declarations with footprints all
  inside `{propext, Classical.choice, Quot.sound}` (2 whitelisted `native_decide` sites), trust
  scan 5/5 whitelisted, `GATE: PASS`. That output is quoted in `results/review-braided-sym-deriv-v79.md`
  §6 and PR #9's body.
- The m-1bad6a run's own `lake build` (18,304 jobs) and the same 173-declaration audit are on
  record in PR #7's body; the two runs agree.

## PROPOSE (nothing of it delivered)

- `lean/RESULTS.md`: drop the nonexistent `TwistedCommutative.` namespace from two declaration
  names (filed in `ISSUES.md`).
- `lean/check_axioms.lean`: add the `BSDGeneral.*` and `Closures.TW_*` names to the audit list
  (m-1bad6a's PROPOSE 3 — I endorse it).
- One closure declaration for the twisted rule of `TW.dd`, to close the audit's one weaker row.

## Correction (same day, after the joint review)

My "twenty-two names, all present" check was a grep, not a resolution check. The review of the
joint branch showed why that is not enough: `TwistedCommutative.lean` declares `section Defect`,
and a section name is not a namespace. Verified now with the project's own environment:

```
$ lake env lean check_defect2.lean
error(lean.unknownIdentifier): Unknown identifier `Defect.prop_defect_aut`
prop_defect_aut.{u_1} {R : Type u_1} [Ring R] (α : R ≃+* R) (D : R →+ R) (hDα : ∀ (x : R), D (α x) = α (D x)) : …
error(lean.unknownIdentifier): unknown identifier `Defect.ncDefect`
```

`BINDINGS.tsv` is repaired accordingly (the two names are root level). The same misspelling sits
in m-1bad6a's `BINDINGS.tsv` and in their "#check" claim text; it is a finding in my updated
review of their integration.
