# REPORT-lean — lean-1, model m-1bad6a, branch `loom/v79/m-1bad6a/lean-1`

Task: the Lean task of `loom-pack/lean/LEAN-TASK.md`, worked in the worktree
`/workspace/nucleus/work/projects/p-03b54f00731940169d85066d71c6eb04/repo/.loom/m-1bad6a/lean-1`.
That task has two halves. Step 0 is the version bump; the second half is to bind the
four own results. The orchestrator settled step 0 on evidence, and I re-checked it here.

No new Lean declaration was written. The four results already have declarations in
the tree, and this run binds them and audits them. Rule 14 forbids adding anything else.

## 1. Summary

* Skills read in full, with `cat`: `loom-rules`, `loom-lean-latest`,
  `loom-lean-formalize`, `loom-report`, `loom-git-delivery`. Then `LEAN-TASK.md`.
* Optional platform skills: none used. `lean-elaboration` was not needed (no
  heartbeat or timing problem: the whole build replays in seconds).
  `lean-statement-audit` was not run as a separate skill; the statement comparison
  in section 3 is mine, done against `paper/braided-sym-deriv.tex`. I did not write
  the statements I audited, so the independence the skill asks for holds.
* Versions, all re-checked in this session:
  * `lean/lean-toolchain` reads `leanprover/lean4:v4.36.0-rc2`.
  * `lean --version` in `lean/` answers `Lean (version 4.36.0-rc2, x86_64-unknown-linux-gnu, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)`; `lake --version` answers `Lake 5.0.0-src+b35cb10 (Lean version 4.36.0-rc2)`.
  * `curl -sS https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` answers `leanprover/lean4:v4.36.0-rc2`, the same pin.
  * `lean/lake-manifest.json` pins Mathlib at `bf20166d9391` from `https://github.com/leanprover-community/mathlib4`.
  * So the repository already sits on Mathlib's current pair. Nothing to bump. I ran no
    `lake update`, no `lake clean`, no dependency change. No `lean-toolchain` or
    `lakefile.toml` edit.
* Settings: `sandbox` is the worktree only. Build cache linked as instructed:
  `ln -s <repo>/lean/.lake <worktree>/lean/.lake` (7.7 GB, project-root cache).
* `BLOCKED`: none. `UNVERIFIED`: none for the four rows. Three `PROPOSE:` items in
  section 8.
* I did not run the full gate `tools/papercheck.py` (it also forces a LaTeX rebuild);
  I ran its two Lean legs, `lake-build.sh` and `check_axioms.lean`.

## 2. The four rows

Every row below was checked with the same two commands, run from the worktree:

```
cd <worktree>/lean && lake env lean <scratch>/check_m1.lean     # #check + #print axioms of every bound declaration
cd <worktree>/lean && lake env lean check_axioms.lean           # the repository's axiom audit
```

`<worktree>` is `.../repo/.loom/m-1bad6a/lean-1` and `<scratch>` is
`.../repo/.scratch/m-1bad6a/lean-1` (the scratch tree, so no check file enters the
worktree). Both commands exited 0. The ledger is `loom/m-1bad6a/BINDINGS.tsv`.

### 2.1 `prop:defect` (paper Prop 3.2, `paper/braided-sym-deriv.tex` lines 337–378)

Paper: unital associative `K`-algebra `A`, `alpha` an involutive automorphism or
anti-automorphism, `D` linear with `D alpha = alpha D`; (i) automorphism case,
`D in BSDer` iff `E_D(x,y) + alpha(E_D(y,x)) = 0` for all `x,y`; (ii) anti case,
`E_D(x,y) + alpha(E_D(x,y)) = 0`; and in both cases every derivation commuting with
`alpha` lies in the class.

Lean declarations (all exist, all `#check`ed):

* `BSDGeneral.bsd_iff_automorphism` — case (i).
* `BSDGeneral.bsd_iff_antiautomorphism` — case (ii).
* `BSDGeneral.residual_automorphism`, `BSDGeneral.residual_antiautomorphism` — the two
  residual identities displayed after the proof, with no hypothesis on the relation of
  `D` and `alpha`.
* `BSDGeneral.derivation_iff_commutes` — the paper's last sentence in the sharp form
  (a derivation satisfies the twisted rule iff it commutes with `alpha`).
* `BSDGeneral.cocycle` — the cocycle identity the paper uses.
* `prop_defect_aut`, `prop_defect_anti` (root namespace, `TwistedCommutative.lean`) —
  the same two iff statements with `alpha : R ≃+* R`.

Axiom footprint: `propext, Classical.choice, Quot.sound` for six of the seven;
`BSDGeneral.cocycle` rests on `propext` only. Evidence: my `#print axioms` run.
`BSDGeneral` is **not** in `lean/check_axioms.lean`; `prop_defect_aut` and
`prop_defect_anti` are, with the same footprint.

Hypotheses: the paper's are matched, and the Lean is stronger in two ways. Maps are
additive (`A →+ A`) instead of `K`-linear, which is a strengthening. `alpha` need not be
involutive and need not be bijective; neither property is used. The status stays
`proved`.

### 2.2 `cor:twisted-semiprime` (paper Cor 3.5, line 436)

Paper: `A` 2-torsion-free semiprime `K`-algebra, `alpha` an involutive `K`-algebra
automorphism or anti-automorphism, then
`BSDer_{sigma_alpha}(A)^alpha` meet `JDer(A)` equals `Der(A)^alpha`.

Lean declarations:

* `BSD.corollary_3_5_unconditional` — `(BSD.TwistedAlpha alpha D ∧ BSD.JDer D) ↔ BSD.Der D` for `h2 : Background.JordanHerstein.TwoTorsionFree A`, `hs : Background.JordanHerstein.SemiprimeRing A`, `alpha : A ≃+* A` with `alpha (alpha x) = x`, and `hDalpha : BSD.Comm D alpha`.
* `AntiAutomorphism.corollary_3_5_anti_unconditional` — the anti-automorphism half,
  `alpha : R ≃+ R` with `alpha (x*y) = alpha y * alpha x` and `alpha 1 = 1`.

The `hDalpha` hypothesis is standing, so the statement is the paper's set equality read
inside the class of maps commuting with `alpha`; that is exactly what the `^alpha`
superscript means. Axiom footprint: `propext, Classical.choice, Quot.sound` for both,
from the repository audit (lines for both names are in its output).

Hypotheses: the paper's two hypotheses are present and named as in the paper. The Lean
is stronger in two ways: additive maps, and the anti-automorphism half assumes no
involution at all, while the paper assumes `alpha` involutive. The paper's cited
Brešar 1988 Theorem 1 is proved in the tree (`Bresar1988.bresar1988Theorem1_holds`), so
no `hBresar` hypothesis remains. The conditional forms `BSD.corollary_3_5` and
`AntiAutomorphism.corollary_3_5_anti` are kept for reference and are not what this row
binds. Status `proved`.

### 2.3 `thm:twisted-commutative` (paper Thm 4.1, line 453; proof lines 460–494)

Paper: commutative reduced `K`-algebra with `2` invertible in `K`, `alpha` an involutive
automorphism, then `BSDer_{sigma_alpha}(A)^alpha = Der(A)^alpha`.

Lean declarations:

* `BSD.theorem_4_1` — `BSD.TwistedAlpha alpha D ↔ BSD.Der D` for `[CommRing A] [IsReduced A]`, `alpha : A ≃+* A` with `alpha (alpha x) = x`, `D : A →+ A`, `h2 : IsUnit (2 : A)`, `hDalpha : BSD.Comm D alpha`.
* `twisted_commutative` — the one-way kernel proof that `theorem_4_1` calls.
* `BSDGeneral.thm41_core` — the sharpened statement of the proof (arbitrary ring,
  symmetric defect, `2`-torsion-free, no nonzero square-zero `z` in `A_-`), which is the
  form Remark 4.6 falsifies. This is a separate row in `lean/RESULTS.md`.

Axiom footprint: `propext, Classical.choice, Quot.sound` for all three.
`BSD.theorem_4_1` and `twisted_commutative` are in the repository audit;
`BSDGeneral.thm41_core` is not, and I audited it in my own run (same footprint).

Hypotheses, stated exactly as the orchestrator asked. Against the paper's **theorem
sentence** the hypotheses match: commutative, reduced, `2` invertible, `alpha` an
involutive automorphism. Two rendering differences, neither a weakening:

1. `D : A →+ A` is additive rather than `K`-linear (a strengthening).
2. `IsUnit (2 : A)` rather than "`2` invertible in `K`". For a `K`-algebra the paper's
   hypothesis implies this one, and this is the form the proof uses.

Against the paper's **sharpened** statement inside the proof, `[IsReduced A]` is
strictly stronger, since the sharpened hypothesis is "no nonzero `z` in `A_-` has
`z^2 = 0`". `lean/RESULTS.md` records this difference against the sharpened statement,
not against the theorem's sentence. Following the instruction, the status is not
lowered for it, and it is stated here and in the `notes` column. Status `proved`.

### 2.4 `prop:twisted` (paper Prop 4.4, line 531)

Paper: `A = F_3[eps]/(eps^3)`, `alpha(eps) = -eps`; then `ADer(A)` is not contained in
`BSDer_{sigma_alpha}(A)^alpha` and the class is not contained in `ADer(A)`.

Lean declarations (`TwistedCommutative.lean`, namespaces `TW` and `Closures`):

* `TW.D1_alphader`, `TW.D1_not_twisted`, `TW.D1_comm_alpha` — `D1` (kills `1`, fixes
  `eps` and `eps^2`) is an `alpha`-derivation, commutes with `alpha`, and fails the
  twisted rule at `(eps, eps)`.
* `TW.dd_der`, `TW.dd_not_alphader`, `TW.dd_comm_alpha` — `dd(eps^i) = i eps^i` is a
  derivation, commutes with `alpha`, and fails the `alpha`-derivation rule at
  `(eps, eps)`.
* `Closures.TW_D1_alphader_all`, `Closures.TW_dd_der_all`,
  `Closures.TW_D1_comm_alpha_all`, `Closures.TW_dd_comm_alpha_all` — the four statements
  over all 81 pairs, closing the basis-pair gap of the first list.

Axiom footprint: `propext, Classical.choice, Quot.sound` for all ten, from my own run
(`TW` and `Closures` are not in `lean/check_axioms.lean`; `Closures.lean` prints its own
footprints when it compiles). The two `not` facts use kernel `decide` on the finite
type, no `native_decide`.

Hypotheses: the model is `TW.V = Fin 3 → ZMod 3` with `TW.mul` the convolution
truncated at degree 2, which is `F_3[eps]/(eps^3)` by direct reading of the definition;
`TW.alpha` negates the `eps` coordinate only, as the paper's `alpha` does. The Lean
states the two **witnesses**, not a set-theoretic non-inclusion sentence. The
`dd` membership in the twisted class is a one-line deduction from `dd_der`,
`dd_comm_alpha` and the proved `der_twisted_iff_comm`; it is not a separate
declaration. Both non-inclusions follow from the facts above with no gap, so the status
is `proved`.

## 3. Build, audit, `sorry` count

Build, only through the repository script, after linking the cache:

```
bash <LOOM>/checks/lake-build.sh <worktree>/lean
...
Build completed successfully (18304 jobs).
```

First run 3.3 s wall (every job replayed from the linked cache), the capture run 65 s.
No `error:` line and no "declaration uses `sorry`" line in the log. A grep of
`Research/` and `Background/` finds no `sorry`, no `admit` and no `axiom` declaration;
the only hits are docstrings that say the files have none.

Axiom audit, as the repository runs it:

```
cd <worktree>/lean && lake env lean check_axioms.lean
```

Exit 0, 2.4 s, 187 output lines, 179 `#print axioms` lines in the file. 173 footprints
plus 6 declarations with no axioms. Every footprint is inside
`{propext, Classical.choice, Quot.sound}`, except the two known `Triangular.lean`
`native_decide` theorems. There is no `sorryAx` anywhere. Last lines of the audit:

```
'tau_isLieDerivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'kerBaseChangeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'finrank_ker_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuaternionConjug.class_is_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuaternionConjug.adI_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuaternionConjug.conj_conjugacy' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuaternionConjug.reduced_imp_semiprime' does not depend on any axioms
```

The audit lines for the four rows, verbatim:

```
'prop_defect_aut' depends on axioms: [propext, Classical.choice, Quot.sound]
'prop_defect_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSD.corollary_3_5_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'AntiAutomorphism.corollary_3_5_anti_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSD.theorem_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'twisted_commutative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

From my own check file, for the declarations the repository audit leaves out:

```
'BSDGeneral.residual_automorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSDGeneral.residual_antiautomorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSDGeneral.bsd_iff_automorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSDGeneral.bsd_iff_antiautomorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSDGeneral.derivation_iff_commutes' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSDGeneral.cocycle' depends on axioms: [propext]
'BSDGeneral.thm41_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.D1_comm_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.D1_alphader' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.D1_not_twisted' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.dd_comm_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.dd_der' depends on axioms: [propext, Classical.choice, Quot.sound]
'TW.dd_not_alphader' depends on axioms: [propext, Classical.choice, Quot.sound]
'Closures.TW_D1_comm_alpha_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Closures.TW_D1_alphader_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Closures.TW_dd_comm_alpha_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Closures.TW_dd_der_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Upstream declarations reused: none had to be fetched or added. Every row binds a
declaration that was already in `lean/`, so no Mathlib or TauCeti search was needed for
a new statement, and none was written.

## 4. Sources opened

* `paper/braided-sym-deriv.tex` at HEAD, version 79 (`\paperversion{79}`, line 47):
  Prop 3.2 at 337, Cor 3.5 at 436, Thm 4.1 at 453 with the sharpened forms at 491–494,
  Prop 4.4 at 531. Read the statements and the proofs.
* `lean/RESULTS.md` (99 lines, the statement ledger), `lean/BACKGROUND.md` (line 3 reads
  "`paper/braided-sym-deriv.tex`, v79 (`\paperversion` 79)", so the stale v73 pin the
  addendum mentions is not there at this HEAD), `lean/check_axioms.lean`,
  `loom-pack/lean/LEAN-TASK.md`, `formalization.yaml`.
* The declaration sources: `Research/BraidedSymDeriv/{General,Paper,TwistedCommutative,Closures,AntiAutomorphism}.lean`.
* `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain`
  over HTTPS, for the pin check only.
* Nothing paywalled, nothing unreachable, no `UNVERIFIED`.

## 5. Files changed

`git diff --name-only main...HEAD` (the branch base is `main` at `da26080`):

```
formalization.yaml
loom/m-1bad6a/BINDINGS.tsv
loom/m-1bad6a/REPORT-lean.md
loom/m-1bad6a/claims.tsv
```

`formalization.yaml` carries three one-line corrections, all inside my write scope:

* `sources.title`: `(preprint, v75)` to `(preprint, v79)`;
* `sources.id`: `pdf/braided-sym-deriv-v75.pdf` to `pdf/braided-sym-deriv-v79.pdf`
  (that file exists; `\paperversion` is 79);
* `automation.notes`: "a 149-declaration axiom audit" to "a 179-declaration" — the file
  has 179 `#print axioms` lines and the audit prints 179 footprints.

No `.lean` file was touched, so the four rows bind the tree as it stood.

## 6. Friction

* `lake-build.sh` reported 3.3 s on its first run and 65 s on the run I captured to a
  file. Both ended `Build completed successfully (18304 jobs).` I report both numbers.
* The repository's axiom audit does not cover `BSDGeneral.*` or `Closures.TW_*`. Four of
  the seventeen declarations these four rows bind are therefore outside it. I audited
  them myself and put the output in section 3.
* `README.md` line 4 says "Current version: **v76**" while the source is v79. That file
  is outside my write scope, so I did not touch it (`PROPOSE` 3).
* `lean/RESULTS.md`, row Prop 3.2, status cell: "**proved**, arbitrary rings, no
  hypothesis relating `D` and `alpha`". The phrase is true of the residual identities,
  which is what the row starts from. The iff statements in the same row do assume
  `D alpha = alpha D`, as the paper's Proposition does. I left the text alone
  (`PROPOSE` 2).

## 7. Doubts, and what I did not check

* The claim that `TW.mul` on `Fin 3 → ZMod 3` is `F_3[eps]/(eps^3)` rests on reading the
  definition: the double sum keeps the terms whose degrees add to a `Fin 3` index, so
  `eps^3` and higher have no index and vanish. I did not prove an isomorphism to a
  quotient ring, because no such statement is asked for.
* `prop:twisted` is bound to two witnesses, not to a set-level `⊄` sentence. A Lean
  statement of the non-inclusions would need set-level classes for `ADer` and the
  twisted class on this model; none exists, and rule 14 forbids adding one.
* I ran the two Lean legs of the gate only. I did not run `tools/papercheck.py` and did
  not compare a rebuilt PDF with `pdf/braided-sym-deriv-v79.pdf`.
* Whether `IsUnit (2 : A)` is the best rendering of "`2` invertible in `K`" depends on
  the intended `K`-algebra structure, which the Lean statement does not carry. The form
  used is the hypothesis the proof needs.

## 8. PROPOSE

* `PROPOSE:` add the missing `#print axioms` lines for `BSDGeneral.*` and
  `Closures.TW_*` to `lean/check_axioms.lean`, so the audit covers the four rows above
  without a scratch file.
* `PROPOSE:` in `lean/RESULTS.md`, row Prop 3.2, split the status cell so that "no
  hypothesis relating `D` and `alpha`" sits on the residual identities only.
* `PROPOSE:` `README.md` line 4 says "Current version: **v76**", and the changelog stops
  at v76; the source is v79. The text role or the orchestrator owns that file.
