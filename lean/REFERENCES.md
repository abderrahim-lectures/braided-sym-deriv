# Formalizing the sixteen references of "Braided-Symmetric Derivations of Algebras"

Paper: `paper/braided-sym-deriv.tex`, v63 (`\paperversion` 63).
Catalogue: `lean/Research/BraidedSymDeriv/References/`.
Build: `lean/build_references.sh` (see §7 for why it does not use `lake`).

This file lives in `lean/` beside the code it documents, not in `results/`, so
that it is versioned with the catalogue and travels with a clone of the
repository.

## 1. What the task is, and what it is not

The paper cites sixteen bibliography entries. This catalogue gives, for each
entry, a Lean 4 module that formalizes **the notion and the results the paper
takes from that entry**:

* the definition, in the paper's conventions (additive maps on rings, Jordan
  product without the half, `[x,y] = xy - yx`);
* every lemma of that reference that is elementary enough to prove — the
  linearisations, the sign conventions, "the 1-cocycles are the derivations",
  "the transpose is an involution";
* a witness where the reference asserts that a distinction is not vacuous (a
  Jordan derivation that is not a derivation, a braided-symmetric derivation
  that is not a braided derivation, a ring that is not reduced);
* for the deep theorems the paper **uses as hypotheses** (Herstein 1957,
  Cusack 1975, Brešar 1988), an exactly stated `Prop`-valued `def` documenting
  the theorem, plus a conditional theorem that consumes it. No `axiom`, no
  `sorry`: a theorem that is not proved here is a hypothesis of everything that
  uses it, never a silent gap.

It is **not** a proof of Herstein's, Cusack's or Brešar's theorems. Those are
research results of functional-identity theory; the paper itself takes Brešar's
theorem as a hypothesis in its Corollary 3.5, and `Paper.lean`'s
`corollary_3_5` does the same. What is gained is that every place where the
paper leans on them is now a named hypothesis with a machine-checked statement,
so a reader sees exactly what is assumed and can test the paper's theorems
against weaker or different assumptions.

## 2. The sixteen references

Line numbers are in `paper/braided-sym-deriv.tex` (v63). The numbering is the
order of the `bibitem`s, which is also the order of the paper's bibliography.

| # | Reference (bibitem key) | Where the paper uses it | Lean module |
|---|---|---|---|
| 1 | Beidar, Brešar, Chebotar, Martindale, *On Herstein's Lie map conjectures II*, J. Algebra 238 (2001) | line 100: maps acting as derivations on a fixed multilinear polynomial, earlier than Benkovič | `FDerivation` |
| 2 | Benkovič, *A note on f-derivations of triangular algebras*, Aequationes Math. 89 (2015) | line 99, §1: derivations, Jordan and Lie derivations as `f`-derivations for `f = x₁x₂`, `x₁∘x₂`, `[x₁,x₂]` | `FDerivation` |
| 3 | Brešar, *Jordan derivations on semiprime rings*, Proc. AMS 104 (1988) | lines 107–113: prime / semiprime / 2-torsion-free; line 191 `Der ⊆ JDer`; line 112 converse false in general; Theorem 1 (line 434) used in Cor. 3.5 | `Basic`, `JordanHerstein` |
| 4 | Brešar, Zelmanov, *Jordan homomorphisms: a survey*, Serdica 51 (2025) | lines 102, 118, Example 2.1: the Jordan product `½(xy+yx)`, twice the paper's `x∘y` | `JordanProduct` |
| 5 | Chambert-Loir, *(Mostly) Commutative Algebra*, Springer 2021 | lines 172 and 455, 1.4.12: reduced = no nonzero nilpotent | `Reduced` |
| 6 | Cusack, *Jordan derivations on rings*, Proc. AMS 53 (1975) | line 113, Cor. 5: extends Herstein to 2-torsion-free semiprime rings; line 324, §2: the defect `d(a,b)` | `JordanHerstein` |
| 7 | Herstein, *Jordan derivations of prime rings*, Proc. AMS 8 (1957) | line 104, p. 1104: `ab+ba` without the half; line 180: the square form; line 111: Theorem 3.1 | `JordanHerstein` |
| 8 | Herstein, *Rings with Involution*, Chicago 1976 | line 285, §1.2: `a** = a`, `(a+b)* = a*+b*`, `(ab)* = b*a*` | `Involution` |
| 9 | Hochschild, *On the cohomology groups of an associative algebra*, Ann. of Math. 46 (1945) | lines 97, 332: §§2 and 4, the cocycles, Definition 2.1 for `δ` on a 1-cochain | `Hochschild`, `HochschildComplex`, `HochschildGeneral` |
| 10 | Hosseini, Mohammadzadeh Karizaki, *Functional equations characterizing σ-derivations*, Acta Sci. Math. 85 (2019) | line 187, §1: the α-derivation identity | `AlphaDerivation` |
| 11 | Huru, *Quantizations of braided derivations I*, Lobachevskii J. Math. 24 (2006) | lines 139, 215, §4.1 Def. 14: braided derivations, a different notion | `BraidedDerivation` |
| 12 | Jacobson, *Abstract derivation and Lie algebras*, Trans. AMS 42 (1937) | line 96, Part I: derivations of a nonassociative algebra; line 238: `BSDer_σ` = derivations of `(A, ·_σ)` | `Nonassoc` |
| 13 | Jordan, von Neumann, Wigner, *On an algebraic generalization of the quantum mechanical formalism*, Ann. of Math. 35 (1934) | line 103, p. 64: quasi-multiplication `ab` from `a×b` and `b×a` | `JordanProduct` |
| 14 | Martindale, *Lie derivations of primitive rings*, Michigan Math. J. 11 (1964) | lines 98, 266, p. 183: the definition of a Lie derivation | `Nonassoc` |
| 15 | Różański, *Bicharacters, braids and Jacobi identity*, arXiv q-alg/9611029 (1996) | lines 139, 215, §2: braided derivations | `BraidedDerivation` |
| 16 | Weibel, *An Introduction to Homological Algebra*, Cambridge 1994 | lines 176, 325–339, §9.1: the Hochschild complex, `δ∘δ = 0`, `HH^n`; §9.2: principal (= inner) derivations | `Hochschild`, `HochschildComplex`, `HochschildGeneral` |

Two entries are cited for a definition only, and the catalogue says so instead of
inventing a theorem:

* **Martindale 1964** is cited at p. 183 for the Lie-derivation identity, not for
  the structure theorem of his paper. `Nonassoc.lean` formalizes the identity,
  the fact that it is Jacobson's condition for the commutator product, and the
  elementary facts; it does **not** state a structure theorem it cannot quote
  verbatim.
* **Beidar–Brešar–Chebotar–Martindale 2001** is cited to date the notion of "a
  map acting as a derivation on a fixed multilinear polynomial" before Benkovič.
  `FDerivation.lean` formalizes the notion; no theorem of the entry is used by
  the paper, and none is claimed.

## 3. What each module contains

`Basic.lean` holds the notions shared by at least two modules, all of them
elementary and all in the paper's conventions: `jordan`, `commutator`, `Der`,
`JDer`, `hersteinJordan`, `LieDer`, `Comm`, `leibnizDefect`, `delta1`, `delta2`,
`innerDer`, `PrimeRing`, `SemiprimeRing`, `TwoTorsionFree`. Proved there:
`der_jder`, `der_lie`, `der_hersteinJordan`, `leibnizDefect_eq_neg_delta1`,
`delta1_eq_zero_iff_der` (the 1-cocycles are the derivations),
`delta2_delta1` (`δ∘δ = 0`), `leibnizDefect_cocycle` (the paper's identity
(3.2)), `jder_iff_defect_symm`, `innerDer_der`, `innerDer_lie`,
`der_comp_innerDer` (`ad_{Dg}` is the bracket of `D` with `ad_g`), and
`prime_imp_semiprime`.

| Module | Proved | Stated as a hypothesis | Witness |
|---|---|---|---|
| `Reduced` (5) | `isReduced_iff_no_nilpotent`, `mul_self_eq_zero`, `isReduced_imp_semiprime`, `pow_pred_sq_eq_zero`, `isReduced_iff_semiprime` | — | `zmod4_not_reduced`, `dualNumber_not_reduced` |
| `Nonassoc` (12, 14) | `NonassocDer`, `bsder_iff` (line 238), `zero_mul`, `commutator_iff_lieDer`, `jordan_iff_jDer` | — | `Witness.lie`, `Witness.not_der` (a Lie derivation that is not a derivation) |
| `FDerivation` (1, 2) | `fDerivation`, `fDerivation₂`, `fDerivation_iff₂`, `mul_iff`, `jordan_iff`, `commutator_iff`, `fDerivation_one` | — | — |
| `JordanHerstein` (3, 6, 7) | `linearisation`, `herstein_imp_jder`, `jder_imp_herstein`, `herstein_iff_jder`, `cusackDefect_eq` | `hersteinTheorem`, `cusackCorollary`, `bresarTheorem`, with consumers `jder_eq_der_of_bresar`, `jder_eq_der_of_herstein` | `Witness.jordan_eq_zero`, `Witness.jder`, `Witness.id_not_der` (char 2: Jordan but not a derivation); `NonTorsionFree.double_jder_zmod4`, `double_not_der`, `double_not_hersteinJordan` (on `ZMod 4` the two Jordan forms differ, and `Der ⊊ JDer`) |
| `JordanProduct` (4, 13) | `quasiMul`, `quasiMul_comm`, `quasiMul_eq_jordan`, `jordan_identity`, `jordan_eq_two_smul_half`, `der_jordan` | — | — |
| `Involution` (8) | `RingInvolution` with `map_add`, `map_mul`, `involutive`, `map_zero`, `map_neg`, `map_sub`, `map_one`, `map_pow`, `injective`; `matrixTranspose`; `eq_half_symm_add_half_skew` | — | `matrixTranspose` is the standard example |
| `AlphaDerivation` (10) | `AlphaDer`, `alphaDer_id_iff`, `der_alphaDer_id`, `alphaDer_add`, `alphaDer_zero`, `symmProd`, `TwistedAlpha`, `bsder_iff_twisted`, `symmProd_alpha` | — | Prop 4.4's witness is already kernel-checked in `Counterexamples.lean` (`TW`) and is not duplicated |
| `Hochschild` (9, 16) | `delta0`, `delta1_delta0`, `innerDer_eq_neg_delta0`, `Cocycle1`, `Coboundary1`, `coboundary_imp_cocycle`, `cocycle1_iff_der`, `coboundary1_iff_inner`, `defect_is_twoCocycle` | — | — |
| `HochschildGeneral` (9, 16) | `contract` (merge two adjacent slots) with its three slotwise lemmas, `coboundary n` for **every** `n` with `coboundary_apply`, and `coboundary_zero`, `coboundary_one`, `coboundary_two` identifying it with `delta0`, `delta1`, `delta2` | — | — |
| `HochschildComplex` (9, 16) | curried cochains in degrees 0–3, `delta0`–`delta3`, `delta1_delta0`, `delta2_delta1`, `delta3_delta2`, `leibnizDefect_cocycle`, `isCocycle1_iff_der`, `isCoboundary_iff_exists_innerDer`, `HH1` as a quotient with its setoid, `hh1_mk_eq_iff`, and `der_iff_ref`, `leibnizDefect_eq_ref` identifying its notions with the prelude's | — | `ExampleDefect.defectCochain_ne_zero` (a non-zero 2-cocycle), `ExamplePolynomial.hh1_nontrivial` (`HH¹(F₂[t], F₂[t]) ≠ 0`, via the formal derivative) |
| `BraidedDerivation` (11, 15) | `Braiding`, `braidedDerivation` (Różański's Definition 2.2), `signedSwap`, `symmProd`, `symmProd_signedSwap`, `braidedDerivation_signedSwap`, `bsder_signedSwap` | — | `not_braidedDerivation`, `bsder_witness`: Remark 2.2, proved for the signed swap |
| `PaperBridge` | `der_iff`, `jder_iff`, `lieDer_iff`, `comm_iff`, `innerDer_eq`, `leibnizDefect_eq`, `leibnizDefect_cocycle_eq` | — | — |

`PaperBridge.lean` proves that the catalogue's notions are the paper's own:
`Ref.Der`, `Ref.JDer`, `Ref.LieDer`, `Ref.Comm` are `Iff.rfl`-identified with
`BSD.Der`, `BSD.JDer`, `BSD.LieDer`, `BSD.Comm` of `Paper.lean`, the inner
derivation is the same map, and the defect is the defect of
`TwistedCommutative.lean`. Nothing in the catalogue is a parallel universe of
notions the paper does not use.

### Three results of the catalogue that are not in the paper

1. **The linearisation does not need 2-torsion-freeness.**
   `JordanHerstein.herstein_imp_jder` derives the `∘` form from Herstein's square
   form in an arbitrary ring, by linearising at `x + y`; no division by 2 and no
   torsion hypothesis occurs. The converse (`jder_imp_herstein`) does need
   `TwoTorsionFree`, which is exactly the paper's §1 remark. Brešar 1988 states
   the same linearisation as Proposition 2(i) under his blanket 2-torsion-free
   hypothesis; the hypothesis is not needed for that step. That the two forms are
   *different conditions*, not two presentations of one, is witnessed on `ZMod 4`:
   the doubling map satisfies the `∘` form (`4 = 0`) and not the square form
   (`2 ≠ 0`) — `NonTorsionFree.double_not_hersteinJordan`. The same map is a
   Jordan derivation that is not a derivation (`double_not_der`), the witness
   Brešar's "the converse is false in general" asks for in a ring that is neither
   2-torsion-free nor semiprime.
2. **Remark 2.2 is true, and here is an instance.** For the signed swap
   `B(x⊗y) = (-y)⊗x` (the Koszul braiding with `χ = -1` on odd elements),
   Różański's braided derivations are exactly the ordinary derivations, while the
   paper's braided-symmetric derivations are exactly the Lie derivations. Since
   `Nonassoc.Witness` exhibits a Lie derivation of `F₂ × F₂` that is not a
   derivation, the two notions of Remark 2.2 differ, and the paper's sentence
   "braided derivations form a different notion" is proved for that braiding
   rather than asserted.
3. **Nonassoc.Witness.not_der** is the elementary reason the `−τ` row of
   Remark 2.4 is a separate row: on a commutative ring every additive map is a
   Lie derivation, while a derivation must satisfy the Leibniz rule.

### 3.1 One place where the paper's attribution is inverted

The paper's §1 (line 180) says: "A *Jordan derivation* in the sense of
Herstein 1957, p. 1104, is an additive map with `D(x²) = D(x)x + xD(x)`. ...
We follow Herstein and do not divide by 2, so that characteristic 2 is allowed."

Herstein's p. 1104 says the opposite, in this order: first, a Jordan derivation
is a derivation of the Jordan ring, `(a ∘ b)' = a' ∘ b + a ∘ b'`, "writing this
out ... `(ab + ba)' = a'b + ab' + b'a + ba'`"; then, "for most of this paper all
rings considered will be of characteristic not 2; for such rings `A` a Jordan
derivation can be defined by `(1) (a+b)' = a'+b'`, `(2) (a²)' = aa' + a'a`".
So the square form is Herstein's *characteristic-≠2 simplification*, and the `∘`
form is his general definition. The paper's substance is unaffected — the `∘`
form is what the paper uses everywhere, and it is Herstein's general one — but
the clause "in the sense of Herstein, p. 1104" attached to the square form
reverses which of the two Herstein offers in general. The catalogue records the
correct order in `JordanHerstein.lean`, and `herstein_imp_jder` is the theorem
that reconciles them in every characteristic.

## 4. What is deliberately not formalized

* **Herstein 1957, Theorem 3.1; Cusack 1975, Corollary 5; Brešar 1988,
  Theorem 1.** The same theorem in three strengths, proved by functional-identity
  arguments of research length. The paper takes Brešar's version as a hypothesis
  in its Corollary 3.5. The catalogue states all three and consumes them; it does
  not prove them, and no declaration claims otherwise.
* **Martindale 1964's structure theorem.** Cited for the definition only; see §2.
* **Beidar–Brešar–Chebotar–Martindale 2001, Theorem 4.3.** The paper imports no
  theorem from it; the module formalizes the notion.
* **The Hochschild complex in general degree.** `Hochschild.lean` covers the
  degrees the paper uses (0, 1, 2); `HochschildComplex.lean` covers 0–3, `HH¹`
  as a quotient and two non-vacuity examples; `HochschildGeneral.lean` defines the
  coboundary `δ_n` in **every** degree. What is *not* formalized is
  `δ (δ f) = 0` in general degree — it is proved in degrees 0, 1, 2
  (`delta1_delta0`, `delta2_delta1`, `delta3_delta2`, `leibnizDefect_cocycle`) and
  the general case is the one remaining gap. It needs two pieces this development
  does not have: the face commutation
  `contract i (contract j a) = contract (j-1) (contract i a)` for `i < j`
  (a vector identity on `Fin` indices), and the alternating double-sum
  cancellation that pairs the index `(i,j)` with `(j-1,i)`. The paper does not
  need it (it uses degrees 0–2 only), so shipping the low-degree instances is not
  a loss for the paper's claims, but the general complex is incomplete without it.
* **The classification of natural involutions of `V ↦ V ⊗ V`** (Remark 2.4) is
  the paper's own claim, not a citation of any of the sixteen entries.

## 5. TauCeti

`TauCetiProject/TauCeti` was inspected as a source (`git clone --depth 1`, 22,664
Lean files). Relevant content:

* `TauCeti/RingTheory/CyclicCohomology/Cochain.lean`: the Hochschild coboundary
  as the alternating sum of cofaces, `hochschildCoboundary_hochschildCoboundary :
  b (b φ) = 0` in general degree, and the explicit face formula
  `hochschildCoboundary_apply_eq_sum_contractNth_add`;
* `TauCeti/RingTheory/HochschildCohomology/{Complex,Coboundary,Dual}.lean`: the
  cochain complex, cocycles, coboundaries and `HH^n` as a quotient;
* `TauCeti/RingTheory/CyclicCohomology/Derivation.lean`: `derivationLieAlgebra`
  and `innerDerivation` (`⁅z, -⁆`), with the cocycle of an inner derivation shown
  to be a coboundary;
* `TauCeti/Algebra/Homology/AInfinity/Algebra/Hochschild/*`: the `A∞`
  (suspended) version with the Gerstenhaber bracket.

It **cannot be imported here**. TauCeti pins `leanprover/lean4:v4.36.0-rc1` and
uses the module system (`module`, `public import`), while every Lean in this VM is
4.33.1 with a Mathlib built for 4.33.1; Mathlib has no Hochschild complex at this
version (`rg Hochschild /opt/mathlib/Mathlib` matches only group cohomology).
Building TauCeti would mean a second Lean and a second Mathlib, out of proportion
to this task and disconnected from the repository's own toolchain.

So TauCeti is used as a **specification**. `Hochschild.lean` follows its
statement design (the alternating-sum coboundary, `b² = 0`) while keeping the
paper's convention: the paper's `n`-cochains take `n` arguments, TauCeti's take
`n + 1` (Connes' convention), so its formulae agree with the paper's only after
the index shift, and the catalogue states this in the module header. Two TauCeti
practices were adopted as requirements: no `native_decide` anywhere, and a pinned
build description.

## 6. Conventions that decide paper↔Lean fidelity

* maps are **additive** (`A →+ A`), not `K`-linear: the paper says results cited
  hold more generally for additive maps on rings, and the ring-level references
  (Herstein, Cusack, Brešar, Martindale, Beidar et al.) are stated that way;
* the Jordan product is `x ∘ y = xy + yx`, without the half (Herstein 1957,
  p. 1104); the survey's `½(xy + yx)` differs by the factor 2, which is recorded
  in `JordanProduct.jordan_eq_two_smul_half` and matters only in characteristic 2;
* `IsReduced` is Mathlib's, which is Chambert-Loir's definition, and is stronger
  than the paper's sharpest sufficient condition ("no nonzero `z ∈ A_-` with
  `z² = 0`", stated in the proof of Theorem 4.1);
* Herstein's three axioms for an involution do **not** include `1* = 1`, but in a
  unital ring it follows from them (`Involution.map_one`: apply
  anti-multiplicativity to `1 · 1*`), and the catalogue proves it rather than
  assuming it;
* everything is over a `Ring` or `CommRing`; the field `K` of the paper enters
  only through invertibility of 2, which appears as an explicit hypothesis where
  it is used.

## 7. Build

```
cd lean && ./build_references.sh
```

builds `TwistedCommutative`, `Paper`, the prelude, every per-reference module,
the bridge and the aggregator, in dependency order, and prints `OK: every
reference module elaborates` only if all of them did. A single module:

```
cd lean && ./build_references.sh Research.BraidedSymDeriv.References.Hochschild
```

`lean/lean-toolchain` pins `v4.36.0-rc2`, which is not installed in this VM;
`lean` on `PATH` is 4.33.1 and the Mathlib on `LEAN_PATH` is built for it. The
script therefore calls `lean` directly instead of `lake build`, and writes every
`.olean` to `.scratch/olean/` so that no build artifact lands next to a source
file and the tree stays clean. The toolchain pin remains unverified — a
repository-level defect this catalogue does not introduce.

## 8. Verification

**Elaboration.** `cd lean && ./build_references.sh` was run on 2026-11-01 with
`lean` 4.33.1 and Mathlib of that toolchain. It built, in this order and with
`rc = 0` for each,

```
TwistedCommutative  Paper  References.Basic  References.Reduced
References.Hochschild  References.HochschildComplex  References.HochschildGeneral
References.JordanHerstein  References.JordanProduct  References.FDerivation
References.Nonassoc  References.AlphaDerivation  References.Involution
References.BraidedDerivation  References.PaperBridge  References.All
```

The last full run, with `.scratch/olean/` deleted first (so nothing was cached),
built all sixteen targets in 43 s and printed
`OK: every reference module elaborates`. After the two corrections of §9 the whole
build was repeated (fifteen targets, `OK`) and the concatenation re-run at 2021
lines, `rc = 0`. `References.All` imports the whole catalogue, so the
aggregator's elaboration is a second check of the union. In
addition the whole catalogue was elaborated as a single 1967-line file
(`lean/.scratch/refs_all.lean`, produced by `lean/.scratch/mk_all.py`, which
strips the `import` lines and concatenates the modules) with `rc = 0` and no
warnings, which is a check that the modules agree when read together.

**Trust.** No `sorry`, `admit`, custom `axiom` or `native_decide` occurs:

```
rg -n 'sorry|admit|native_decide|^axiom' lean/Research/BraidedSymDeriv/References/
```

is empty. The only `set_option` in the catalogue is `set_option autoImplicit
false` at the head of `HochschildComplex.lean`, which is stricter than the
default, not a loophole. An axiom audit of twelve load-bearing declarations
(`RefJordanHerstein.herstein_imp_jder`, `RefJordanHerstein.linearisation`,
`Ref.delta1_eq_zero_iff_der`, `Ref.delta2_delta1`,
`RefReduced.isReduced_iff_semiprime`, `RefJordanProduct.jordan_identity`,
`RefBraided.not_braidedDerivation`, `RefNonassoc.Witness.not_der`,
`RefAlpha.bsder_iff_twisted`, `RefInvolution.matrixTranspose`,
`RefFDerivation.mul_iff`, `RefPaper.jder_iff`,
`RefHochschildComplex.ExamplePolynomial.hh1_nontrivial`,
`RefHochschildComplex.delta2_delta1`,
`RefHochschildComplex.leibnizDefect_cocycle`,
`RefHochschildComplex.leibnizDefect_eq_ref`) prints only `propext`,
`Classical.choice` and `Quot.sound`, or nothing:

```
'RefJordanHerstein.herstein_imp_jder' depends on axioms: [propext]
'RefJordanHerstein.linearisation' depends on axioms: [propext]
'Ref.delta1_eq_zero_iff_der' depends on axioms: [propext]
'Ref.delta2_delta1' depends on axioms: [propext]
'RefReduced.isReduced_iff_semiprime' depends on axioms: [propext, Quot.sound]
'RefJordanProduct.jordan_identity' depends on axioms: [propext]
'RefBraided.not_braidedDerivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'RefNonassoc.Witness.not_der' depends on axioms: [propext, Classical.choice, Quot.sound]
'RefAlpha.bsder_iff_twisted' does not depend on any axioms
'RefInvolution.matrixTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'RefFDerivation.mul_iff' does not depend on any axioms
'RefPaper.jder_iff' depends on axioms: [propext]
'RefHochschildComplex.ExamplePolynomial.hh1_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'RefHochschildComplex.delta2_delta1' depends on axioms: [propext, Quot.sound]
'RefHochschildComplex.leibnizDefect_cocycle' depends on axioms: [propext, Quot.sound]
'RefHochschildComplex.leibnizDefect_eq_ref' does not depend on any axioms
```

**What is not verified.** The pinned toolchain `v4.36.0-rc2` is not installed in
this VM, so nothing here has been elaborated under it; every check above used
4.33.1 with the Mathlib of that toolchain. `lake build` was not run and would
not reproduce the check (no `lake-manifest.json` is committed and the
requirement tracks `master`). The deep theorems listed in §4 are hypotheses, not
proofs, and the catalogue does not make the paper's theorems depend on anything
weaker than they do.

## 9. What the swarm contributed, and one process error

Eight agents worked the same eight clusters in parallel. All eight submitted, but
the submissions arrived after the swarm was stopped and the verdict channel
refused them (`swarm smvxk8w5r has ended`) — a process error on my side: I stopped
the swarm when its members looked starved, and the submissions were already in
flight. I checked all eight by hand instead: each file was compiled here with
`lean` and returned `rc = 0` with no warnings, in its own directory under
`.ultramath/`.

Three of them changed the catalogue:

* **m7** found the false claim in `Involution.lean` that `1* = 1` does not follow
  from Herstein's three axioms. It does: `(1 · 1*)* = 1** · 1* = 1 · 1* = 1*` and
  `(1 · 1*)* = 1** = 1`. `map_one` (and `map_pow`) now prove it; the header was
  corrected.
* **m5** supplied the `ZMod 4` witness that the square form and the `∘` form are
  different conditions without 2-torsion-freeness (the doubling map). Integrated
  as `JordanHerstein.NonTorsionFree`.
* **m3** pointed out that the paper's braided-derivation remark is **Remark 2.2**,
  not 2.5 (2.4 is the four-row dictionary). Corrected here and in the Lean
  docstrings.

One produced the module that replaced the thin version of a reference:
**m1**'s Hochschild development is `HochschildComplex.lean`.

The other four were correct but redundant with what is already there: **m2**'s
α-derivation module (it also refuted the equivalence "α-derivation = derivation
of `x ↦ x·α(y)` under `Dα = αD`", which my task brief asserted and which
`AlphaDerivation.lean` never claimed), **m4**'s two-directional Remark 2.2 (a
different braiding separates the classes in the other direction as well;
`BraidedDerivation.lean` already proves the one direction that makes the two
notions different), **m6**'s Jordan-product module and **m8**'s `f`-derivation
module (both overlap the shipped modules; m8's witness that the identity on `ℤ`
is an `f`-derivation for the non-multilinear `f(x) = x²` while not being a
derivation is a good demonstration that multilinearity is essential, and is not
shipped).
