# The paper's results, and their Lean status

Every numbered result of `paper/braided-sym-deriv.tex` with its Lean
counterpart, statement for statement, and the honest status of each. This is a
statement audit in the sense of the *statement-audit* method: source
correspondence and proof status are reported separately, and the modelling
choices that make a Lean statement weaker or stronger than the paper's are named.

Two carriers appear, deliberately:

* `A` is a ring (or `CommRing`), maps are additive `A →+ A` — the paper's
  "additive maps on rings where the result holds more generally" convention
  (its line 93);
* `A := Fin 4 → ZMod 3` (or a sibling finite model) for the examples, where
  `Remark46.lean` uses `Fin 3` coefficients for its kernel `decide`s and
  `Dimensions.lean` uses `ZMod 3` for the linear algebra; the coordinate
  formulas agree.

| # | Paper result | Lean | Status |
|---|---|---|---|
| Def 2.1 | braided-symmetric derivation for an involution `σ` of `A ⊗ A` | `BraidedSymDeriv.BraidedSymmetricDerivation` (binary `σ`; the `A ⊗ A` form via `BSDGeneral.sigmaAlpha` and `General.lean`'s `prodA`/`prodB`) | **proved-equivalent** for `id`, `τ`, `σ_α`, and the triangle `μ_σ ∘ σ = μ_σ` of line 125 is `BSDGeneral.muSigma_comp_sigma`; the binary encoding is strictly narrower in general (documented in `Paper.lean`'s header, and the pair encoding of `-id`/`-τ` lives in `Background/Nonassoc.lean`) |
| Rem 2.2 | braided derivations (Huru, Różański) are a different notion | `Background.BraidedDerivation.not_braidedDerivation` (signed-swap braiding: a map braided-symmetric and not a braided derivation) | **proved** for that braiding |
| Ex 2.3 | `K × K` with the swap: product neither associative nor unital | `BSD.Example23.not_assoc`, `BSD.Example23.no_unit` (`K = F₅`) | **proved** (instance over `F₅`; the paper's `K` generic) |
| Rem 2.4, 2.5 | the dictionary `id ↦ Der`, `τ ↦ JDer`, `-id ↦ End`, `-τ ↦ LieDer`; completeness of the four natural involutions; the idempotent correspondence; the char-2 family | `BSD.bsderP_two_mul_iff`, `BSD.bsderP_jordan_iff`, `BSD.bsderP_zero`, `BSD.bsderP_commutator_iff`; `Remark24.natural_form`, `natural_involution_arith`, `natural_involution_char_ne_two`, `natural_involution_char_two`, `idempotent_reflection`, `char_two_reflection_trivial`; `BSDGeneral.bsd_id_iff_der`, `char_two_bsd_id_all`, `char_two_strict`, `bsd_neg_id_all`, `bsd_neg_tau_is_lie`; the four space identities on `F₅[u,v]/(u²,v²)` and `F₃[ε]/(ε³)` in `Closures.lean` / `TwistedCommutative.UV` (the paper's `F₅[ε]/(ε²)` sentence, line 262, is a computation of this review's, not a Lean declaration); the characteristic-2 family `σ_λ = λ·id + (1+λ)·τ`: `BSDGeneral.sigmaLam_involution` (each is an involution when `2 = 0`), `sigmaLam_product` (its product is `(1+λ)(x∘y)`) and `sigmaLam_one_product` (`λ = 1` gives the zero product); the collapse of the four to two in characteristic 2 (`neg_eq_self_of_char_two`, `neg_tauSwap_eq_tauSwap`) and `τ = id` on `K ⊗ K` (`tauSwap_self`) | **proved** (the dictionary is Remark 2.4; the completeness, idempotent and characteristic-2 classification is Remark 2.5, in the `M₂(K)` matrix form of `V ⊗ V`; the binary-encoding expressibility limit is recorded in `Paper.lean`) |
| Def 3.1 | the Leibniz defect `E_D` | `leibnizDefect` (`TwistedCommutative`), `ncDefect` (same file), `BSDGeneral.Ed` | **proved** |
| Prop 3.2 | `D ∈ BSDer ⇔ E_D(x,y) + α(E_D(y,x)) = 0` (automorphism and anti-automorphism forms); both residual identities | `BSDGeneral.residual_automorphism`, `residual_antiautomorphism`, `bsd_iff_automorphism`, `bsd_iff_antiautomorphism`, `derivation_iff_commutes`, `cocycle`; `TwistedCommutative.prop_defect_aut`, `prop_defect_anti` | **proved**, arbitrary rings, no hypothesis relating `D` and `α` |
| Rem 3.3 | `ad_g` lies in the twisted class iff `g − α(g) ∈ Z(A)` (anti: `g + α(g) ∈ Z(A)`); `Inn_α = Inn ∩ BSDer^α` | `BSD.innerDer_comm_iff`, `BSD.innerDer_twisted_iff`; `AntiAutomorphism.der_twisted_iff_comm_anti` | **proved**, in the `∀x, [g−α(g), α(x)] = 0` form and in the `∈ Z(A)` form (`innerDer_comm_iff_center`, `innerDer_twisted_iff_center`, which use the bijectivity of `α`), with the space identity `Inn_α(A) = Inn(A) ∩ BSDer_{σ_α}(A)^α` as `innAlpha_eq` |
| Thm 3.4 | Brešar 1988, Theorem 1 | **proved** in `Bresar1988.lean`: `jordan_derivation_eq_derivation` (all rings, 2-torsion-free and semiprime), `bresar1988Theorem1_holds` : `Background.JordanHerstein.bresar1988Theorem1` | **proved** — `corollary_3_5_unconditional`; the conditional form `corollary_3_5`, which still takes `hBresar` (`Paper.lean:167`), and its anti-automorphism twin (`AntiAutomorphism.lean:59`) are kept for reference, not because anything needs them. The proof is the paper's own chain (Proposition 2, Theorem 3 in the defect form, Lemma 4, then `2w² = w·D[a,b]`, `4w³ = 0`, `w = 0`) |
| Cor 3.5 | `BSDer_{σ_α}(A)^α ∩ JDer(A) = Der(A)^α` for 2-torsion-free semiprime rings, both kinds of `α` | `BSD.corollary_3_5` (automorphism), `AntiAutomorphism.corollary_3_5_anti` | **proved** unconditionally: `BSD.corollary_3_5_unconditional`, `AntiAutomorphism.corollary_3_5_anti_unconditional` (the conditional forms are kept for reference) |
| Thm 4.1 | `BSDer_{σ_α}(A)^α = Der(A)^α` for commutative reduced `A` with 2 invertible | `BSD.theorem_4_1` (equivalence, `[IsReduced A]`, `IsUnit 2`); `twisted_commutative` | **proved**; `[IsReduced]` is stronger than the paper's sharpened hypothesis (deliberate, `Remark46.lean` header) |
| Thm 4.1, proof | the symmetric-defect version for arbitrary algebras; the `z ∈ A₋, z² = 0` sharpening | `BSDGeneral.thm41_core` (symmetric `E_D` + no nonzero square-zero `z ∈ A₋` ⇒ derivation, any ring) | **proved**, and it is the form `Remark 4.6` falsifies |
| Rem 4.6, quaternions (v73) | `dim BSDer_{σ_α}(ℍ)^α = dim Der(ℍ)^α = 1` and `dim BSDer_{σ_α}(ℍ) = 1 < 3` hold for the conjugations, not for `α = id` (where all three are `3`) | `QuaternionConjug.class_is_line`: for `α x = -(i x i)`, the maps that commute with `α` and satisfy the twisted rule are exactly the multiples of `ad_i`; `adI_ne_zero`; `conj_conjugacy`: `q'` with `q'² = -1` is conjugate to `i` by `u = 1 - q' i` | **proved** for the model conjugation and for the `α`-**commuting** half (`class_is_line` assumes `∀ x, D (conjI x) = conjI (D x)`); the whole-class statement `dim BSDer_{σ_α}(ℍ) = 1 < 3` is a computation, not a Lean theorem. The passage to a general pure imaginary unit is the conjugacy identity, stated and proved, but the transport of the class along it is not formalized |
| §2, reduced (v73) | `reduced` is defined for commutative algebras and used for algebras that are not commutative; v73 defines it for any algebra | `QuaternionConjug.reduced_imp_semiprime`: a reduced ring (no nonzero nilpotent), commutative or not, is semiprime in Brešar's sense | **proved** |


| Ex 4.2 | `F₅[u,v]/(u²,v²)`, `α`: `u ↦ u`, `v ↦ -v`; `D(uv) = uv` lies in the twisted class and is not a derivation; `E_D(u,v) = uv` has square zero | `TwistedCommutative.UV.D_comm_alpha`, `D_twisted` (basis pairs), `D_not_der`; `Closures.UV_D_comm_alpha_all`, `UV_D_twisted_all` (all 625 pairs) | **proved** on all pairs (the basis-pair gap closed in `Closures.lean`) |
| Ex 4.3 | `F₂ × F₂` with the swap: `D(p) = D(q) = e` is twisted, not a derivation | `BSD.Example43.comm`, `twisted`, `not_der` | **proved** (all pairs, `decide`) |
| Prop 4.4 | `F₃[ε]/(ε³)`, `α(ε) = -ε`: neither `ADer` nor `BSDer^α` contains the other | `TwistedCommutative.TW.D1_comm_alpha`, `D1_alphader`, `D1_not_twisted`, `dd_comm_alpha`, `dd_der`, `dd_not_alphader`; `Closures.TW_*_all` (all 81 pairs) | **proved** on all pairs |
| Ex 4.5(a) | `M₂(F₃)`, transpose, `g = E₁₂ − E₂₁`: `ad_g` commutes with the transpose, is braided-symmetric, is not an α-derivation | `BraidedSymDerivCounterexamples.ex45a_alphaDeriv`, `ex45a_braided`, `ex45a_commutes`, `ex45a_derivation`, `ex45a_tuple`, `ex45a_not_alpha` (structural proofs, no enumeration) | **proved** as propositions (the printed `#eval`s remain as documentation) |
| Ex 4.5(b) | `K[ε]/(ε²)`: in char ≠ 2 both classes one-dimensional and equal; in char 2 `BSDer = End` (dim 4) and `ADer = Der` (dim 2) | `Example45b.lean`, for an **arbitrary field** `K` (no finite model): `Dε_der`, `Dε_ader`, `Dε_comm`, `Dε_mem`; char ≠ 2: `bsderαSub_eq_span`/`derSub_eq_span`/`aderSub_eq_span` (`= span {Dε}`) and `finrank_bsderαSub`, `finrank_derSub`, `finrank_aderSub` `= 1`; char 2: `alphaLin_eq_id_of_char_two`, `bsderSub_eq_top` with `finrank_bsderSub_of_char_two = 4`, `derSub_eq_span_of_char_two` with `finrank_derSub_of_char_two = 2`, and `aderSub_eq_derSub` | **proved** — kernel-checked, no `native_decide`; the eleven footprints are `propext, Classical.choice, Quot.sound` (`check_axioms.lean`) |
| Rem 4.6 | the four-dimensional `F₃`-algebra where `BSDer^α = 3 > 2 = Der^α` | `BSD.Remark46.{assoc, one_mul, mul_one, alpha_mul, alpha_involutive, comm, leibniz, not_deriv, defect_vw, skew_sq_zero}` (kernel-checked, no `native_decide`); both dimension counts in `Dimensions.lean`: `derα_eq_span`, `linIndep_B`, `finrank_derα : finrank DerαSub = 2` and `bsderα_eq_span`, `linIndep_bsder`, `finrank_bsderα : finrank BSDerαSub = 3`; the witness `U₁`: `U₁_bsder`, `U₁_jder`, `U₁_not_der` | **proved** (all six axiom footprints audited in `check_axioms.lean`, kernel `decide` only) |
| §3, the residual identity (v78) | without `Dα = αD`, the two terms `E(x,y) + α(E(y,x))` vanish exactly when `D` is in the class **and** commutes with `α`? No: granted their vanishing, membership in the class is *equivalent* to commuting | `ReductionEquiv.bsd_iff_comm_of_defect`: from `∀ x y, Ed D x y + α (Ed D y x) = 0`, `D` satisfies the `σ_α`-Leibniz rule iff `Dα = αD` | **proved**; the hypothesis is essential (a derivation with `Dα ≠ αD` is the counterexample) |
| Rem 4.6, the three forms (v77) | the defect vanishes on the mixed pairs iff it vanishes on the odd–odd pairs iff `D` is a derivation | `ReductionEquiv.lean`: `Ed_self_eq_zero_of_skew` and `Ed_add_swap_of_skew` (the defect is alternating on `A₋`), `thm41_of_mixed` (mixed ⟹ derivation: the defect is then antisymmetric everywhere, so `D` is a Jordan derivation and Brešar applies), `der_iff_mixed`, `der_iff_odd_odd`, `mixed_iff_odd_odd`, and `bsd_iff_mixed_and_odd_odd`, which states it in the paper's own terms (`D ∈ BSDer_{σ_α}(A)^α`) | **proved** (seven declarations in the axiom audit) |
| Rem 4.6, open question | does Theorem 4.1 survive dropping commutativity while keeping reducedness? | `Reduction.lean`: `Ea_eq_lie` (the antisymmetric defect *is* the Lie-derivation defect), `Ea_alpha_fixed`, `Ed_alpha_of_fixed`/`_fixed_skew`/`_skew_fixed`/`_skew_skew` (the defect respects the `α`-grading), `Ea_eq_zero_of_fixed_skew` (the mixed pairs are free), `thm41_of_even_even_odd_odd` (the sharpened reduction), `fixedSubring`/`Dfix`/`jder_Dfix`/`Ed_eq_zero_of_fixed` (the fixed part is Brešar's theorem, not an assumption) with `thm41_of_odd_odd` (the reduction with only the odd-odd case assumed), `EaNilpotent`, `thm41_of_nilpotent_Ea`, `thm41_of_sq_zero_Ea`, `EaNilpotent_of_comm` (the commutative case is the `n = 1` case) | **equivalent** to `E` vanishing on `A₋ × A₋`: the fixed part is Brešar's theorem on the fixed subring, the mixed pairs are automatic, and by `ReductionEquiv.lean` the three conditions are equivalent, so a counterexample needs a nonzero defect on the mixed pairs too. The odd-odd case itself is **open** |

## Unnumbered claims

* The abstract's summary — every clause maps to a row above.
* The strengthened Theorem 4.1, the second of the two statements that close the proof of the theorem — `BSDGeneral.thm41_core` (row Thm 4.1, proof).
* the four-class dimensions `1, 1, 4, 4` on `F₅[u,v]/(u²,v²)` — `Closures` / `TwistedCommutative.UV` (row Rem 2.4). Remark 2.4's `F₅[ε]/(ε²)` sentence (paper line 262) has no Lean counterpart: it is a computation.
* The two small computations used in the characteristic-2 corner — `σ_λ = λ•id + (1+λ)•τ` acting as `(1+λ)(x∘y)` (`BSDGeneral.sigmaLam_product`, `sigmaLam_one_product`) and the triangle `μ_σ ∘ σ = μ_σ` (`muSigma_comp_sigma`) — **proved**.

## Deliberate modelling choices (statement-audit notes)

1. **Additive maps, not K-linear** (`A →+ A` where the paper says `K`-linear
   `A → A`): a strengthening, except where a statement is about dimensions
   (`Dimensions.lean`, over `ZMod 3`).
2. **The binary `σ`**: `BraidedSymmetric.lean`'s binary map and `Paper.lean`'s
   product-level `P` are exact for the four structure-free involutions and the
   `σ_α` twists; they cannot express `-id`/`-τ` over `F₃` (`N2`), which the
   pair encoding of `Background/Nonassoc.lean` and the matrix form of
   `Remark24.lean` do cover.
3. **`[IsReduced A]`** in `BSD.theorem_4_1`: strictly stronger than the paper's
   sharpest hypothesis (the `A₋`-square-zero-free form is the proved
   `BSDGeneral.thm41_core`).
4. **The deep theorems.** All three are proved in `Bresar1988.lean`
   (`bresar1988Theorem1_holds`, `cusack1975Corollary5_holds`,
   `herstein1957Theorem31_holds`), so `BSD.corollary_3_5` and its
   anti-automorphism form take no hypothesis.  The three are closed through
   Brešar's theorem, which generalizes the other two; `Background`'s conditional
   consumers are kept as the route in which each source's own proof would enter.

## What remains

Every numbered result of the paper now has a Lean counterpart, and every one of
them is proved except the cited theorem:

1. **All three cited theorems are proved** (`Bresar1988.lean`): Brešar 1988
   Theorem 1 (`bresar1988Theorem1_holds`), Cusack 1975 Corollary 5
   (`cusack1975Corollary5_holds` — the same statement) and Herstein 1957
   Theorem 3.1 (`herstein1957Theorem31_holds`, from prime ⟹ 2-torsion-free and
   semiprime).  `BSD.corollary_3_5` is unconditional.  Note the distinction the
   docstrings record: these are the *statements* of the three theorems, closed
   through Brešar's generalization, not reproductions of Herstein's 1957 or
   Cusack's 1975 arguments.
2. `BSD.theorem_4_1` assumes `[IsReduced A]`, stronger than the paper's sharpest
   hypothesis; the sharpened form is the proved `BSDGeneral.thm41_core`.
   The question whether the theorem survives dropping commutativity is reduced
   in `Reduction.lean` to the odd-odd case (`thm41_of_even_even_odd_odd`): `E`
   on `A₋ × A₋`, alternating with values in the reduced ring `A₊`.  Nothing in
   the development decides that case, and `EaNilpotent` is stated as a `Prop`
   rather than assumed anywhere.
3. `lean/lake-manifest.json` pins Mathlib, so `lake build` reproduces; the
   `lean-toolchain` bump to `v4.36.0-rc2` has not been independently re-checked
   against a second machine.
4. The binary `σ` encoding of `BraidedSymmetric.lean` / `Paper.lean` cannot
   express `-id`/`-τ` over `F₃`; the limitation is documented and the matrix
   form of `Remark24.lean` covers those rows.
