/-
# Axiom audit of the load-bearing declarations

One `#print axioms` per declaration the paper's claims rest on.  The gate
(`tools/papercheck.py`) runs this file after `lake build` and fails unless
every footprint is inside `{propext, Classical.choice, Quot.sound}`, with the
two `native_decide` theorems of `Triangular.lean` (on v54-orphaned material)
as the enumerated exceptions, each carrying
`<name>._native.native_decide.ax_1_1`.

The three anonymous `native_decide` examples of `Counterexamples.lean`
(lines 158, 386, 419) cannot be named by `#print axioms` at all; they are
enumerated in the gate's source scan instead.

This file also doubles as the import-clash regression test: it imports
`BraidedSymmetric` (whose root-namespace `LieDerivation` used to clash with
`Mathlib.Algebra.Lie.Derivation.Basic`, making the two halves of the
development mutually unimportable) together with modules that import Mathlib.
-/
import Research.BraidedSymDeriv.BraidedSymmetric
import Research.BraidedSymDeriv.TwistedCommutative
import Research.BraidedSymDeriv.Paper
import Research.BraidedSymDeriv.General
import Research.BraidedSymDeriv.Reduction
import Research.BraidedSymDeriv.Counterexamples
import Research.BraidedSymDeriv.Remark24
import Research.BraidedSymDeriv.Remark46
import Research.BraidedSymDeriv.Dimensions
import Research.BraidedSymDeriv.Example45b
import Research.BraidedSymDeriv.JordanDerivation
import Research.BraidedSymDeriv.Bresar1988
import Research.BraidedSymDeriv.QuaternionCase
import Research.BraidedSymDeriv.AntiAutomorphism
import Research.BraidedSymDeriv.Triangular
import Research.BraidedSymDeriv.BaseChange

/-! ## BraidedSymmetric (the library) -/

#print axioms BraidedSymDeriv.jordanDerivation_of_braidedSymmetricDerivation_std
#print axioms BraidedSymDeriv.braidedSymmetricDerivation_of_jordanDerivation_std
#print axioms BraidedSymDeriv.braidedSymmetricDerivation_id_iff_Der
#print axioms BraidedSymDeriv.braidedSymmetricDerivation_id_of_two_eq_zero
#print axioms BraidedSymDeriv.Der.subset_JDer
#print axioms BraidedSymDeriv.innerDerivation_mem_Der
#print axioms BraidedSymDeriv.Der.subset_LDer
#print axioms BraidedSymDeriv.LieDerivation.add_central
#print axioms BraidedSymDeriv.BraidedSymDerivTrace.traceScalar_lie_not_der

/-! ## TwistedCommutative: Proposition 3.2 and Theorem 4.1 -/

#print axioms leibnizDefect_comm
#print axioms leibnizDefect_cocycle
#print axioms twisted_defect_sq_zero
#print axioms twisted_commutative
#print axioms prop_defect_aut
#print axioms prop_defect_anti
#print axioms der_twisted_iff_comm

/-! ## Paper: the dictionary, the bridge, Theorem 4.1, Corollary 3.5 -/

#print axioms BSD.bsderP_two_mul_iff
#print axioms BSD.bsderP_jordan_iff
#print axioms BSD.bsderP_zero
#print axioms BSD.bsderP_commutator_iff
#print axioms BSD.symm_alpha
#print axioms BSD.bsderP_alpha_iff
#print axioms BSD.der_jder
#print axioms BSD.theorem_4_1
#print axioms BSD.corollary_3_5
#print axioms BSD.jder_iff_background
#print axioms BSD.jder_eq_der_of_semiprime
#print axioms BSD.corollary_3_5_unconditional
#print axioms BSD.alpha_half
#print axioms BSD.refinement
#print axioms BSD.innerDer_der
#print axioms BSD.innerDer_comm_iff
#print axioms BSD.innerDer_twisted_iff
#print axioms BSD.innerDer_comm_iff_center
#print axioms BSD.innerDer_twisted_iff_center
#print axioms BSD.innAlpha_eq
#print axioms BSD.Example43.comm
#print axioms BSD.Example43.twisted
#print axioms BSD.Example43.not_der
#print axioms BSD.Example23.not_assoc
#print axioms BSD.Example23.no_unit

/-! ## Counterexamples: the finite witnesses -/

#print axioms BraidedSymDerivCounterexamples.Dm_der
#print axioms BraidedSymDerivCounterexamples.Dm_comm_trans
#print axioms BraidedSymDerivCounterexamples.Dm_symp
#print axioms BraidedSymDerivCounterexamples.ex45a_alphaDeriv
#print axioms BraidedSymDerivCounterexamples.ex45a_braided
#print axioms BraidedSymDerivCounterexamples.ex45a_commutes
#print axioms BraidedSymDerivCounterexamples.ex45a_derivation
#print axioms BraidedSymDerivCounterexamples.ex45a_tuple
#print axioms BraidedSymDerivCounterexamples.ex45a_not_alpha

/-! ## Remark24: the classification of the natural involutions -/

#print axioms Remark24.natural_form
#print axioms Remark24.natural_involution_arith
#print axioms Remark24.natural_involution_char_ne_two
#print axioms Remark24.natural_involution_char_two
#print axioms Remark24.reflection_sq
#print axioms Remark24.idempotent_reflection
#print axioms Remark24.char_two_reflection_trivial

/-! ## Remark46: the counterexample of Theorem 4.1's commutativity hypothesis -/

#print axioms BSD.Remark46.assoc
#print axioms BSD.Remark46.one_mul
#print axioms BSD.Remark46.mul_one
#print axioms BSD.Remark46.alpha_mul
#print axioms BSD.Remark46.alpha_involutive
#print axioms BSD.Remark46.comm
#print axioms BSD.Remark46.leibniz
#print axioms BSD.Remark46.not_deriv
#print axioms BSD.Remark46.defect_vw
#print axioms BSD.Remark46.skew_sq_zero

/-! ## Dimensions: the two finrank counts of Remark 4.6 and the witness `U₁` -/

#print axioms Remark46Dim.derα_eq_span
#print axioms Remark46Dim.finrank_derα
#print axioms Remark46Dim.bsderα_eq_span
#print axioms Remark46Dim.finrank_bsderα
#print axioms Remark46Dim.U₁_jder
#print axioms Remark46Dim.U₁_not_der

/-! ## Example45b: the dual numbers in char ≠ 2 and in char 2 -/

#print axioms Ex45b.Dε_der
#print axioms Ex45b.Dε_ader
#print axioms Ex45b.Dε_bsder
#print axioms Ex45b.bsderαSub_eq_span
#print axioms Ex45b.finrank_bsderαSub
#print axioms Ex45b.finrank_derSub
#print axioms Ex45b.finrank_aderSub
#print axioms Ex45b.alphaLin_eq_id_of_char_two
#print axioms Ex45b.bsderSub_eq_top
#print axioms Ex45b.finrank_bsderSub_of_char_two
#print axioms Ex45b.finrank_derSub_of_char_two
#print axioms Ex45b.aderSub_eq_derSub

/-! ## General: Section 2's triangle and the characteristic-2 family of Remark 2.4 -/

#print axioms BSDGeneral.muSigma_comp_sigma
#print axioms BSDGeneral.tauSwap_involution
#print axioms BSDGeneral.neg_eq_self_of_char_two
#print axioms BSDGeneral.neg_tauSwap_eq_tauSwap
#print axioms BSDGeneral.tauSwap_self
#print axioms BSDGeneral.sigmaLam_involution
#print axioms BSDGeneral.sigmaLam_product
#print axioms BSDGeneral.sigmaLam_one_product

/-! ## Reduction: the open question of Remark 4.6 reduced to one nilpotency -/

#print axioms BSDGeneral.Ea_eq_lie
#print axioms BSDGeneral.Ea_skew
#print axioms BSDGeneral.Ed_alpha_of_fixed
#print axioms BSDGeneral.Ed_alpha_of_fixed_skew
#print axioms BSDGeneral.Ed_alpha_of_skew_fixed
#print axioms BSDGeneral.Ed_alpha_of_skew_skew
#print axioms BSDGeneral.Ea_eq_zero_of_fixed_skew
#print axioms BSDGeneral.Ea_add_left
#print axioms BSDGeneral.Ea_add_right
#print axioms BSDGeneral.thm41_of_even_even_odd_odd
#print axioms BSDGeneral.alpha_one
#print axioms BSDGeneral.fixedSubring
#print axioms BSDGeneral.Dfix
#print axioms BSDGeneral.jder_Dfix
#print axioms BSDGeneral.twoTorsionFree_fixedSubring
#print axioms BSDGeneral.semiprime_fixedSubring
#print axioms BSDGeneral.Ed_eq_zero_of_fixed
#print axioms BSDGeneral.thm41_of_odd_odd
#print axioms BSDGeneral.symm_iff_Ea_zero
#print axioms BSDGeneral.Ea_alpha_fixed
#print axioms BSDGeneral.Ea_eq_zero_of_comm
#print axioms BSDGeneral.EaNilpotent_of_comm
#print axioms BSDGeneral.eq_zero_of_pow_eq_zero
#print axioms BSDGeneral.thm41_of_nilpotent_Ea
#print axioms BSDGeneral.thm41_of_sq_zero_Ea

/-! ## Bresar1988: Brešar's theorem, proved -/

#print axioms Bresar1988.jordan_derivation_eq_derivation
#print axioms Bresar1988.bresar1988Theorem1_holds
#print axioms Bresar1988.bresar1988Theorem1_apply
#print axioms Bresar1988.cusack1975Corollary5_holds
#print axioms Bresar1988.herstein1957Theorem31_holds

/-! ## QuaternionCase: the `α = id` case of Remark 4.6's question, at `ℍ` -/

#print axioms QuaternionCase.twoTorsionFree_quaternion
#print axioms QuaternionCase.semiprime_quaternion
#print axioms QuaternionCase.jder_eq_der_quaternion
#print axioms QuaternionCase.quaternion_jder_iff_der

/-! ## JordanDerivation: the elementary layer of Brešar 1988 -/

#print axioms JordanDerivation.eq_of_two_mul_eq
#print axioms JordanDerivation.jder_triple
#print axioms JordanDerivation.jder_quad
#print axioms JordanDerivation.defect_add_left
#print axioms JordanDerivation.defect_add_right
#print axioms JordanDerivation.defect_self
#print axioms JordanDerivation.defect_mul_right
#print axioms JordanDerivation.defect_cocycle
#print axioms JordanDerivation.defect_mul_of_ideal
#print axioms JordanDerivation.bresar_lemma4
#print axioms JordanDerivation.defect_skew
#print axioms JordanDerivation.defect_theorem3
#print axioms JordanDerivation.defect_mul_commutator_eq_zero
#print axioms JordanDerivation.bresar1988Theorem1_of_defectGap
#print axioms JordanDerivation.jder_eq_der_of_commutative
#print axioms JordanDerivation.defect_eq_zero_of_essential

/-! ## AntiAutomorphism: the anti-automorphism halves of Remark 3.3 / Corollary 3.5 -/

#print axioms AntiAutomorphism.der_twisted_iff_comm_anti
#print axioms AntiAutomorphism.corollary_3_5_anti
#print axioms AntiAutomorphism.corollary_3_5_anti_unconditional

/-! ## Triangular (v54-orphaned): the two native_decide theorems -/

#print axioms jordanDerivation_eq_derivation_tri
#print axioms lieDerivation_standard_tri
#print axioms tau_isLieDerivation

/-! ## BaseChange (v54-orphaned, kept for reference) -/

#print axioms kerBaseChangeEquiv
#print axioms finrank_ker_baseChange
