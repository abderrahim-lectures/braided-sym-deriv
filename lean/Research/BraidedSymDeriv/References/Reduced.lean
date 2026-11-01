import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# Reduced commutative algebras

Chambert-Loir, *(Mostly) Commutative Algebra*, Universitext, Springer 2021,
1.4.12, is cited in the paper (§2, line 172) for the definition: a commutative
algebra is **reduced** if its only nilpotent element is zero. This is exactly
Mathlib's `IsReduced`, stated for any structure with `0` and a power operation:
`IsReduced R` says `∀ x, IsNilpotent x → x = 0`.

The paper uses reducedness twice. In Theorem 4.1 (reduced commutative algebras)
the hypothesis turns the identity `e * e = 0` of the defect computation into
`e = 0`; that is `RefReduced.mul_self_eq_zero` below. In §1 the paper contrasts
reduced algebras with prime and semiprime rings (Brešar 1988, p. 1003); for a
commutative ring the three conditions reduced, semiprime and "no nonzero square
zero element" agree, which is `isReduced_iff_semiprime` below.

## Main results

* `RefReduced.isReduced_iff_no_nilpotent`: Chambert-Loir's definition.
* `RefReduced.mul_self_eq_zero`: the form in which Theorem 4.1 uses it.
* `RefReduced.isReduced_iff_semiprime`: for a commutative ring, reduced is
  Brešar's semiprime condition.
* `RefReduced.dualNumber_not_reduced`: the standard witness that reducedness is
  not automatic (`ε ≠ 0`, `ε² = 0`), the shape of the paper's Example 4.2.

## References

* Chambert-Loir, A.: (Mostly) Commutative Algebra. Universitext. Springer, Cham
  (2021), 1.4.12.
* Bresar, M.: Jordan derivations on semiprime rings. Proc. Amer. Math. Soc. 104
  (1988), 1003--1006.
-/

namespace RefReduced

open Ref

/-- Chambert-Loir 2021, 1.4.12: a ring is reduced when its only nilpotent
element is zero. This is Mathlib's definition of `IsReduced`, restated. -/
theorem isReduced_iff_no_nilpotent {A : Type*} [CommRing A] :
    IsReduced A ↔ ∀ x : A, IsNilpotent x → x = 0 :=
  isReduced_iff (R := A)

/-- The form in which Theorem 4.1 of the paper uses reducedness: a square-zero
element vanishes. -/
theorem mul_self_eq_zero {A : Type*} [CommRing A] [IsReduced A] {x : A}
    (h : x * x = 0) : x = 0 :=
  IsReduced.eq_zero x ⟨2, by simpa [pow_two] using h⟩

/-- A reduced commutative ring is semiprime in the sense of Bresar 1988,
p. 1003. -/
theorem isReduced_imp_semiprime {A : Type*} [CommRing A] (h : IsReduced A) :
    SemiprimeRing A := by
  intro a ha
  exact h.eq_zero a ⟨2, by simpa [pow_two] using ha 1⟩

/-- In a commutative ring, a nilpotent element has a nilpotent half: if
`x ^ n = 0` with `n ≥ 2`, then `x ^ (n - 1)` is a square-zero element. This is
the induction step of `isReduced_iff_semiprime`. -/
theorem pow_pred_sq_eq_zero {A : Type*} [CommRing A] {x : A} {n : ℕ} (hn : 2 ≤ n)
    (h : x ^ n = 0) : x ^ (n - 1) * x ^ (n - 1) = 0 := by
  rw [← pow_add, show n - 1 + (n - 1) = (n - 2) + n by omega, pow_add, h, mul_zero]

/-- For a commutative ring, Bresar's semiprime condition and reducedness agree;
this is the form in which the paper's hypotheses on `A` meet Chambert-Loir's
definition. -/
theorem isReduced_iff_semiprime {A : Type*} [CommRing A] :
    IsReduced A ↔ SemiprimeRing A := by
  refine ⟨isReduced_imp_semiprime, fun h => ?_⟩
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases n with _ | _ | m
    · rw [pow_zero] at hn
      calc x = x * 1 := (mul_one x).symm
        _ = x * 0 := by rw [← hn]
        _ = 0 := mul_zero x
    · simpa using hn
    · have hsq : x ^ (m + 1) * x ^ (m + 1) = 0 := by
        rw [← pow_add, show m + 1 + (m + 1) = m + (m + 2) by omega, pow_add, hn, mul_zero]
      have hzero : x ^ (m + 1) = 0 := by
        refine h _ (fun r => ?_)
        rw [mul_assoc, mul_comm r, ← mul_assoc, hsq, zero_mul]
      exact ih (m + 1) (by omega) x hzero

/-- The dual numbers are not reduced: `ε ≠ 0` and `ε ^ 2 = 0`, the standard
counterexample to reducedness (and the shape of the paper's Example 4.2). -/
theorem eps_ne_zero (K : Type*) [Field K] : (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.snd h
  simp at h1

theorem dualNumber_not_reduced (K : Type*) [Field K] : ¬ IsReduced (DualNumber K) := by
  intro h
  have hsq : (DualNumber.eps : DualNumber K) * DualNumber.eps = 0 := DualNumber.eps_mul_eps
  exact eps_ne_zero K (mul_self_eq_zero hsq)

end RefReduced
