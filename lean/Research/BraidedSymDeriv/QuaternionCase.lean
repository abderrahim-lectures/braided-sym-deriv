/-
# The Hilbert quaternions: the `α = id` case of Remark 4.6's open question

Remark 4.6 of the paper (v64) says that a witness against commutativity in
Theorem 4.1 must be a reduced non-commutative algebra, and that a
finite-dimensional one over a finite field cannot exist; it names the
quaternions `ℍ` over `ℝ` as the first candidate and observes that there
`α = id` gives `σ_α = τ`, so the assertion `BSDer_{σ_α}(A)^α = Der(A)^α`
becomes `JDer(ℍ) = Der(ℍ)`, which is Theorem 3.4.

This file makes that last step a theorem rather than a reference: it proves
`JDer = Der` for the Hamilton quaternions, as an instance of Brešar's theorem
(`Bresar1988.lean`) — `ℍ` is a division ring, hence 2-torsion-free and
semiprime.

Nothing here is specific to `ℝ`: the argument uses only that `ℍ` is a division
ring of characteristic zero.  The `α ≠ id` case (conjugation by a pure imaginary
quaternion) is *not* settled here; see the campaign notes.
-/
import Mathlib.Algebra.Quaternion
import Background.JordanHerstein
import Research.BraidedSymDeriv.Bresar1988

namespace QuaternionCase

open Background.JordanHerstein

/-- `ℍ = Quaternion ℝ` is 2-torsion-free: it has no zero divisors and `2 ≠ 0`. -/
theorem twoTorsionFree_quaternion : TwoTorsionFree (Quaternion ℝ) := by
  have h2ne : (2 : Quaternion ℝ) ≠ 0 := by
    intro h
    have h' : (2 : Quaternion ℝ).re = (0 : Quaternion ℝ).re := (Quaternion.ext_iff.mp h).1
    rw [show (2 : Quaternion ℝ).re = 2 from rfl, show (0 : Quaternion ℝ).re = 0 from rfl] at h'
    norm_num at h'
  intro a ha
  have h2 : (2 : Quaternion ℝ) * a = 0 := by rw [two_mul]; exact ha
  exact (mul_eq_zero.mp h2).resolve_left h2ne

/-- `ℍ` is semiprime: in a division ring `a A a = 0` forces `a = 0`, on testing
against `a⁻¹`. -/
theorem semiprime_quaternion : SemiprimeRing (Quaternion ℝ) := by
  intro a ha
  by_contra hne
  have h := ha a⁻¹
  rw [mul_inv_cancel₀ hne, one_mul] at h
  exact hne h

/-- **Theorem 3.4 at the Hilbert quaternions**: every Jordan derivation of `ℍ`
is a derivation.  This is the `α = id` case of the question Remark 4.6 leaves
open, since `α = id` gives `σ_α = τ` and `BSDer_τ = JDer`. -/
theorem jder_eq_der_quaternion (D : Quaternion ℝ →+ Quaternion ℝ) (hD : JDer D) : Der D :=
  Bresar1988.bresar1988Theorem1_apply (Quaternion ℝ) twoTorsionFree_quaternion
    semiprime_quaternion D hD

/-- The same in the form in which Remark 4.6 states the assertion. -/
theorem quaternion_jder_iff_der (D : Quaternion ℝ →+ Quaternion ℝ) : JDer D ↔ Der D :=
  ⟨jder_eq_der_quaternion D, der_jder⟩

end QuaternionCase

#print axioms QuaternionCase.jder_eq_der_quaternion
#print axioms QuaternionCase.quaternion_jder_iff_der
