/-
# The anti-automorphism halves of Remark 3.3 and Corollary 3.5

The paper states the first part of Remark 3.3 (l. 415) and Corollary 3.5
(l. 441) for an involutive automorphism **or anti-automorphism** α.  The
repository's `BSD.der_twisted_iff_comm` and `BSD.corollary_3_5` (in
`Paper.lean`, on `TwistedCommutative.lean`) take `α : A ≃+* A`, an
automorphism; this file carries the anti-automorphism halves, which were
absent from the development until the v63 review.

For an anti-automorphism the σ_α-symmetrized product is
`xy + α(y)α(x) = xy + α(xy)`, so the transported identity is `TwistedAlphaAnti`
below.  Everything is stated for an `α` that is an additive bijection with
`α (x * y) = α y * α x` and `α 1 = 1` — an involutive anti-automorphism in the
paper's sense (Remark 3.1, Herstein 1976 §1.2) is such a map with
`α (α x) = x`, which the statements do not need.

No `sorry`, no `native_decide`; the proofs rest only on
`propext, Classical.choice, Quot.sound`.
-/
import Research.BraidedSymDeriv.Paper

namespace AntiAutomorphism

variable {R : Type*} [Ring R]

/-- The `σ_α`-identity of the paper for an anti-automorphism `α`. -/
def TwistedAlphaAnti (α : R → R) (D : R →+ R) : Prop :=
  ∀ x y, D (x * y + α y * α x) = D x * y + α y * α (D x) + (x * D y + α (D y) * α x)

/-- **Remark 3.3, first part, anti-automorphism case**: a derivation satisfies the
`σ_α`-identity exactly when it commutes with `α`. -/
theorem der_twisted_iff_comm_anti (α : R ≃+ R)
    (hmul : ∀ x y : R, α (x * y) = α y * α x) (h1 : α 1 = 1) (D : R →+ R)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    TwistedAlphaAnti (⇑α) D ↔ ∀ z, D (α z) = α (D z) := by
  have hD1 : D 1 = 0 := by
    have h := hD 1 1
    rw [one_mul, mul_one, one_mul] at h
    exact left_eq_add.mp h
  constructor
  · intro h z
    have hz := h 1 z
    simp only [TwistedAlphaAnti, one_mul, mul_one, h1, hD1, map_zero, zero_mul,
      mul_zero, zero_add, map_add] at hz
    exact add_left_cancel hz
  · intro h x y
    have : TwistedAlphaAnti (⇑α) D := by
      intro a b
      rw [← hmul a b, map_add, h (a * b), hD a b]
      simp only [map_add, hmul]
      abel
    exact this x y

/-- **Corollary 3.5, anti-automorphism case**, conditional on Brešar's theorem
(every Jordan derivation is a derivation), exactly as `BSD.corollary_3_5` is. -/
theorem corollary_3_5_anti (α : R ≃+ R) (hmul : ∀ x y : R, α (x * y) = α y * α x)
    (h1 : α 1 = 1) (D : R →+ R) (hDα : ∀ z, D (α z) = α (D z))
    (hBresar : ∀ E : R →+ R, BSD.JDer E → BSD.Der E) :
    (TwistedAlphaAnti (⇑α) D ∧ BSD.JDer D) ↔ BSD.Der D := by
  constructor
  · rintro ⟨-, hJ⟩
    exact hBresar D hJ
  · intro hD
    exact ⟨(der_twisted_iff_comm_anti α hmul h1 D hD).2 hDα, BSD.der_jder hD⟩

#print axioms der_twisted_iff_comm_anti
#print axioms corollary_3_5_anti

end AntiAutomorphism
