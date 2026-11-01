import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# `α`-derivations (Hosseini–Mohammadzadeh Karizaki 2019)

The paper (§2, line 187) recalls: "For an automorphism `α` of `A`, an
`α`-derivation satisfies `D(xy) = D(x)α(y) + α(x)D(y)` (Hosseini and
Mohammadzadeh Karizaki 2019, §1). We write `Der_α(A)` for this space." Section 4
then compares `Der_α(A)` with the twisted class `BSDer_{σ_α}(A)^α`: Proposition
4.4 shows on `F₃[ε]/(ε³)` that neither contains the other, and Example 4.5 shows
that the two classes can meet.

This module formalizes the definition, the degeneration `α = id` to the ordinary
derivations, the closure of `Der_α(A)` under addition, and the bridge between the
paper's `σ_α`-Leibniz rule and the `α`-derivation identity. The finite witness of
Proposition 4.4 is kernel-checked in `Counterexamples.lean` (namespace `TW`) and
is not duplicated here; what is duplicated from `Paper.lean` is the *bridge*
(`bsderP_alpha_iff` there), restated against this module's own definitions so
that the module can be read alone.

## Main results

* `RefAlpha.AlphaDer`: the `α`-derivation identity.
* `RefAlpha.alphaDer_id_iff`: for `α = id` it is the derivation identity.
* `RefAlpha.alphaDer_add`: `Der_α(A)` is closed under addition.
* `RefAlpha.symmProd`, `RefAlpha.TwistedAlpha`: the paper's symmetrized product
  `x·_{σ_α}y = xy + α(y)α(x)` and its Leibniz rule.
* `RefAlpha.bsder_iff_twisted`: the two forms of the twisted condition agree.

## References

* Hosseini, A., Mohammadzadeh Karizaki, M.: Functional equations characterizing
  `σ`-derivations. Acta Sci. Math. (Szeged) 85 (2019), 431--440, §1.
-/

namespace RefAlpha

open Ref

variable {A : Type*} [Ring A]

/-- **Hosseini–Mohammadzadeh Karizaki 2019, §1**: `D` is an `α`-derivation if
`D(xy) = D(x)α(y) + α(x)D(y)` for all `x, y`. -/
def AlphaDer (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (x * y) = D x * α y + α x * D y

/-- For `α = id` an `α`-derivation is a derivation: this is the definitional
degeneration the paper uses to place `Der(A)` inside the `α`-derivations. -/
theorem alphaDer_id_iff (D : A →+ A) : AlphaDer (RingHom.id A) D ↔ Der D :=
  Iff.rfl

/-- Every derivation is an `α`-derivation for `α = id`. -/
theorem der_alphaDer_id {D : A →+ A} (h : Der D) : AlphaDer (RingHom.id A) D :=
  h

/-- `Der_α(A)` is closed under addition: the condition is linear in `D`. -/
theorem alphaDer_add {α : A →+* A} {D E : A →+ A}
    (hD : AlphaDer α D) (hE : AlphaDer α E) : AlphaDer α (D + E) := by
  intro x y
  simp only [AddMonoidHom.add_apply, hD x y, hE x y]
  noncomm_ring

/-- The zero map is an `α`-derivation. -/
theorem alphaDer_zero (α : A →+* A) : AlphaDer α 0 := by
  intro x y
  simp

/-! ## The paper's `σ_α`-product and its Leibniz rule

For an involutive automorphism `α`, the paper's braiding is
`σ_α(x ⊗ y) = α(y) ⊗ α(x)`, whose symmetrized product is
`x ·_{σ_α} y = xy + α(y)α(x)`. In the binary encoding of `Paper.lean` the
braiding is written `σ x y = α y`, so that `σ y x = α x`. -/

/-- The symmetrized product `x ·_σ y = xy + σ(x,y)·σ(y,x)` of Definition 2.1. -/
def symmProd (σ : A → A → A) (x y : A) : A := x * y + σ x y * σ y x

/-- The paper's `σ_α`-Leibniz rule, in the form of `Paper.lean`'s
`TwistedAlpha`. -/
def TwistedAlpha (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (x * y + α (y * x)) =
    D x * y + α (y * D x) + (x * D y + α (D y * x))

/-- **The bridge**: the Leibniz rule for the product `x·_{σ_α}y` is the paper's
twisted identity. Both sides are the same condition after `α` is applied to a
product; this is `Paper.lean`'s `bsderP_alpha_iff`, restated here. -/
theorem bsder_iff_twisted (α : A →+* A) (D : A →+ A) :
    (∀ x y : A, D (symmProd (fun _ y => α y) x y)
        = symmProd (fun _ y => α y) (D x) y + symmProd (fun _ y => α y) x (D y))
      ↔ TwistedAlpha α D := by
  constructor
  · intro h x y
    have h' := h x y
    simpa only [symmProd, TwistedAlpha, map_mul] using h'
  · intro h x y
    have h' := h x y
    simpa only [symmProd, TwistedAlpha, map_mul] using h'

/-- The product `x ·_{σ_α} y = xy + α(y)α(x)` of the paper, equation (3.1): for
an automorphism `α`, `α(y)α(x) = α(yx)`. -/
theorem symmProd_alpha (α : A →+* A) (x y : A) :
    symmProd (fun _ y => α y) x y = x * y + α (y * x) := by
  simp only [symmProd, map_mul]

end RefAlpha
