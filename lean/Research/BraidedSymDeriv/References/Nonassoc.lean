import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# Derivations of nonassociative algebras (Jacobson 1937), Lie derivations
# (Martindale 1964)

The paper cites Jacobson 1937, Part I, for the notion of a derivation of an
arbitrary nonassociative algebra and uses it at §2 (line 238): the
braided-symmetric condition for a product `·_σ` *is* the Leibniz rule for that
product, so `BSDer_σ(A)` is the set of derivations of the nonassociative algebra
`(A, ·_σ)`.

Martindale 1964, p. 183 is cited for the definition of a Lie derivation,
`D([x,y]) = [D(x), y] + [x, D(y)]`. The paper uses only the definition (it never
quotes a structure theorem), so this module formalizes the definition, the fact
that it is the same condition as a derivation of the commutator product, and a
witness that the class is strictly larger than the derivations — which is why
the `−τ` row of the paper's dictionary (Remark 2.4) is a separate row.

## Main definitions and results

* `RefNonassoc.NonassocDer`: Jacobson's condition for a product `mul`.
* `RefNonassoc.bsder_iff`: `BSDer_σ` is `NonassocDer` for `·_σ` (paper, line 238).
* `RefNonassoc.commutator_iff_lieDer`: `NonassocDer` for the commutator is
  Martindale's `LieDer`.
* `RefNonassoc.Witness`: over `F₂ × F₂`, an additive map that is a Lie
  derivation and not a derivation.

## References

* Jacobson, N.: Abstract derivation and Lie algebras. Trans. Amer. Math. Soc. 42
  (1937), 206--224, Part I.
* Martindale, W. S., III: Lie derivations of primitive rings. Michigan Math. J.
  11 (1964), 183--187, p. 183.
-/

namespace RefNonassoc

open Ref

variable {A : Type*} [Ring A]

/-- A derivation of the nonassociative algebra `(A, mul)`, Jacobson 1937,
Part I: `D(mul x y) = mul (D x) y + mul x (D y)`. No associativity of `mul` is
assumed, and none is used. -/
def NonassocDer (mul : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (mul x y) = mul (D x) y + mul x (D y)

/-- **Paper, §2, line 238.** For the symmetrized product `x ·_σ y = xy + σ x y *
σ y x` the braided-symmetric derivation condition of Definition 2.2 is exactly
Jacobson's derivation condition for the product `·_σ`. -/
theorem bsder_iff (σ : A → A → A) (D : A →+ A) :
    (∀ x y : A, D (x * y + σ x y * σ y x)
        = ((D x) * y + σ (D x) y * σ y (D x))
          + (x * (D y) + σ x (D y) * σ (D y) x))
      ↔ NonassocDer (fun x y => x * y + σ x y * σ y x) D :=
  Iff.rfl

/-- Every additive map is a derivation of the zero product, so the `−id` row of
the paper's dictionary is the whole of `End_K(A)` (paper, Remark 2.4). -/
theorem zero_mul (D : A →+ A) : NonassocDer (fun _ _ => (0 : A)) D := by
  intro x y
  simp

/-- **Martindale 1964, p. 183**, read as a derivation of the commutator product:
a Lie derivation is a derivation of `(A, [·,·])` in Jacobson's sense. -/
theorem commutator_iff_lieDer (D : A →+ A) :
    NonassocDer (fun x y => x * y - y * x) D ↔ LieDer D := by
  simp only [NonassocDer, LieDer, Ref.commutator]

/-- The Jordan product `x ∘ y = xy + yx` is the symmetrized product for the swap,
so the swap row of the dictionary is the `NonassocDer` condition for `∘`
(paper, Remark 2.4, and Jacobson 1937 for the notion). -/
theorem jordan_iff_jDer (D : A →+ A) :
    NonassocDer (fun x y => x * y + y * x) D ↔ JDer D := by
  simp only [NonassocDer, JDer, Ref.jordan]

/-- **In a commutative ring every additive map is a Lie derivation**: the
commutator vanishes, so the two sides of Martindale's identity are both zero.
This is the reason the `−τ` row of the paper's dictionary is larger than the
derivations, and it is what makes the witness below cheap. -/
theorem lieDer_of_comm {A : Type*} [CommRing A] (D : A →+ A) : LieDer D := by
  intro x y
  simp only [Ref.commutator, mul_comm, sub_self, map_zero, add_zero]

/-! ## The class of Lie derivations is strictly larger than the derivations

Martindale's definition would be uninteresting if it coincided with `Der`. In a
commutative ring of characteristic 2 the identity map is multiplicative, hence
additive, and is a Lie derivation, but it is not a derivation because `1 + 1 = 0`
while `D(1) = 1`. -/

namespace Witness

/-- The field `F₂`, commutative of characteristic two. -/
abbrev F2 : Type := ZMod 2

/-- The identity map of `F₂`, additive. -/
def D : F2 →+ F2 := AddMonoidHom.id F2

/-- `D` is a Lie derivation: the ring is commutative (`lieDer_of_comm`). -/
theorem lie : LieDer D := lieDer_of_comm D

/-- `D` is not a derivation: `D(1·1) = 1`, while `D(1)·1 + 1·D(1) = 1 + 1 = 0`. -/
theorem not_der : ¬ Der D := by
  intro h
  have h1 := h 1 1
  simp only [D, AddMonoidHom.id_apply, mul_one] at h1
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h2] at h1
  exact one_ne_zero h1

end Witness

end RefNonassoc
