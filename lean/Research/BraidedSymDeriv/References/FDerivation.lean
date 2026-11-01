import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# `f`-derivations (Benkovič 2015) and maps that act as derivations on one
# multilinear polynomial (Beidar, Brešar, Chebotar, Martindale 2001)

The paper (§1, lines 99--100) recalls that Benkovič 2015, §1 treats derivations,
Jordan derivations and Lie derivations as `f`-derivations, for `f = x₁x₂`,
`f = x₁ ∘ x₂` and `f = [x₁, x₂]`, "so that one identity for a multilinear
polynomial `f` covers all three", and notes that Beidar, Brešar, Chebotar and
Martindale 2001, Theorem 4.3 studied maps that act as derivations on a fixed
multilinear polynomial, earlier than Benkovič.

This module formalizes the general notion for a polynomial `f` in `n` variables
(`RefFDerivation.fDerivation`) and the three binary instances as definitional
equivalences. The paper imports no theorem from these two entries — the
citations date the notion — so nothing here is stated as a hypothesis that the
catalogue would need: the content of the two references that the paper uses is
the *definition*, and that is what is formalized.

## Main definitions and results

* `RefFDerivation.fDerivation f D`: `D (f v) = ∑ i, f (v with i ↦ D (v i))`.
* `RefFDerivation.fDerivation₂ f D`: the binary form.
* `RefFDerivation.mul_iff`, `jordan_iff`, `commutator_iff`: the three instances
  of Benkovič 2015, §1, each definitional.
* `RefFDerivation.one_var`: in one variable the notion is `D (f ()) = f ()`-free
  — recorded to show that the arity is part of the definition.

## References

* Benkovič, D.: A note on `f`-derivations of triangular algebras. Aequationes
  Math. 89 (2015), 1207--1211, §1.
* Beidar, K. I., Brešar, M., Chebotar, M. A., Martindale, W. S., III: On
  Herstein's Lie map conjectures, II. J. Algebra 238 (2001), 239--264,
  Theorem 4.3.
-/

namespace RefFDerivation

open Ref

variable {A : Type*} [Ring A]

/-- An `f`-derivation in the sense of Benkovič 2015, §1: `D` acts as a derivation
on the single polynomial `f` of `n` variables,
`D (f v) = ∑ i, f (v with vᵢ replaced by D (vᵢ))`. Multilinearity of `f` is not
part of the definition (Benkovič assumes it); it is what makes the notion
equivalent to the classical ones in arity two. -/
def fDerivation {n : ℕ} (f : (Fin n → A) → A) (D : A →+ A) : Prop :=
  ∀ v : Fin n → A, D (f v) = ∑ i : Fin n, f (Function.update v i (D (v i)))

/-- The binary form of `fDerivation`, which is the form the three classical
notions take. -/
def fDerivation₂ (f : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (f x y) = f (D x) y + f x (D y)

/-- The general definition at arity two is the binary form. -/
theorem fDerivation_iff₂ {f : A → A → A} {D : A →+ A} :
    fDerivation (fun v : Fin 2 → A => f (v 0) (v 1)) D ↔ fDerivation₂ f D := by
  constructor
  · intro h x y
    have h' := h (fun i => if (i : ℕ) = 0 then x else y)
    simpa [fDerivation, fDerivation₂, Fin.sum_univ_two] using h'
  · intro h v
    have h' := h (v 0) (v 1)
    simpa [fDerivation, fDerivation₂, Fin.sum_univ_two] using h'

/-- **Benkovič 2015, §1**, first instance: for `f = x₁x₂` an `f`-derivation is a
derivation. -/
theorem mul_iff (D : A →+ A) : fDerivation₂ (fun x y => x * y) D ↔ Der D :=
  Iff.rfl

/-- **Benkovič 2015, §1**, second instance: for `f = x₁ ∘ x₂ = x₁x₂ + x₂x₁` an
`f`-derivation is a Jordan derivation. -/
theorem jordan_iff (D : A →+ A) : fDerivation₂ (fun x y => x * y + y * x) D ↔ JDer D :=
  Iff.rfl

/-- **Benkovič 2015, §1**, third instance: for `f = [x₁, x₂]` an `f`-derivation
is a Lie derivation. -/
theorem commutator_iff (D : A →+ A) :
    fDerivation₂ (fun x y => x * y - y * x) D ↔ LieDer D :=
  Iff.rfl

/-- In arity one, `fDerivation` says only `D (f v) = f (D (v 0))`: the arity and
the polynomial are part of the definition, so the family is genuinely indexed by
`f`, not a reformulation of one condition. -/
theorem fDerivation_one {f : A → A} {D : A →+ A} (h : fDerivation (fun v : Fin 1 → A => f (v 0)) D) (x : A) :
    D (f x) = f (D x) := by
  have h' := h (fun _ => x)
  simpa using h'

end RefFDerivation
