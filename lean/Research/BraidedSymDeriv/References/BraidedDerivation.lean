import Mathlib
import Research.BraidedSymDeriv.References.Basic
import Research.BraidedSymDeriv.References.Nonassoc

/-!
# Braided derivations (Różański 1996, Huru 2006) and Remark 2.5

The paper cites Różański 1996, §2 and Huru 2006, §4.1 Definition 14 for the
notion of a *braided derivation*, and asserts in Remark 2.5 that braided
derivations "form a different notion from braided-symmetric derivations,
although both use a braiding". The paper does not write the braided rule down.

The rule, in Różański 1996, Definition 2.2 (quoted from Oziewicz–Paal–Różański
1995), is: a `k`-linear `d` with

  `d ∘ m = m ∘ (d ⊗ id) + m ∘ B⁻¹ ∘ (d ⊗ id) ∘ B`,

for the multiplication `m` and the braiding `B`. On an element `x ⊗ y` this says
`d(xy) = d(x)y + m(B⁻¹(d(B(x⊗y))))`. Writing the braiding in the binary encoding
used by the paper, `B(x⊗y) = b₁(x,y) ⊗ b₂(x,y)`, `B⁻¹(x⊗y) = i₁(x,y) ⊗ i₂(x,y)`,
the rule becomes

  `d(xy) = d(x)y + i₁(d(b₁(x,y)), b₂(x,y)) · i₂(d(b₁(x,y)), b₂(x,y))`,

which is `RefBraided.braidedDerivation` below.

Huru 2006, §4.1, Definition 14 states the same rule for a *symmetry* `σ` and a
**`σ`-symmetric algebra** (`μ = μ ∘ σ`): `Der_σ(E) = {f ∈ Diff^σ_1(A,E) | f(1) = 0}`,
and "an internal homomorphism `f : A → E` is a `σ`-derivation if and only if
`f : A → E_σ ⊂ E` and `f` satisfies the braided or `σ`-Leibniz rule", equation
(20) of that paper, which in the binary encoding is
`f(ab) = f(a)b + i₁(f(b₁(a,b)), b₂(a,b)) · i₂(f(b₁(a,b)), b₂(a,b))`. Note the
hypotheses: Huru's notion is defined for `σ`-symmetric algebras and `σ`-symmetric
modules only, whereas the paper's braided-symmetric condition is defined for an
arbitrary algebra and an arbitrary involution `σ` of `A ⊗ A`. The two notions
therefore differ in their hypotheses as well as in their rule, a second reason
the paper's Remark 2.5 is not a comparison of two classes of the same objects.

**The separation.** Instantiate the braiding by the *signed swap*
`B(x⊗y) = (-y) ⊗ x`, the Koszul braiding of a `ℤ/2`-grading with `χ = -1` on odd
elements, `B⁻¹ = B`. For this `B`:

* Różański's rule collapses to the ordinary Leibniz rule, so the braided
  derivations are exactly the derivations (`braidedDerivation_signedSwap`);
* the paper's symmetrized product is `x·_{σ}y = xy + (-y)x = xy - yx`, so the
  braided-symmetric class is exactly the Lie derivations (`bsder_signedSwap`).

Since the derivations are a proper subclass of the Lie derivations
(`RefNonassoc.Witness` exhibits an additive map of `F₂ × F₂` that is a Lie
derivation and not a derivation), the two notions of the paper's Remark 2.5 are
different for this braiding: `not_braidedDerivation` exhibits a map that is
braided-symmetric and not a braided derivation. The separation in the other
direction cannot occur for this `B`, because for it the braided derivations are
contained in the braided-symmetric ones.

## Main definitions and results

* `RefBraided.Braiding`: a braiding and its inverse in the binary encoding.
* `RefBraided.braidedDerivation`: Różański 1996, Definition 2.2.
* `RefBraided.signedSwap`: the Koszul braiding `B(x⊗y) = (-y)⊗x`.
* `RefBraided.braidedDerivation_signedSwap`: for it, braided = ordinary.
* `RefBraided.bsder_signedSwap`: for it, braided-symmetric = Lie.
* `RefBraided.not_braidedDerivation`: Remark 2.5, proved for this braiding.

## References

* Różański, J.: Bicharacters, braids and Jacobi identity. arXiv:q-alg/9611029
  (1996), §2, Definition 2.2.
* Huru, H. L.: Quantizations of braided derivations. I: Monoidal categories.
  Lobachevskii J. Math. 24 (2006), 13--42, §4.1, Definition 14.
-/

namespace RefBraided

open Ref

variable {A : Type*} [Ring A]

/-- A braiding and its inverse, in the binary encoding of the paper: `B(x⊗y)`
is `b₁(x,y) ⊗ b₂(x,y)` and `B⁻¹(x⊗y)` is `i₁(x,y) ⊗ i₂(x,y)`. -/
structure Braiding (A : Type*) where
  /-- First factor of `B(x⊗y)`. -/
  b1 : A → A → A
  /-- Second factor of `B(x⊗y)`. -/
  b2 : A → A → A
  /-- First factor of `B⁻¹(x⊗y)`. -/
  i1 : A → A → A
  /-- Second factor of `B⁻¹(x⊗y)`. -/
  i2 : A → A → A

/-- **Różański 1996, Definition 2.2**: `d ∘ m = m ∘ (d ⊗ id) + m ∘ B⁻¹ ∘ (d ⊗ id)
∘ B`, written in the binary encoding. -/
def braidedDerivation (β : Braiding A) (d : A →+ A) : Prop :=
  ∀ x y : A, d (x * y) =
    d x * y + (β.i1 (d (β.b1 x y)) (β.b2 x y)) * (β.i2 (d (β.b1 x y)) (β.b2 x y))

/-- The signed swap `B(x⊗y) = (-y) ⊗ x`, with `B⁻¹ = B`: the Koszul braiding of
a `ℤ/2`-grading whose bicharacter is `-1` on odd elements (Różański 1996, §2,
equation (2.1) with `χ = -1`). -/
def signedSwap : Braiding A where
  b1 _ y := -y
  b2 x _ := x
  i1 _ y := -y
  i2 x _ := x

/-- The symmetrized product of the paper for a braiding in the binary encoding:
`x·_β y = xy + b₁(x,y)·b₂(x,y)`. -/
def symmProd (β : Braiding A) (x y : A) : A := x * y + β.b1 x y * β.b2 x y

/-- For the signed swap, the braided-symmetric product is the commutator
`xy - yx`. -/
theorem symmProd_signedSwap (x y : A) :
    symmProd (signedSwap (A := A)) x y = Ref.commutator x y := by
  simp only [symmProd, signedSwap, Ref.commutator]
  noncomm_ring

/-- **For the signed swap, Różański's braided derivations are the ordinary
derivations**: the braiding contributes exactly the second Leibniz term. -/
theorem braidedDerivation_signedSwap (d : A →+ A) :
    braidedDerivation (signedSwap (A := A)) d ↔ Der d := by
  constructor
  · intro h x y
    have h' := h x y
    simpa only [braidedDerivation, signedSwap, map_neg, neg_mul_neg] using h'
  · intro h x y
    simpa only [braidedDerivation, signedSwap, map_neg, neg_mul_neg] using h x y

/-- **For the signed swap, the braided-symmetric class is the Lie derivations**
(the `-τ` row of the paper's dictionary, which this braiding encodes). -/
theorem bsder_signedSwap (d : A →+ A) :
    (∀ x y : A, d (symmProd (signedSwap (A := A)) x y)
        = symmProd (signedSwap (A := A)) (d x) y
          + symmProd (signedSwap (A := A)) x (d y)) ↔ LieDer d := by
  simp only [symmProd, signedSwap, LieDer, Ref.commutator, neg_mul, sub_eq_add_neg]

/-- **Remark 2.5, proved for the signed swap**: the projection of `F₂ × F₂` onto
the first factor is a braided-symmetric derivation for the signed swap and not a
braided derivation. So the two notions of the paper's Remark 2.5 are different,
not merely differently presented. -/
theorem not_braidedDerivation :
    ¬ braidedDerivation (signedSwap (A := ZMod 2)) RefNonassoc.Witness.D := by
  rw [braidedDerivation_signedSwap]
  exact RefNonassoc.Witness.not_der

/-- The same map is a braided-symmetric derivation for the signed swap, so the
strictness in `not_braidedDerivation` is genuine. -/
theorem bsder_witness :
    ∀ x y : ZMod 2,
      RefNonassoc.Witness.D (symmProd (signedSwap (A := ZMod 2)) x y)
        = symmProd (signedSwap (A := ZMod 2)) (RefNonassoc.Witness.D x) y
          + symmProd (signedSwap (A := ZMod 2)) x (RefNonassoc.Witness.D y) :=
  (bsder_signedSwap _).mpr RefNonassoc.Witness.lie

end RefBraided
