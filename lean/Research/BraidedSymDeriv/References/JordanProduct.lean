import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# The Jordan product and quasi-multiplication (Jordan–von Neumann–Wigner 1934,
# Brešar–Zelmanov 2025)

The paper (§1, lines 102--104, 118) says: "The sum `xy + yx` is twice the Jordan
product `½(xy + yx)` of an associative algebra (Brešar–Zelmanov 2025,
Example 2.1)", and: "Jordan, von Neumann and Wigner form a product `ab` from the
two products `a × b` and `b × a` of an associative system, and call this
quasi-multiplication (Jordan–von Neumann–Wigner 1934, p. 64)." The paper then
follows Herstein and uses `x ∘ y = xy + yx`, without the half, so that
characteristic 2 is allowed.

This module formalizes:

* quasi-multiplication for an arbitrary product on an additive group, its
  commutativity, and the fact that for the product of an associative ring it is
  the paper's `x ∘ y` (Jordan–von Neumann–Wigner 1934, p. 64);
* the **Jordan identity** for quasi-multiplication of an associative algebra —
  the reason the construction produces a Jordan algebra at all. This is a real
  theorem of the reference, not a definitional identity;
* the factor 2 that separates the paper's product from the survey's: over a
  `ℚ`-algebra, `2 • (½(xy + yx)) = x ∘ y`, so the two products have the same
  derivations but are not the same product (Brešar–Zelmanov 2025, Example 2.1).

The paper's use of the factor is only lexical, but the distinction matters in
characteristic 2, where `½` does not exist: the paper's `∘` form is then the
right one, and its Remark 2.4 records that in a commutative algebra of
characteristic 2 the product vanishes and every linear map satisfies the `∘`
condition.

## Main results

* `RefJordanProduct.quasiMul`: `(x, y) ↦ mul x y + mul y x`.
* `RefJordanProduct.quasiMul_comm`.
* `RefJordanProduct.quasiMul_eq_jordan`: for the ring product it is `Ref.jordan`.
* `RefJordanProduct.jordan_identity`: `(x∘y)∘(x∘x) = x∘(y∘(x∘x))`.
* `RefJordanProduct.jordan_eq_two_smul_half`: the factor 2 over `ℚ`.

## References

* Jordan, P., von Neumann, J., Wigner, E.: On an algebraic generalization of the
  quantum mechanical formalism. Ann. of Math. 35 (1934), 29--64, p. 64.
* Bresar, M., Zelmanov, E.: Jordan homomorphisms: a survey. Serdica Math. J. 51
  (2025), 203--230, Example 2.1.
-/

namespace RefJordanProduct

open Ref

/-- **Jordan–von Neumann–Wigner 1934, p. 64**: from a (not necessarily
associative) product `mul` on an additive group, the *quasi-multiplication*
`x y ↦ mul x y + mul y x`. -/
def quasiMul {A : Type*} [Add A] (mul : A → A → A) (x y : A) : A :=
  mul x y + mul y x

/-- Quasi-multiplication is commutative, whatever the product is. -/
theorem quasiMul_comm {A : Type*} [AddCommMagma A] (mul : A → A → A) (x y : A) :
    quasiMul mul x y = quasiMul mul y x := by
  simp only [quasiMul]
  exact add_comm _ _

/-- For the product of a ring, quasi-multiplication is the paper's Jordan
product `x ∘ y = xy + yx`, the sum without the half (Herstein 1957, p. 1104). -/
theorem quasiMul_eq_jordan {A : Type*} [Ring A] (x y : A) :
    quasiMul (fun a b => a * b) x y = jordan x y := rfl

/-- **The Jordan identity** for the quasi-multiplication of an associative
algebra: `(x ∘ y) ∘ (x ∘ x) = x ∘ (y ∘ (x ∘ x))`. This is what makes
quasi-multiplication a Jordan product in the sense of Jordan–von Neumann–Wigner
1934. -/
theorem jordan_identity {A : Type*} [Ring A] (x y : A) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  simp only [jordan]
  noncomm_ring

/-- **The factor 2 of the survey** (Brešar–Zelmanov 2025, Example 2.1): over a
`ℚ`-algebra the Jordan product `½(xy + yx)` is half of the paper's `x ∘ y`, so
`2 • (½(xy + yx)) = x ∘ y`. The two products therefore have the same `K`-linear
derivations, and the paper's choice of the sum without the half is the one that
survives in characteristic 2. -/
theorem jordan_eq_two_smul_half {A : Type*} [Ring A] [Algebra ℚ A] (x y : A) :
    jordan x y = (2 : ℚ) • ((2 : ℚ)⁻¹ • (x * y + y * x)) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  simp only [jordan, smul_smul, mul_inv_cancel₀ h2, one_smul]

/-- A derivation of an associative algebra is a derivation of its
quasi-multiplication in the `f`-derivation sense: the Jordan rule is the Leibniz
rule for `∘` (Benkovič 2015, §1; the paper's `Der ⊆ JDer`, Bresar 1988,
p. 1003). -/
theorem der_jordan {A : Type*} [Ring A] (D : A →+ A) (h : Der D) (x y : A) :
    D (jordan x y) = jordan (D x) y + jordan x (D y) :=
  der_jder h x y

end RefJordanProduct
