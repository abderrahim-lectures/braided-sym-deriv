import Mathlib

/-!
# The Jordan product: quasi-multiplication (Jordan--von Neumann--Wigner 1934) and
# the Jordan product `½(xy + yx)` (Brešar--Zelmanov 2025)

`paper/braided-sym-deriv.tex` takes two things from its Jordan references: the
*quasi-multiplication* of Jordan, von Neumann and Wigner 1934, p. 64, and the
*Jordan product* `x ∘ y = ½(xy + yx)` together with the Jordan identity of
Brešar and Zelmanov 2025, Example 2.1 and §2, p. 204--205. Both are formalized
here. The paper takes no deep theorem from either entry, so this file has no
hypothesis-`Prop`: the Jordan identity is proved (`jordan_identity`) and the hard
part of the comparison of the two products is the factor `2`, which is proved
too (`jordan_eq_two_smul_halfJordan`, `halfJordanDer_iff_jder`).

## Conventions

The paper (line 102--106) follows Herstein 1957, p. 1104, and writes
`x ∘ y = xy + yx`, without the half, so that characteristic `2` is allowed; both
references write the half. Hence `jordan` below is the paper's product, and

* `jordan_eq_two_smul_halfJordan` shows that it is twice the Jordan product of
  Brešar--Zelmanov 2025, Example 2.1, p. 205;
* `halfJordanDer_iff_jder` shows that over a `ℚ`-algebra -- that is, when `2` is
  invertible and the maps are `ℚ`-linear -- the two products have the same
  derivations.

Maps are additive, `D : A →+ A`, as everywhere in the paper, except in the
section on the halved product, where the factor `2` forces `D : A →ₗ[ℚ] A`.

## Contents

* `jordan`, `JDer`, `JDerLin` (prelude): the paper's product and the Jordan
  derivation rule, for additive and for `ℚ`-linear maps;
* `qmul`: the quasi-multiplication of an arbitrary product, its commutativity,
  its coincidence with `jordan` for an associative product, and the Jordan
  identity `jordan_identity`;
* `halfJordan`, `HalfJordanDer`: the halved product and its derivations;
* `symm`, `BSDer`: the paper's symmetrized product `x ·_σ y = xy + σ(x,y)σ(y,x)`
  and Definition 2.1 of the paper; for the swap braiding `symm` is `qmul` and
  `BSDer` is `JDer`;
* `exProd`, `exMul`: the witness of Example 2.3 of the paper, whose product is
  the quasi-multiplication of `exMul` and is neither associative nor unital.

## References

* Jordan, P., von Neumann, J., Wigner, E.: On an algebraic generalization of the
  quantum mechanical formalism. Ann. of Math. **35** (1934), 29--64, p. 64.
* Brešar, M., Zelmanov, E.: Jordan homomorphisms: a survey. Serdica Math. J.
  **51** (2025), 203--230, Example 2.1 and §2, p. 204--205.
-/

namespace Background.JordanProduct

/-! ## Prelude (may be lifted) -/

section Prelude

variable {A : Type*} [Ring A]

/-- The paper's Jordan product without the half, `x ∘ y = xy + yx` (paper, §2,
line 102--106, after Herstein 1957, p. 1104). It is twice the Jordan product
`½(xy + yx)` of Brešar--Zelmanov 2025, Example 2.1, p. 205, as
`jordan_eq_two_smul_halfJordan` records. -/
def jordan (x y : A) : A := x * y + y * x

/-- The Jordan product is commutative, `x ∘ y = y ∘ x`: this is the first of the
two Jordan-algebra identities of Brešar--Zelmanov 2025, §2, p. 204 (`xy = yx`),
for the product of the paper. -/
theorem jordan_comm (x y : A) : jordan x y = jordan y x := add_comm (x * y) (y * x)

/-- A Jordan derivation: the Leibniz rule `D(x ∘ y) = D(x) ∘ y + x ∘ D(y)` for the
paper's product `∘ = jordan`. This is the form that paper, §2 uses throughout; it
is the linearisation of the Jordan derivation `D(x²) = D(x)x + xD(x)` of Herstein
1957, p. 1104, the two agreeing when `2` is invertible (paper, §2). -/
def JDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (jordan x y) = jordan (D x) y + jordan x (D y)

variable [Algebra ℚ A]

/-- The Jordan derivation rule for a `ℚ`-linear map; it is the rule `JDer` for the
underlying additive map (`jderLin_iff_jder`). The halved Jordan product needs
`2` invertible, which is why the linear maps are `ℚ`-linear there. -/
def JDerLin (D : A →ₗ[ℚ] A) : Prop :=
  ∀ x y : A, D (jordan x y) = jordan (D x) y + jordan x (D y)

/-- The two forms of the Jordan derivation rule agree: the underlying additive map
of a `ℚ`-linear map satisfies `JDer` exactly when the map satisfies `JDerLin`. -/
theorem jderLin_iff_jder (D : A →ₗ[ℚ] A) : JDerLin D ↔ JDer D.toAddMonoidHom :=
  Iff.rfl

/-- Cancelling the factor `2⁻¹` in a `ℚ`-module: the step "when `2` is invertible
we divide by `2`" that the paper performs once and for all by using the product
`xy + yx` without the half (paper, §2 and Remark 2.4). -/
theorem eq_of_inv_two_smul_eq {M : Type*} [AddCommMonoid M] [Module ℚ M] {z w : M}
    (h : (2 : ℚ)⁻¹ • z = (2 : ℚ)⁻¹ • w) : z = w := by
  have h' := congrArg (fun u : M => (2 : ℚ) • u) h
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_smul] using h'

end Prelude

/-! ## Quasi-multiplication (Jordan--von Neumann--Wigner 1934, p. 64) -/

section QuasiMultiplication

/-- The quasi-multiplication of Jordan--von Neumann--Wigner 1934, p. 64: the
product `x y ↦ mul x y + mul y x`, formed from a product `mul` and from the same
product with the two arguments exchanged. JVNW form `ab = (a × b + b × a)/2` from
the product `a × b` of an associative system; the paper (line 103) and this
definition drop the half, and `jordan_eq_two_smul_halfJordan` records the factor.
No hypothesis is put on `mul`: a product on an additive monoid is symmetrized to
a commutative product. -/
def qmul {M : Type*} [Add M] (mul : M → M → M) (x y : M) : M := mul x y + mul y x

/-- The quasi-multiplication is commutative, `qmul mul x y = qmul mul y x`:
Jordan--von Neumann--Wigner 1934, p. 64, where `ab` is built from `a × b` and from
`b × a` and hence does not see the order. -/
theorem qmul_comm {M : Type*} [AddCommSemigroup M] (mul : M → M → M) (x y : M) :
    qmul mul x y = qmul mul y x := add_comm (mul x y) (mul y x)

/-- The quasi-multiplication of an associative product is the paper's Jordan
product: Jordan--von Neumann--Wigner 1934, p. 64, with the half dropped as in the
paper, line 103 (`x ∘ y = xy + yx`); Brešar--Zelmanov 2025, Example 2.1, p. 205. -/
theorem qmul_mul_eq_jordan {A : Type*} [Ring A] (x y : A) :
    qmul (fun u v : A => u * v) x y = jordan x y := rfl

/-- The quasi-multiplication of a product that is additive in each argument is
additive in its first argument, so that it is again a product on the same
additive group: Jordan--von Neumann--Wigner 1934, p. 64, who symmetrize the
product `a × b` of an associative system. -/
theorem qmul_add_left {M : Type*} [AddCommSemigroup M] (mul : M → M → M)
    (h₁ : ∀ x y z : M, mul (x + y) z = mul x z + mul y z)
    (h₂ : ∀ x y z : M, mul x (y + z) = mul x y + mul x z) (x y z : M) :
    qmul mul (x + y) z = qmul mul x z + qmul mul y z := by
  simp only [qmul, h₁ x y z, h₂ z x y]
  ac_rfl

/-- The quasi-multiplication of a product that is additive in each argument is
additive in its second argument (Jordan--von Neumann--Wigner 1934, p. 64). -/
theorem qmul_add_right {M : Type*} [AddCommSemigroup M] (mul : M → M → M)
    (h₁ : ∀ x y z : M, mul (x + y) z = mul x z + mul y z)
    (h₂ : ∀ x y z : M, mul x (y + z) = mul x y + mul x z) (x y z : M) :
    qmul mul x (y + z) = qmul mul x y + qmul mul x z := by
  simp only [qmul, h₂ x y z, h₁ y z x]
  ac_rfl

/-- The Jordan identity for the quasi-multiplication of an associative product,
`(x ∘ y) ∘ (x ∘ x) = x ∘ (y ∘ (x ∘ x))`: this is the paper's form (§2) of the
Jordan-algebra identity `(x²y)x = x²(yx)` of Brešar--Zelmanov 2025, §2, p. 204
(with `x² = x ∘ x` for the halved product of their Example 2.1, the two forms
agreeing by `jordan_eq_two_smul_halfJordan`). It is what makes an associative
algebra a Jordan algebra for the product `∘`, and it is proved here from the
associativity of the ring product. -/
theorem jordan_identity {A : Type*} [Ring A] (x y : A) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  simp only [jordan]
  noncomm_ring

end QuasiMultiplication

/-! ## The halved Jordan product and the factor `2` (Brešar--Zelmanov 2025,
Example 2.1, p. 205) -/

section HalfJordan

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The Jordan product of Brešar--Zelmanov 2025, Example 2.1, p. 205,
`x ∘ y = (xy + yx)/2`, by which every associative algebra becomes a Jordan
algebra `A⁺`. It is stated over a `ℚ`-algebra, since `2` has to be invertible. -/
def halfJordan (x y : A) : A := (2 : ℚ)⁻¹ • (x * y + y * x)

/-- The halved Jordan product is commutative: Brešar--Zelmanov 2025, §2, p. 204
(`xy = yx`), for the product of their Example 2.1. -/
theorem halfJordan_comm (x y : A) : halfJordan x y = halfJordan y x := by
  simp only [halfJordan, add_comm (x * y) (y * x)]

/-- The paper's product is twice the Jordan product of Brešar--Zelmanov 2025,
Example 2.1, p. 205: paper, §2, line 102, "the sum `xy + yx` is twice the Jordan
product `½(xy + yx)` of an associative algebra". -/
theorem jordan_eq_two_smul_halfJordan (x y : A) :
    jordan x y = (2 : ℚ) • halfJordan x y := by
  simp only [jordan, halfJordan, smul_smul]
  rw [mul_inv_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_smul]

/-- A derivation of the halved Jordan product, `D(x ∘ y) = D(x) ∘ y + x ∘ D(y)` for
`x ∘ y = ½(xy + yx)` of Brešar--Zelmanov 2025, Example 2.1, p. 205. It is stated
for a `ℚ`-linear map, because the halved product needs `2` invertible. -/
def HalfJordanDer (D : A →ₗ[ℚ] A) : Prop :=
  ∀ x y : A, D (halfJordan x y) = halfJordan (D x) y + halfJordan x (D y)

/-- The halved product has the same derivations as the paper's product: over a
`ℚ`-algebra, that is when `2` is invertible, `D` satisfies the Leibniz rule for
`½(xy + yx)` (Brešar--Zelmanov 2025, Example 2.1, p. 205) if and only if it
satisfies the Jordan rule for `xy + yx` (paper, §2, line 102). -/
theorem halfJordanDer_iff_jderLin (D : A →ₗ[ℚ] A) : HalfJordanDer D ↔ JDerLin D := by
  constructor
  · intro h x y
    have h0 := h x y
    simp only [halfJordan, LinearMap.map_smul] at h0
    simp only [jordan]
    apply eq_of_inv_two_smul_eq
    rw [h0]
    simp only [smul_add]
  · intro h x y
    have h0 := h x y
    simp only [jordan] at h0
    simp only [halfJordan, LinearMap.map_smul]
    rw [h0]
    simp only [smul_add]

/-- The two products have the same derivations when `2` is invertible:
`D : A →ₗ[ℚ] A` is a derivation of `½(xy + yx)` (Brešar--Zelmanov 2025,
Example 2.1, p. 205) exactly when its underlying additive map is a Jordan
derivation for the paper's `xy + yx` (paper, §2). -/
theorem halfJordanDer_iff_jder (D : A →ₗ[ℚ] A) :
    HalfJordanDer D ↔ JDer D.toAddMonoidHom :=
  (halfJordanDer_iff_jderLin D).trans (jderLin_iff_jder D)

end HalfJordan

/-! ## The paper's symmetrized product and Definition 2.1 for the swap -/

section Symm

variable {A : Type*} [Ring A]

/-- The swap `τ(x ⊗ y) = y ⊗ x` in the binary encoding of paper, §2: the map
`σ(x,y) = y` returns the second factor of `σ(x ⊗ y)`, so that
`σ(x,y) · σ(y,x) = y · x`. This is the `standardBraiding` of
`lean/Research/BraidedSymDeriv/BraidedSymmetric.lean`, restated locally. -/
def swapBraiding (_x y : A) : A := y

/-- The paper's `σ`-symmetrized product `x ·_σ y = μ(x ⊗ y) + μ(σ(x ⊗ y))` (paper,
§2, line 118--121), written in the binary encoding of the braiding by the two
factors of `σ(x ⊗ y)`. This restates `symmetrizedProduct` of
`lean/Research/BraidedSymDeriv/BraidedSymmetric.lean` locally. -/
def symm (σ : A → A → A) (x y : A) : A := x * y + σ x y * σ y x

/-- A braided-symmetric derivation for `σ`: identity (eq:sigma-leibniz) of
Definition 2.1 of the paper, `D(x ·_σ y) = D(x) ·_σ y + x ·_σ D(y)`. -/
def BSDer (σ : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (symm σ x y) = symm σ (D x) y + symm σ x (D y)

/-- For the swap braiding the symmetrized product is the quasi-multiplication of
the associative product, hence the paper's Jordan product: paper, §2, line 124,
"For `σ = τ` this is the Jordan product `x ∘ y`". This is
`symmetrizedProduct_std` of `BraidedSymmetric.lean` restated locally; with
`qmul_mul_eq_jordan` it says that the paper's symmetrized product for the swap is
the quasi-multiplication of Jordan--von Neumann--Wigner 1934, p. 64. -/
theorem symm_swapBraiding (x y : A) :
    symm swapBraiding x y = qmul (fun u v : A => u * v) x y := rfl

/-- For the swap braiding the symmetrized product is the Jordan product
(Jordan--von Neumann--Wigner 1934, p. 64; paper, §2, line 124). -/
theorem symm_swapBraiding_eq_jordan (x y : A) : symm swapBraiding x y = jordan x y :=
  rfl

/-- For the swap, Definition 2.1 of the paper is the Jordan derivation rule:
`BSDer_τ(A) = JDer(A)` in every characteristic (paper, Remark 2.4). -/
theorem bsDer_swapBraiding_iff_jder (D : A →+ A) : BSDer swapBraiding D ↔ JDer D :=
  Iff.rfl

end Symm

/-! ## The quasi-multiplication need not be associative (paper, Example 2.3) -/

section Witness

/-- The swap `α(a,b) = (b,a)` of the paper's Example 2.3 (§2). -/
def exAlpha (z : ℚ × ℚ) : ℚ × ℚ := (z.2, z.1)

/-- `α` is an automorphism of `ℚ × ℚ`: paper, Example 2.3 (§2), "then `α` is an
automorphism with `α² = id`". -/
theorem exAlpha_mul (x y : ℚ × ℚ) : exAlpha (x * y) = exAlpha x * exAlpha y := by
  ext <;> simp only [exAlpha, Prod.fst_mul, Prod.snd_mul]

/-- `α² = id`: paper, Example 2.3 (§2). -/
theorem exAlpha_involutive (z : ℚ × ℚ) : exAlpha (exAlpha z) = z := by
  ext <;> simp only [exAlpha]

/-- The product `x ·_{σ_α} y = xy + α(xy)` of Example 2.3 of the paper (§2), on
`A = ℚ × ℚ` with `α` the swap: since `A` is commutative and
`σ_α(x ⊗ y) = α(y) ⊗ α(x)`, the paper gets `x ·_{σ_α} y = xy + α(xy)`, which for
`x = (x₁,x₂)` and `y = (y₁,y₂)` is `(x₁y₁ + x₂y₂)(1,1)`; that is this map. -/
def exProd (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 * y.1 + x.2 * y.2, x.1 * y.1 + x.2 * y.2)

/-- `exProd` is the product `xy + α(xy)` of Example 2.3 of the paper (§2). -/
theorem exProd_eq (x y : ℚ × ℚ) : exProd x y = x * y + exAlpha (x * y) := by
  ext <;> simp only [exProd, exAlpha, Prod.fst_mul, Prod.snd_mul, Prod.fst_add,
    Prod.snd_add]
  ring

/-- The product `½(x₁y₁ + x₂y₂)(1,1)` whose quasi-multiplication
(Jordan--von Neumann--Wigner 1934, p. 64) is the product of Example 2.3 of the
paper. -/
def exMul (x y : ℚ × ℚ) : ℚ × ℚ :=
  ((x.1 * y.1 + x.2 * y.2) / 2, (x.1 * y.1 + x.2 * y.2) / 2)

/-- The product of Example 2.3 of the paper is the quasi-multiplication of
`exMul`: Jordan--von Neumann--Wigner 1934, p. 64. -/
theorem qmul_exMul_eq_exProd (x y : ℚ × ℚ) : qmul exMul x y = exProd x y := by
  ext <;> simp only [qmul, exMul, exProd, Prod.fst_add, Prod.snd_add] <;> ring

/-- The product of Example 2.3 of the paper is not associative: this is the
paper's computation with `p = (1,0)` and `q = (0,1)`, where `(p · p) · q = (1,1)`
but `p · (p · q) = 0`. -/
theorem exProd_not_assoc :
    ¬ ∀ x y z : ℚ × ℚ, exProd (exProd x y) z = exProd x (exProd y z) := by
  intro h
  have h' := congrArg Prod.snd (h (1, 0) (1, 0) (0, 1))
  simp only [exProd] at h'
  norm_num at h'

/-- Hence the quasi-multiplication of a product on `ℚ × ℚ` need not be
associative: it is not a product on an associative algebra in general
(Jordan--von Neumann--Wigner 1934, p. 64; the failure is the one of Example 2.3 of
the paper). -/
theorem qmul_not_assoc :
    ¬ ∀ x y z : ℚ × ℚ,
      qmul exMul (qmul exMul x y) z = qmul exMul x (qmul exMul y z) := by
  intro h
  apply exProd_not_assoc
  intro x y z
  simp only [← qmul_exMul_eq_exProd]
  exact h x y z

/-- The product of Example 2.3 of the paper has no unit: as the paper puts it,
every product `u ·_{σ_α} y` lies in `ℚ(1,1)`, so `u ·_{σ_α} p ≠ p` for `p = (1,0)`
and every `u`. -/
theorem exProd_no_unit : ¬∃ e : ℚ × ℚ, ∀ y : ℚ × ℚ, exProd e y = y := by
  rintro ⟨e, he⟩
  have h1 := congrArg Prod.fst (he (1, 0))
  have h2 := congrArg Prod.snd (he (1, 0))
  simp only [exProd, mul_one, mul_zero, add_zero] at h1 h2
  linarith

end Witness

end Background.JordanProduct
