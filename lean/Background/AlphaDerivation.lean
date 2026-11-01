import Mathlib

/-!
# `Background/AlphaDerivation.lean` — Hosseini and Mohammadzadeh Karizaki (2019)

*Reference.* A. Hosseini, M. Mohammadzadeh Karizaki, *Functional equations
characterizing σ-derivations*, Acta Sci. Math. (Szeged) **85** (2019), 431--440.

*What the paper takes from it.* `paper/braided-sym-deriv.tex` (v63) cites
`\citep[\S1]{HosseiniKarizaki2019}` at line 189 for one thing only: the
definition of an `α`-derivation, quoted there as

  "For an automorphism `α` of `A`, an *`α`-derivation* satisfies
   `D(xy) = D(x)α(y) + α(x)D(y)`",

and it writes `Der_α(A)` for the set of them.  The paper uses the notion in
Proposition 4.4 and Example 4.5, where it compares `Der_α(A)` with the
braided-symmetric derivations of `σ_α`.  It imports **no theorem** from this
entry, so this module formalizes the definition, the elementary facts about it,
and witnesses showing that the notion is genuinely different from the
neighbouring ones.  There is no hypothesis-`Prop` here because the paper takes
no deep theorem from this source.

*Contents.*
* `Der`, `Comm`, `LeibnizDefect`, `Symm`, `BSDerP` — prelude, shareable;
* `AlphaDer α D` — the definition of §1 and its closure under addition;
* `alphaDer_iff_der_conjD`, `alphaDer_iff_exists` — the structure of the notion:
  `D` is an `α`-derivation exactly when `D = α ∘ d` for an ordinary derivation
  `d` (for `α` an automorphism);
* `der_twistedProd_iff` — for `D` commuting with `α`, the derivations of the
  twisted product `x *ₐ y = x * α(y)` are exactly the derivations of `A`;
* `symm_alpha`, `bsderP_alpha_iff` — the paper's `σ_α`-Leibniz rule
  `TwistedAlpha` is the binary encoding of `BSDerP` for the product `·_{σ_α}`;
* `Witness` — on `A = ℚ[X]` with `α(p) = p(-X)`: an `α`-derivation that is
  neither a derivation, nor a derivation of `x *ₐ y = x * α(y)`, nor a
  `σ_α`-braided-symmetric derivation, and which does not commute with `α`.

*Note on a false reading.*  The task brief proposes that `AlphaDer α` coincides
with the derivations of the twisted product `x *ₐ y = x * α y` under
`Comm D α`.  That is false, and `Witness.D_not_derTwisted` below is a
machine-checked refutation (there without `Comm D α`, which also fails).  The
correct statement, `der_twistedProd_iff`, is that those derivations are the
ordinary derivations of `A` when `D` commutes with `α`, while the
`α`-derivations are the maps `α ∘ d` with `d` a derivation.

Everything is stated for additive maps on rings, which is stronger than the
paper's `K`-linear maps on `K`-algebras.  Nothing here is a placeholder and no
compiler axiom is used.
-/

namespace Background.AlphaDerivation

variable {A : Type*} [Ring A]

/-! ## Prelude (may be lifted) -/

/-- An ordinary derivation, in the additive form `D(xy) = D(x)y + xD(y)`.
Paper §1 (the notion recalled there from Jacobson 1937 and Hochschild 1945); not
specific to the reference of this module. -/
def Der (D : A →+ A) : Prop := ∀ x y, D (x * y) = D x * y + x * D y

/-- `D` commutes with the map `α`.  Paper Definition 2.1 (`Dα = αD`); not
specific to the reference of this module. -/
def Comm (D : A →+ A) (α : A → A) : Prop := ∀ x, D (α x) = α (D x)

/-- The Leibniz defect `E_D(x,y) = D(xy) - D(x)y - xD(y)`.  Paper §3,
Definition 3.1; not specific to the reference of this module. -/
def LeibnizDefect (D : A →+ A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- The symmetrized product of a binary map `σ`: `x ·_σ y = xy + (σ x y)(σ y x)`.
Paper §1 (`μ_σ = μ + μ ∘ σ`, in the binary encoding); not specific to the
reference of this module. -/
def Symm (σ : A → A → A) (x y : A) : A := x * y + σ x y * σ y x

/-- A braided-symmetric derivation for a binary product `P`.  Paper §1,
identity (2.1); not specific to the reference of this module. -/
def BSDerP (P : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y, D (P x y) = P (D x) y + P x (D y)

/-- `D` is a derivation exactly when its Leibniz defect vanishes.  Paper §3
(`E_D = -δD`, hence `D` is a derivation iff `E_D = 0`); not specific to the
reference of this module. -/
theorem der_iff_leibnizDefect_zero (D : A →+ A) :
    Der D ↔ ∀ x y, LeibnizDefect D x y = 0 := by
  constructor
  · intro h x y
    simp only [LeibnizDefect, h x y]
    abel
  · intro h x y
    have h1 := h x y
    simp only [LeibnizDefect] at h1
    have h2 : D (x * y) = (D (x * y) - D x * y - x * D y) + (D x * y + x * D y) := by
      abel
    rw [h2, h1, zero_add]

/-! ## 1. `α`-derivations (Hosseini--Karizaki §1)

Throughout `α` is a unital ring endomorphism; the paper's `α` is a `K`-algebra
automorphism, which is the case `A ≃+* A` used in §2 below. -/

/-- An `α`-derivation: `D(xy) = D(x)α(y) + α(x)D(y)`.
Hosseini and Mohammadzadeh Karizaki, Acta Sci. Math. (Szeged) 85 (2019), §1,
quoted in paper §2 (line 189) and written `Der_α(A)` there. -/
def AlphaDer (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y, D (x * y) = D x * α y + α x * D y

/-- For `α = id` the `α`-derivations are the derivations.
Hosseini--Karizaki (2019) §1, as used in paper Example 4.5. -/
theorem alphaDer_id_iff (D : A →+ A) : AlphaDer (RingHom.id A) D ↔ Der D :=
  Iff.rfl

/-- The zero map is an `α`-derivation.  Hosseini--Karizaki (2019) §1: the
`α`-derivations form a subgroup of the additive group of `End(A)`. -/
theorem alphaDer_zero (α : A →+* A) : AlphaDer α 0 := by
  intro x y
  simp

/-- A sum of `α`-derivations is an `α`-derivation.  Hosseini--Karizaki (2019)
§1 (the defining equation is additive in `D`). -/
theorem alphaDer_add {α : A →+* A} {D E : A →+ A}
    (hD : AlphaDer α D) (hE : AlphaDer α E) : AlphaDer α (D + E) := by
  intro x y
  have h1 := hD x y
  have h2 := hE x y
  simp only [AddMonoidHom.add_apply]
  rw [h1, h2]
  noncomm_ring

/-- If `d` is a derivation, then `α ∘ d` is an `α`-derivation: the easy
direction of the structural description of `α`-derivations.
Hosseini--Karizaki (2019) §1. -/
theorem alphaDer_comp (α : A →+* A) {d D : A →+ A} (hd : Der d)
    (hD : ∀ x, D x = α (d x)) : AlphaDer α D := by
  intro x y
  rw [hD, hD x, hD y, hd x y, map_add, map_mul, map_mul]

/-- The Leibniz defect of an `α`-derivation is its `α`-deviation:
`E_D(x,y) = D(x)(α(y) - y) + (α(x) - x)D(y)`.
Hosseini--Karizaki (2019) §1, the defining identity rearranged; this is the form
in which paper Proposition 3.2 compares `α`-derivations with the `σ_α`-class. -/
theorem leibnizDefect_of_alphaDer {α : A →+* A} {D : A →+ A}
    (h : AlphaDer α D) (x y : A) :
    LeibnizDefect D x y = D x * (α y - y) + (α x - x) * D y := by
  have h1 := h x y
  simp only [LeibnizDefect]
  rw [h1]
  noncomm_ring

/-! ## 2. Structure: `α`-derivations are `α ∘ d` with `d` a derivation

This is the honest form of "the relation to derivations of a twisted product":
an `α`-derivation is the conjugate of a derivation by `α`. -/

/-- The additive map `α⁻¹ ∘ D`. -/
def conjD (α : A ≃+* A) (D : A →+ A) : A →+ A where
  toFun x := α.symm (D x)
  map_zero' := by simp
  map_add' := by
    intro x y
    simp

/-- `α (conjD α D x) = D x`. -/
theorem alpha_conjD (α : A ≃+* A) (D : A →+ A) (x : A) : α (conjD α D x) = D x := by
  simp [conjD]

/-- The `α`-derivations are the maps `D` with `α⁻¹ ∘ D` a derivation.
Hosseini--Karizaki (2019) §1: substituting `D = α d` in the defining identity and
cancelling `α` (an automorphism) gives the derivation rule for `d`.
Both directions are proved. -/
theorem alphaDer_iff_der_conjD (α : A ≃+* A) (D : A →+ A) :
    AlphaDer α D ↔ Der (conjD α D) := by
  constructor
  · intro h x y
    refine α.injective ?_
    calc α (conjD α D (x * y)) = D (x * y) := alpha_conjD α D _
      _ = D x * α y + α x * D y := h x y
      _ = α (conjD α D x) * α y + α x * α (conjD α D y) := by
            rw [alpha_conjD α D x, alpha_conjD α D y]
      _ = α (conjD α D x * y + x * conjD α D y) := by
            rw [map_add, map_mul, map_mul]
  · intro h x y
    calc D (x * y) = α (conjD α D (x * y)) := (alpha_conjD α D _).symm
      _ = α (conjD α D x * y + x * conjD α D y) := by rw [h x y]
      _ = D x * α y + α x * D y := by
            rw [map_add, map_mul, map_mul, alpha_conjD α D x, alpha_conjD α D y]

/-- The `α`-derivations are exactly the maps `α ∘ d` with `d` a derivation.
Hosseini--Karizaki (2019) §1, the same content as
`alphaDer_iff_der_conjD` in the form `D = α d`. -/
theorem alphaDer_iff_exists (α : A ≃+* A) (D : A →+ A) :
    AlphaDer α D ↔ ∃ d : A →+ A, Der d ∧ ∀ x, D x = α (d x) := by
  constructor
  · intro h
    exact ⟨conjD α D, (alphaDer_iff_der_conjD α D).1 h, fun x => (alpha_conjD α D x).symm⟩
  · rintro ⟨d, hd, hD⟩
    exact alphaDer_comp α hd hD

/-- `α⁻¹ ∘ D` commutes with `α` exactly when `D` does.
Hosseini--Karizaki (2019) §1 with the commutation hypothesis of paper
Definition 2.1 (`BSDer_σ(A)^α`). -/
theorem comm_conjD_iff (α : A ≃+* A) (D : A →+ A) :
    Comm (conjD α D) α ↔ Comm D α := by
  constructor
  · intro h x
    calc D (α x) = α (conjD α D (α x)) := (alpha_conjD α D (α x)).symm
      _ = α (α (conjD α D x)) := by rw [h x]
      _ = α (D x) := by rw [alpha_conjD α D x]
  · intro h x
    refine α.injective ?_
    rw [alpha_conjD α D (α x), h x, alpha_conjD α D x]

/-! ## 3. The twisted product `x *ₐ y = x * α(y)`

This is the product with respect to which `α`-derivations are usually
introduced.  The correct relation is the one proved here: its derivations are
the ordinary derivations (for `D` commuting with `α`), not the
`α`-derivations. -/

/-- The twisted product `x *ₐ y = x * α(y)` of Hosseini--Karizaki (2019) §1. -/
def twistedProd (α : A →+* A) (x y : A) : A := x * α y

/-- Derivations of the twisted product `x *ₐ y = x * α(y)`.
Hosseini--Karizaki (2019) §1. -/
def DerTwisted (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y, D (twistedProd α x y) = twistedProd α (D x) y + twistedProd α x (D y)

/-- For `D` commuting with an automorphism `α`, the derivations of the twisted
product `x *ₐ y = x * α(y)` are exactly the derivations of `A`.
Hosseini--Karizaki (2019) §1; both directions are proved. -/
theorem der_twistedProd_iff (α : A ≃+* A) (D : A →+ A) (hDα : Comm D α) :
    DerTwisted α D ↔ Der D := by
  constructor
  · intro h x z
    have h1 := h x (α.symm z)
    have h2 : α (α.symm z) = z := by simp
    have h3 : α (D (α.symm z)) = D z := by
      rw [← hDα (α.symm z)]
      simp
    simpa [twistedProd, h2, h3] using h1
  · intro h x y
    have h1 := h x (α y)
    have h2 : D (α y) = α (D y) := hDα y
    simpa [twistedProd, h2] using h1

/-! ## 4. The paper's `σ_α`-Leibniz rule

Paper §3 (`eq:twisted-product`): for an involutive `α` the product is
`x ·_{σ_α} y = xy + α(yx)`, and Definition 2.1 for `σ_α` is the paper's
displayed twisted identity. -/

/-- The paper's `σ_α`-Leibniz identity
`D(xy + α(yx)) = D(x)y + α(yD(x)) + xD(y) + α(D(y)x)`
(`eq:twisted-product` and Proposition 3.2, paper §3). -/
def TwistedAlpha (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x))

/-- The symmetrized product for `σ = σ_α` is `xy + α(yx)`.
Paper §3 (`eq:twisted-product`). -/
theorem symm_alpha (α : A →+* A) (x y : A) :
    Symm (fun _ z => α z) x y = x * y + α (y * x) := by
  simp [Symm, map_mul]

/-- The paper's binary encoding: `BSDerP` for the product `·_{σ_α}` is exactly
the paper's `TwistedAlpha` predicate.  Paper §3, Proposition 3.2. -/
theorem bsderP_alpha_iff (α : A →+* A) (D : A →+ A) :
    BSDerP (Symm (fun _ z => α z)) D ↔ TwistedAlpha α D := by
  constructor <;> intro h x y <;> simpa [TwistedAlpha, Symm, map_mul] using h x y

/-! ## 5. Witness: `α`-derivations and derivations differ for `α ≠ id`

`A = ℚ[X]`, `α(p) = p(-X)` (Mathlib's `Polynomial.compRingHom (-X)`), and
`D = α ∘ d/dX`.  Then `D` is an `α`-derivation and not a derivation; all
failures are read at `X` and `X * X`, and each reduces to `X ≠ 0`. -/

namespace Background.Witness

noncomputable section

/-- The witness algebra `A = ℚ[X]`. -/
abbrev W : Type := Polynomial ℚ

/-- `α(p) = p(-X)`, the ring endomorphism `p(X) ↦ p(-X)` of `ℚ[X]`
(Mathlib: `Polynomial.compRingHom (-X)`). -/
def sgn : W →+* W := Polynomial.compRingHom (-Polynomial.X)

/-- `α(X) = -X`: the automorphism is not the identity. -/
theorem sgn_X : sgn Polynomial.X = -Polynomial.X := by
  show Polynomial.X.comp (-Polynomial.X) = -Polynomial.X
  rw [Polynomial.X_comp]

/-- The derivation `d/dX` of `ℚ[X]`, as an additive map. -/
def dt : W →+ W where
  toFun p := Polynomial.derivative p
  map_zero' := Polynomial.derivative_zero
  map_add' _ _ := Polynomial.derivative_add

/-- `d/dX` is a derivation. -/
theorem dt_der : Der dt := fun _ _ => Polynomial.derivative_mul

/-- `D = α ∘ d/dX`, that is `D(p) = α(p')`: the witness `α`-derivation. -/
def D : W →+ W := sgn.toAddMonoidHom.comp dt

/-- `D(p) = α(p')`. -/
theorem D_apply (p : W) : D p = sgn (Polynomial.derivative p) := rfl

/-- `D` is an `α`-derivation, because it is `α ∘ d` with `d` a derivation
(Hosseini--Karizaki 2019 §1). -/
theorem D_alphaDer : AlphaDer sgn D := alphaDer_comp sgn dt_der (fun _ => rfl)

/-- `α(X²) = X²`, so `α` is not the identity on the even part. -/
theorem sgn_XX : sgn (Polynomial.X * Polynomial.X) = Polynomial.X * Polynomial.X := by
  rw [map_mul, sgn_X]
  ring

/-- `D(X) = 1`. -/
theorem D_X : D Polynomial.X = 1 := by
  show sgn (Polynomial.derivative Polynomial.X) = 1
  rw [Polynomial.derivative_X, map_one]

/-- `α(X) - X = -2X`. -/
theorem sgn_X_sub : sgn Polynomial.X - Polynomial.X = -(2 * Polynomial.X) := by
  rw [sgn_X]
  ring

/-- `D` is not a derivation: its defect at `(X, X)` is `-4X ≠ 0`.
Hosseini--Karizaki (2019) §1: an `α`-derivation need not be a derivation. -/
theorem D_not_der : ¬ Der D := by
  intro h
  have h1 := (der_iff_leibnizDefect_zero D).1 h Polynomial.X Polynomial.X
  rw [leibnizDefect_of_alphaDer D_alphaDer, D_X, sgn_X_sub] at h1
  have h2 : (4 : W) * Polynomial.X = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by simp)
  · exact Polynomial.X_ne_zero h3

/-- `D` is not a derivation of the twisted product `x *ₐ y = x * α(y)`, although
`D` is an `α`-derivation.  This is the machine-checked refutation of the reading
that `α`-derivations are the derivations of that product
(Hosseini--Karizaki 2019 §1, with `der_twistedProd_iff`). -/
theorem D_not_derTwisted : ¬ DerTwisted sgn D := by
  intro h
  have h1 := h Polynomial.X Polynomial.X
  simp only [twistedProd] at h1
  have hs : Polynomial.X * sgn Polynomial.X = -(Polynomial.X * Polynomial.X) := by
    rw [sgn_X]
    ring
  have hder : Polynomial.derivative (-(Polynomial.X * Polynomial.X) : W) =
      -(Polynomial.X + Polynomial.X) := by
    rw [Polynomial.derivative_neg (Polynomial.X * Polynomial.X : W),
      Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, one_mul]
  have hA : D (Polynomial.X * sgn Polynomial.X) = 2 * Polynomial.X := by
    rw [hs]
    show sgn (Polynomial.derivative (-(Polynomial.X * Polynomial.X) : W)) = 2 * Polynomial.X
    rw [hder, map_neg, map_add, sgn_X]
    ring
  have hB : D Polynomial.X * sgn Polynomial.X + Polynomial.X * sgn (D Polynomial.X) = 0 := by
    rw [D_X, sgn_X, map_one]
    ring
  rw [hA, hB] at h1
  have h2 : (2 : W) * Polynomial.X = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by simp)
  · exact Polynomial.X_ne_zero h3

/-- `D` is not a braided-symmetric derivation for `σ_α`: at `(X, X)` the two
sides of the twisted identity are `-4X` and `0`.
Hosseini--Karizaki (2019) §1 versus paper Proposition 3.2 and Proposition 4.4
(the two notions do not contain each other). -/
theorem D_not_twistedAlpha : ¬ TwistedAlpha sgn D := by
  intro h
  have h1 := h Polynomial.X Polynomial.X
  have hder : Polynomial.derivative (Polynomial.X * Polynomial.X : W) =
      Polynomial.X + Polynomial.X := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, one_mul]
  have hA : D (Polynomial.X * Polynomial.X + sgn (Polynomial.X * Polynomial.X)) =
      -(4 * Polynomial.X) := by
    rw [sgn_XX]
    show sgn (Polynomial.derivative (Polynomial.X * Polynomial.X +
      Polynomial.X * Polynomial.X : W)) = -(4 * Polynomial.X)
    rw [Polynomial.derivative_add, hder, map_add, map_add, sgn_X]
    ring
  have hB : D Polynomial.X * Polynomial.X + sgn (Polynomial.X * D Polynomial.X) +
      (Polynomial.X * D Polynomial.X + sgn (D Polynomial.X * Polynomial.X)) = 0 := by
    rw [D_X, mul_one, one_mul, sgn_X]
    ring
  rw [hA, hB] at h1
  have h2 : (4 : W) * Polynomial.X = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by simp)
  · exact Polynomial.X_ne_zero h3

/-- `D` does not commute with `α`: `D(α(X)) = -1` while `α(D(X)) = 1`.
Hosseini--Karizaki (2019) §1 with paper Definition 2.1: the commutation
hypothesis `Dα = αD` is a genuine restriction. -/
theorem D_not_comm : ¬ Comm D sgn := by
  intro h
  have h1 := h Polynomial.X
  have hA : D (sgn Polynomial.X) = -1 := by
    rw [sgn_X]
    show sgn (Polynomial.derivative (-Polynomial.X)) = -1
    rw [Polynomial.derivative_neg (Polynomial.X : W), Polynomial.derivative_X, map_neg, map_one]
  have hB : sgn (D Polynomial.X) = 1 := by
    rw [D_X, map_one]
  rw [hA, hB] at h1
  have h2 : (2 : W) = 0 := by
    linear_combination -h1
  exact absurd h2 (by simp)

end

end Background.Witness

end Background.AlphaDerivation
