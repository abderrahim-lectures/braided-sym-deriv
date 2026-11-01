import Mathlib

/-!
# Shared notions for the background modules

This file collects the notions that several of the per-source modules of
`Background/` use. Each module cites the
bibliography entry of `paper/braided-sym-deriv.tex` it formalizes; this file
holds only what is common to at least two of them, in the conventions of the
paper:

* products and commutators are those of an associative ring `A`, and maps are
  additive (`A →+ A`) because the paper states "we say so when a result cited
  below holds more generally for additive maps on rings";
* the Jordan product is taken **without the half**, `x ∘ y = xy + yx`, which is
  Herstein's convention (Herstein 1957, p. 1104) and the paper's;
* `Der` is the Leibniz rule, `JDer` the Jordan rule, `LieDer` the commutator
  rule.

Nothing here is a deep theorem: every declaration is either a definition or an
identity that holds in an arbitrary ring.

## Main definitions

* `Background.Der`, `Background.JDer`, `Background.LieDer`, `Background.hersteinJordan`: the four classes of
  maps of the introduction of the paper.
* `Background.jordan`, `Background.commutator`: `x ∘ y = xy + yx` and `[x, y] = xy - yx`.
* `Background.leibnizDefect`: `E_D(x, y) = D(xy) - D(x)y - xD(y)`, Definition 3.1 of the
  paper (the name is the paper's, the map is Cusack 1975, §2).
* `Background.delta1`, `Background.delta2`: the Hochschild coboundary on `1`- and `2`-cochains
  (Hochschild 1945, §2, Definition 2.1; Weibel 1994, §9.1).
* `Background.innerDer`: the inner derivation `ad_g(x) = [g, x]`, called a principal
  derivation by Weibel 1994, §9.2.
* `Background.PrimeRing`, `Background.SemiprimeRing`, `Background.TwoTorsionFree`: the three ring
  conditions of the introduction, as defined by Bresar 1988, p. 1003.
* `Background.Comm`: `D α = α D`, the condition defining `BSDer_σ(A)^α` in
  Definition 2.2 of the paper.

## References

* Bresar, M.: Jordan derivations on semiprime rings. Proc. Amer. Math. Soc. 104
  (1988), 1003--1006.
* Herstein, I. N.: Jordan derivations of prime rings. Proc. Amer. Math. Soc. 8
  (1957), 1104--1110.
* Hochschild, G.: On the cohomology groups of an associative algebra. Ann. of
  Math. 46 (1945), 58--67.
* Weibel, C. A.: An Introduction to Homological Algebra. Cambridge Stud. Adv.
  Math. 38, Cambridge University Press, 1994.
-/

namespace Background

/-! ## The four classes of maps -/

variable {A : Type*} [Ring A]

/-- The Jordan product without the half, `x ∘ y = xy + yx`. The paper follows
Herstein 1957, p. 1104, and does not divide by `2`, so that characteristic `2`
is allowed; `½(xy + yx)` is the Jordan product of Bresar--Zelmanov 2025,
Example 2.1. -/
def jordan (x y : A) : A := x * y + y * x

/-- The commutator, `[x, y] = xy - yx`. -/
def commutator (x y : A) : A := x * y - y * x

/-- A derivation: `D(xy) = D(x)y + xD(y)`. -/
def Der (D : A →+ A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- A Jordan derivation in the `∘` form: `D(x ∘ y) = D(x) ∘ y + x ∘ D(y)`. This
is the form the paper uses throughout (Herstein 1957 states the equivalent
square form; `Background.hersteinJordan` below). -/
def JDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (jordan x y) = jordan (D x) y + jordan x (D y)

/-- A Jordan derivation in Herstein's square form, `D(x²) = D(x)x + xD(x)`
(Herstein 1957, p. 1104). -/
def hersteinJordan (D : A →+ A) : Prop := ∀ x : A, D (x * x) = D x * x + x * D x

/-- A Lie derivation: `D([x, y]) = [D(x), y] + [x, D(y)]`
(Martindale 1964, p. 183). -/
def LieDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (commutator x y) = commutator (D x) y + commutator x (D y)

/-- `D` commutes with `α`: the condition `Dα = αD` that cuts
`BSDer_σ(A)^α` out of `BSDer_σ(A)` in Definition 2.2 of the paper. -/
def Comm (D : A →+ A) (α : A → A) : Prop := ∀ x : A, D (α x) = α (D x)

/-! ## Elementary inclusions

Every derivation is a Jordan derivation (Bresar 1988, p. 1003) and a Lie
derivation (the Leibniz rule for the commutator). -/

theorem der_jder {D : A →+ A} (h : Der D) : JDer D := by
  intro x y
  simp only [jordan, map_add, h x y, h y x]
  abel

theorem der_lie {D : A →+ A} (h : Der D) : LieDer D := by
  intro x y
  simp only [commutator, map_sub, h x y, h y x]
  abel

/-- A derivation is a Jordan derivation in Herstein's square form. -/
theorem der_hersteinJordan {D : A →+ A} (h : Der D) : hersteinJordan D := by
  intro x
  rw [h x x, add_comm]

/-! ## The Leibniz defect and the Hochschild coboundary

The defect `E_D(x,y) = D(xy) - D(x)y - xD(y)` is Definition 3.1 of the paper;
Cusack 1975, §2 writes the same map and studies Jordan derivations through it.
`Background.delta1` is the Hochschild coboundary of Hochschild 1945, §2,
Definition 2.1, and `E_D = -δD`, so the derivations are the `1`-cocycles. -/

/-- The Leibniz defect of `D`, Definition 3.1 of the paper (Cusack 1975, §2). -/
def leibnizDefect (D : A →+ A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- The Hochschild coboundary on a `1`-cochain, `(δD)(x,y) = xD(y) - D(xy) + D(x)y`
(Hochschild 1945, §2, Definition 2.1). -/
def delta1 (D : A →+ A) (x y : A) : A := x * D y - D (x * y) + D x * y

/-- The Hochschild coboundary on a `2`-cochain,
`(δf)(x,y,z) = xf(y,z) - f(xy,z) + f(x,yz) - f(x,y)z` (Weibel 1994, §9.1). -/
def delta2 (f : A → A → A) (x y z : A) : A :=
  x * f y z - f (x * y) z + f x (y * z) - f x y * z

/-- The defect is minus the coboundary, `E_D = -δD` (paper, §3). -/
theorem leibnizDefect_eq_neg_delta1 (D : A →+ A) (x y : A) :
    leibnizDefect D x y = -delta1 D x y := by
  simp only [leibnizDefect, delta1]
  noncomm_ring

/-- The `1`-cocycles are exactly the derivations (Hochschild 1945, §2;
paper, §3). -/
theorem delta1_eq_zero_iff_der (D : A →+ A) : (∀ x y, delta1 D x y = 0) ↔ Der D := by
  have key : ∀ x y : A, D (x * y) - (D x * y + x * D y) = -delta1 D x y := by
    intro x y
    simp only [delta1]
    noncomm_ring
  constructor
  · intro h x y
    have h' := key x y
    rw [h x y, neg_zero] at h'
    exact sub_eq_zero.mp h'
  · intro h x y
    have h' := key x y
    rw [h x y, sub_self, zero_eq_neg] at h'
    exact h'

/-- `δ ∘ δ = 0` in degree one: the coboundary of a coboundary vanishes
(Weibel 1994, §9.1). -/
theorem delta2_delta1 (D : A →+ A) (x y z : A) : delta2 (delta1 D) x y z = 0 := by
  simp only [delta2, delta1]
  noncomm_ring

/-- The defect of any map is a `2`-cocycle: the paper's identity (3.2),
`aE(b,c) - E(ab,c) + E(a,bc) - E(a,b)c = 0` (Weibel 1994, §9.1). -/
theorem leibnizDefect_cocycle (D : A →+ A) (a b c : A) :
    a * leibnizDefect D b c - leibnizDefect D (a * b) c
      + leibnizDefect D a (b * c) - leibnizDefect D a b * c = 0 := by
  have key : a * leibnizDefect D b c - leibnizDefect D (a * b) c
      + leibnizDefect D a (b * c) - leibnizDefect D a b * c
      = -(a * delta1 D b c - delta1 D (a * b) c
          + delta1 D a (b * c) - delta1 D a b * c) := by
    simp only [leibnizDefect_eq_neg_delta1]
    noncomm_ring
  have h : a * delta1 D b c - delta1 D (a * b) c
      + delta1 D a (b * c) - delta1 D a b * c = 0 := by
    simpa only [delta2] using delta2_delta1 D a b c
  rw [key, h, neg_zero]

/-- A map is a Jordan derivation exactly when its defect is symmetric
(paper, §3: `E_D(x,y) + E_D(y,x) = 0`). -/
theorem jder_iff_defect_symm (D : A →+ A) :
    JDer D ↔ ∀ x y, leibnizDefect D x y + leibnizDefect D y x = 0 := by
  have key : ∀ x y : A, leibnizDefect D x y + leibnizDefect D y x
      = D (x * y + y * x) - (D x * y + x * D y + D y * x + y * D x) := by
    intro x y
    simp only [leibnizDefect, map_add]
    noncomm_ring
  constructor
  · intro h x y
    have hj : D (x * y + y * x) = (D x * y + y * D x) + (x * D y + D y * x) := by
      simpa only [JDer, jordan] using h x y
    rw [key x y, hj]
    noncomm_ring
  · intro h x y
    have h' : D (x * y + y * x) - (D x * y + x * D y + D y * x + y * D x) = 0 := by
      rw [← key x y, h x y]
    simp only [jordan]
    rw [sub_eq_zero.mp h']
    abel

/-! ## Inner derivations -/

/-- The inner derivation `ad_g(x) = [g, x] = gx - xg`; Weibel 1994, §9.2 calls
it a principal derivation. -/
def innerDer (g : A) : A →+ A where
  toFun x := g * x - x * g
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]; abel

@[simp]
theorem innerDer_apply (g x : A) : innerDer g x = g * x - x * g := rfl

/-- Inner derivations are derivations. -/
theorem innerDer_der (g : A) : Der (innerDer g) := by
  intro x y
  simp only [innerDer_apply]
  noncomm_ring

/-- Inner derivations are Lie derivations. -/
theorem innerDer_lie (g : A) : LieDer (innerDer g) := der_lie (innerDer_der g)

/-- The commutator of a derivation with the inner derivation `ad_g` is the inner
derivation `ad_{D(g)}`: the inner derivations form a Lie ideal of the
derivations (Weibel 1994, §9.2 for the terminology). -/
theorem der_comp_innerDer (D : A →+ A) (h : Der D) (g : A) :
    (D.comp (innerDer g) : A →+ A) - (innerDer g).comp D = innerDer (D g) := by
  ext x
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, innerDer_apply, map_sub,
    h g x, h x g]
  noncomm_ring

/-! ## The three ring conditions -/

/-- `R` is prime if `aRb = 0` implies `a = 0` or `b = 0`
(Bresar 1988, p. 1003). -/
def PrimeRing (R : Type*) [Ring R] : Prop :=
  ∀ a b : R, (∀ r : R, a * r * b = 0) → a = 0 ∨ b = 0

/-- `R` is semiprime if `aRa = 0` implies `a = 0` (Bresar 1988, p. 1003). -/
def SemiprimeRing (R : Type*) [Ring R] : Prop :=
  ∀ a : R, (∀ r : R, a * r * a = 0) → a = 0

/-- `R` is `2`-torsion-free if `2a = 0` implies `a = 0` (Bresar 1988, p. 1003). -/
def TwoTorsionFree (R : Type*) [AddGroup R] : Prop := ∀ a : R, a + a = 0 → a = 0

/-- Every prime ring is semiprime (paper, §1). -/
theorem prime_imp_semiprime {R : Type*} [Ring R] (h : PrimeRing R) :
    SemiprimeRing R := by
  intro a ha
  rcases h a a (fun r => ha r) with h0 | h0
  · exact h0
  · exact h0

end Background
