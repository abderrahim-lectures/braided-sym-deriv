/-
# Jordan derivations: Herstein 1957, Cusack 1975, Brešar 1988

This module formalizes, in the conventions of `paper/braided-sym-deriv.tex`, what
the paper takes from three bibliography entries.

* I. N. Herstein, *Jordan derivations of prime rings*, Proc. Amer. Math. Soc. 8
  (1957), 1104--1110.  p. 1104 for the definition of a Jordan derivation as the
  square identity, Theorem 3.1 for the deep theorem.
* J. M. Cusack, *Jordan derivations on rings*, Proc. Amer. Math. Soc. 53 (1975),
  321--324.  §2 for the defect `d(a, b) = D(ab) - aDb - (Da)b`, Corollary 5 for
  the deep theorem.
* M. Brešar, *Jordan derivations on semiprime rings*, Proc. Amer. Math. Soc. 104
  (1988), 1003--1006.  p. 1003 for the three ring conditions (prime, semiprime,
  2-torsion-free), for "every derivation is a Jordan derivation, and the converse
  is false in general", and Theorem 1 for the deep theorem.

The deep theorems of the three entries are *not* proved here: each is a
`def ... : Prop` hypothesis (`herstein1957Theorem31`, `cusack1975Corollary5`,
`bresar1988Theorem1`) together with conditional theorems that consume it.  What
is proved is everything elementary the paper uses: the linearisation of the
Jordan identity (paper, lines 180--191), the identification of Herstein's square
form with the paper's `∘` form when `A` is 2-torsion-free, the identity of
Cusack's defect with the paper's `E_D`, the criterion "Jordan derivation iff the
defect is symmetric", and the witnesses showing that the converse fails.

## Encoding choices

The paper says "we say so when a result cited below holds more generally for
additive maps on rings".  All three entries are ring-level results about additive
maps, so everything below is stated for an arbitrary `Ring A` and an additive
`D : A →+ A`.  The Jordan product is taken **without the half**,
`x ∘ y = x * y + y * x`, which is Herstein's convention (p. 1104) and the
paper's; `½(xy + yx)` of Brešar--Zelmanov 2025 is half of it.

Nothing here is a placeholder and no compiler axiom is used.
-/
import Mathlib

namespace RefJordanHerstein

universe u

/-! ## Prelude (may be lifted)

The notions of this section are not specific to the three entries above: they are
the paper's classes of maps (§1), the paper's Leibniz defect (Definition 3.1) and
the ring conditions of Brešar 1988, p. 1003, which the paper recalls in its §1.
-/

variable {A : Type*} [Ring A]

/-- The Jordan product without the half, `x ∘ y = x * y + y * x`.  Herstein 1957,
p. 1104 takes this sum; the paper follows him and does not divide by `2`, so that
characteristic `2` is allowed (paper, §1). -/
def jordan (x y : A) : A := x * y + y * x

/-- A derivation of a ring: `D (x * y) = D x * y + x * D y` (paper, §1). -/
def Der (D : A →+ A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- A Jordan derivation in the `∘` form,
`D (x ∘ y) = D x ∘ y + x ∘ D y`.  This is the form the paper uses throughout
(paper, §1); the equivalent square form is `hersteinJordan` below. -/
def JDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (jordan x y) = jordan (D x) y + jordan x (D y)

/-- Herstein's square form of a Jordan derivation (Herstein 1957, p. 1104): the
additive map `D` satisfies `D (x * x) = D x * x + x * D x` for all `x`.  Herstein
introduces a Jordan derivation on p. 1104 as a derivation of the Jordan ring, that
is by the `∘` identity `JDer`, and records in the same paragraph that for rings of
characteristic different from `2` it "can be defined by" this square identity;
`hersteinJordan_iff_jder_of_twoTorsionFree` below proves the equivalence. -/
def hersteinJordan (D : A →+ A) : Prop := ∀ x : A, D (x * x) = D x * x + x * D x

/-- The Leibniz defect of the paper's Definition 3.1,
`E_D(x, y) = D (x * y) - D x * y - x * D y`. -/
def leibnizDefect (D : A →+ A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- `R` is prime if `a * R * b = 0` implies `a = 0` or `b = 0`
(Brešar 1988, p. 1003; paper, §1). -/
def PrimeRing (R : Type*) [Ring R] : Prop :=
  ∀ a b : R, (∀ r : R, a * r * b = 0) → a = 0 ∨ b = 0

/-- `R` is semiprime if `a * R * a = 0` implies `a = 0`
(Brešar 1988, p. 1003; paper, §1). -/
def SemiprimeRing (R : Type*) [Ring R] : Prop :=
  ∀ a : R, (∀ r : R, a * r * a = 0) → a = 0

/-- `R` is 2-torsion-free if `a + a = 0` implies `a = 0`
(Brešar 1988, p. 1003; paper, §1). -/
def TwoTorsionFree (R : Type*) [AddGroup R] : Prop := ∀ a : R, a + a = 0 → a = 0

/-- Every derivation is a Jordan derivation in the `∘` form
(Brešar 1988, p. 1003; paper, §1). -/
theorem der_jder {D : A →+ A} (h : Der D) : JDer D := by
  intro x y
  simp only [jordan, map_add, h x y, h y x]
  abel

/-- Every derivation satisfies Herstein's square identity (Herstein 1957, p. 1104
for the form; Brešar 1988, p. 1003 for the implication). -/
theorem der_hersteinJordan {D : A →+ A} (h : Der D) : hersteinJordan D := by
  intro x
  rw [h x x]

/-- Every prime ring is semiprime (paper, §1, after Brešar 1988, p. 1003). -/
theorem prime_imp_semiprime {R : Type*} [Ring R] (h : PrimeRing R) : SemiprimeRing R := by
  intro a ha
  rcases h a a (fun r => ha r) with h0 | h0
  · exact h0
  · exact h0

/-! ## Herstein 1957: the two forms of a Jordan derivation

Herstein states a Jordan derivation by the square identity (p. 1104), the paper
by the `∘` identity.  The paper (lines 180--191) linearises: replacing `x` by
`x + y` in the square identity gives the `∘` identity in every characteristic,
and setting `y = x` in the `∘` identity gives the square identity multiplied by
`2`, so the two agree as soon as `2` can be cancelled.
-/

/-- **Linearisation of Herstein's identity** (paper, lines 180--186; the claim
that replacing `x` by `x + y` in `D (x * x) = D x * x + x * D x` gives
`D (x ∘ y) = D x ∘ y + x ∘ D y` in every characteristic).  Only additivity of
`D` is used. -/
theorem jder_of_hersteinJordan {D : A →+ A} (h : hersteinJordan D) : JDer D := by
  intro x y
  have hx := h x
  have hy := h y
  have hxy := h (x + y)
  rw [show (x + y) * (x + y) = x * x + (x * y + (y * x + y * y)) from by
    noncomm_ring] at hxy
  simp only [map_add] at hxy
  have key : D (x * y) + D (y * x) = D x * y + D y * x + x * D y + y * D x := by
    linear_combination (norm := noncomm_ring) hxy - hx - hy
  simp only [jordan, map_add]
  rw [key]
  abel

/-- Setting `y = x` in the `∘` form only gives the square identity **multiplied
by `2`**: `D (x * x) + D (x * x) = (D x * x + x * D x) + (D x * x + x * D x)`,
that is, `2 D (x²) = 2 (D(x) x + x D(x))` (paper, lines 186--188). -/
theorem two_mul_sq_of_jder {D : A →+ A} (h : JDer D) (x : A) :
    D (x * x) + D (x * x) = (D x * x + x * D x) + (D x * x + x * D x) := by
  have hxx := h x x
  simp only [jordan, map_add] at hxx
  rw [hxx]
  abel

/-- The `∘` form implies Herstein's square form on a 2-torsion-free ring: the
factor `2` of the previous identity can be cancelled (paper, lines 186--189;
Brešar 1988, p. 1003). -/
theorem hersteinJordan_of_jder (h2 : TwoTorsionFree A) {D : A →+ A} (h : JDer D) :
    hersteinJordan D := by
  intro x
  have hd := two_mul_sq_of_jder h x
  have hz : (D (x * x) - (D x * x + x * D x)) + (D (x * x) - (D x * x + x * D x)) = 0 := by
    have h1 : (D (x * x) - (D x * x + x * D x)) + (D (x * x) - (D x * x + x * D x))
        = (D (x * x) + D (x * x))
          - ((D x * x + x * D x) + (D x * x + x * D x)) := by abel
    rw [h1, hd]; abel
  exact sub_eq_zero.mp (h2 _ hz)

/-- On a 2-torsion-free ring Herstein's square form and the paper's `∘` form are
the same condition (paper, lines 186--189). -/
theorem hersteinJordan_iff_jder_of_twoTorsionFree (h2 : TwoTorsionFree A) (D : A →+ A) :
    hersteinJordan D ↔ JDer D :=
  ⟨jder_of_hersteinJordan, hersteinJordan_of_jder h2⟩

/-- A prime ring of characteristic different from `2` is 2-torsion-free: if
`a + a = 0`, then `2 * r * a = 0` for every `r`, so primeness gives `2 = 0` or
`a = 0`.  This is how Herstein's hypothesis "characteristic different from `2`"
(Herstein 1957, Theorem 3.1) becomes the 2-torsion-freeness of Cusack 1975,
Corollary 5 and Brešar 1988, Theorem 1. -/
theorem twoTorsionFree_of_primeRing {R : Type*} [Ring R] (h : PrimeRing R)
    (h2 : (2 : R) ≠ 0) : TwoTorsionFree R := by
  intro a ha
  have h2a : (2 : R) * a = 0 := by rw [two_mul]; exact ha
  have hzero : ∀ r : R, (2 : R) * r * a = 0 := by
    intro r
    calc (2 : R) * r * a = r * ((2 : R) * a) := by noncomm_ring
      _ = 0 := by rw [h2a, mul_zero]
  rcases h (2 : R) a hzero with h3 | h3
  · exact absurd h3 h2
  · exact h3

/-! ## Cusack 1975, §2: the defect

Cusack writes the defect `d(a, b) = D(ab) - aDb - (Da)b` and studies Jordan
derivations through it (paper, line 324).  It is the paper's `leibnizDefect`,
which is Definition 3.1 of the paper. -/

/-- Cusack's defect `d(a, b) = D (a * b) - a * D b - D a * b`
(Cusack 1975, §2; paper, line 324). -/
def cusackDefect (D : A →+ A) (a b : A) : A := D (a * b) - a * D b - D a * b

/-- Cusack's defect is the paper's Leibniz defect: the two differ only in the
order in which the two negative terms are written
(Cusack 1975, §2; paper, Definition 3.1 and line 324). -/
theorem cusackDefect_eq_leibnizDefect (D : A →+ A) (a b : A) :
    cusackDefect D a b = leibnizDefect D a b := by
  simp only [cusackDefect, leibnizDefect]
  abel

/-- A map is a Jordan derivation exactly when its defect is symmetric,
`E_D(x, y) + E_D(y, x) = 0`; this is the form in which Cusack 1975, §2 uses the
defect (see the paper's Definition 3.1 and its proof of Theorem 4.1, which
records the symmetric-defect version). -/
theorem jder_iff_defect_add_zero (D : A →+ A) :
    JDer D ↔ ∀ x y : A, leibnizDefect D x y + leibnizDefect D y x = 0 := by
  constructor
  · intro h x y
    have hxy := h x y
    simp only [jordan, map_add, leibnizDefect] at hxy ⊢
    linear_combination (norm := noncomm_ring) hxy
  · intro h x y
    have hxy := h x y
    simp only [jordan, map_add, leibnizDefect] at hxy ⊢
    linear_combination (norm := noncomm_ring) hxy

/-- A map satisfies Herstein's square identity exactly when its defect vanishes
on the diagonal: `E_D(x, x) = 0` for all `x`
(Herstein 1957, p. 1104; Cusack 1975, §2; paper, Definition 3.1). -/
theorem hersteinJordan_iff_defect_self_zero (D : A →+ A) :
    hersteinJordan D ↔ ∀ x : A, leibnizDefect D x x = 0 := by
  constructor
  · intro h x
    have hx := h x
    simp only [leibnizDefect]
    linear_combination (norm := noncomm_ring) hx
  · intro h x
    have hx := h x
    simp only [leibnizDefect] at hx
    linear_combination (norm := noncomm_ring) hx

/-! ## The three cited theorems, as hypotheses

The three deep theorems the paper uses are stated exactly, but not proved: each
is a `Prop`-valued `def` documented as the cited theorem, with conditional
theorems below that consume it so the statement is known to be usable.
-/

/-- **Not proved here: this is the cited theorem, taken as a hypothesis.**
Herstein 1957, Theorem 3.1, as the paper states it (paper, line 111): every
Jordan derivation of a prime ring of characteristic different from `2` is a
derivation.  The hypothesis `(2 : R) ≠ 0` is "characteristic different from 2";
Herstein writes the same hypothesis as `2x = 0` implies `x = 0`, and
`twoTorsionFree_of_primeRing` converts `(2 : R) ≠ 0` into that form, which is the
2-torsion-freeness used by the two later theorems.  The locator is the paper's
(paper, line 111); in the original, §3 is headed by Lemma 3.1 and continues to
Lemma 3.4 before the theorem of the section is stated, so the section's theorem
may carry a later number than 3.1.  The conclusion is stated in the paper's `∘` form; by
`hersteinJordan_iff_jder_of_twoTorsionFree` it is the same statement for
Herstein's own square form. -/
def herstein1957Theorem31 : Prop :=
  ∀ (R : Type u) [Ring R], PrimeRing R → (2 : R) ≠ 0 → ∀ D : R →+ R, JDer D → Der D

/-- **Not proved here: this is the cited theorem, taken as a hypothesis.**
Cusack 1975, Corollary 5 (paper, line 113): every Jordan derivation of a
2-torsion-free semiprime ring is a derivation.  Cusack's Jordan derivation is the
`∘` identity, taken on a ring "in which `2x = 0` implies `x = 0`", so this is his
statement verbatim ("If R is semiprime then D is a derivation"); it extends
Herstein 1957, Theorem 3.1 to semiprime rings. -/
def cusack1975Corollary5 : Prop :=
  ∀ (R : Type u) [Ring R], TwoTorsionFree R → SemiprimeRing R →
    ∀ D : R →+ R, JDer D → Der D

/-- **Not proved here: this is the cited theorem, taken as a hypothesis.**
Brešar 1988, Theorem 1 (paper, line 113 and Theorem 3.1 of the paper): every
Jordan derivation of a 2-torsion-free semiprime ring is a derivation, proved
independently of Cusack 1975.  Brešar calls an additive map a Jordan derivation
when `(a * a)' = a' * a + a * a'`, the square form `hersteinJordan`, and states
Theorem 1 for that form: "Let R be a 2-torsion free semiprime ring and let
' : R → R be a Jordan derivation. In this case, ' is a derivation."  On the
2-torsion-free ring the two forms agree, so this is the statement below; the
literal square-form version is `der_of_hersteinJordan_of_semiprime`.  It is
literally Cusack's Corollary 5 as well, which `bresar_iff_cusack` records. -/
def bresar1988Theorem1 : Prop :=
  ∀ (R : Type u) [Ring R], TwoTorsionFree R → SemiprimeRing R →
    ∀ D : R →+ R, JDer D → Der D

/-- Brešar 1988, Theorem 1 and Cusack 1975, Corollary 5 state the same theorem,
which is why the paper cites them together as two proofs of one result
(paper, line 113). -/
theorem bresar_iff_cusack :
    bresar1988Theorem1.{u} ↔ cusack1975Corollary5.{u} := Iff.rfl

/-- Herstein 1957, Theorem 3.1, consumed: a Jordan derivation of a prime ring of
characteristic different from `2` is a derivation. -/
theorem der_of_jder_of_prime (H : herstein1957Theorem31.{u}) {R : Type u} [Ring R]
    (hp : PrimeRing R) (h2 : (2 : R) ≠ 0) {D : R →+ R} (hD : JDer D) : Der D :=
  H R hp h2 D hD

/-- Herstein 1957, Theorem 3.1, consumed in Herstein's own square form: the
hypothesis `hersteinJordan` is read in the `∘` form by the linearisation. -/
theorem der_of_hersteinJordan_of_prime (H : herstein1957Theorem31.{u}) {R : Type u}
    [Ring R] (hp : PrimeRing R) (h2 : (2 : R) ≠ 0) {D : R →+ R}
    (hD : hersteinJordan D) : Der D :=
  H R hp h2 D (jder_of_hersteinJordan hD)

/-- Cusack 1975, Corollary 5, consumed: a Jordan derivation of a 2-torsion-free
semiprime ring is a derivation. -/
theorem der_of_jder_of_semiprime (H : cusack1975Corollary5.{u}) {R : Type u} [Ring R]
    (htf : TwoTorsionFree R) (hsp : SemiprimeRing R) {D : R →+ R} (hD : JDer D) :
    Der D :=
  H R htf hsp D hD

/-- Brešar 1988, Theorem 1, consumed in Herstein's square form; the two forms
agree on a 2-torsion-free ring by `hersteinJordan_iff_jder_of_twoTorsionFree`. -/
theorem der_of_hersteinJordan_of_semiprime (H : bresar1988Theorem1.{u}) {R : Type u}
    [Ring R] (htf : TwoTorsionFree R) (hsp : SemiprimeRing R) {D : R →+ R}
    (hD : hersteinJordan D) : Der D :=
  H R htf hsp D ((hersteinJordan_iff_jder_of_twoTorsionFree htf D).mp hD)

/-- Brešar 1988, Theorem 1 implies Herstein 1957, Theorem 3.1: a prime ring of
characteristic different from `2` is 2-torsion-free and semiprime.  This is the
sense in which the paper's two citations are a generalisation and its special
case (paper, lines 111--113). -/
theorem herstein_of_bresar (H : bresar1988Theorem1.{u}) :
    herstein1957Theorem31.{u} := by
  intro R _inst hp h2 D hD
  exact H R (twoTorsionFree_of_primeRing hp h2) (prime_imp_semiprime hp) D hD

/-- Cusack 1975, Corollary 5 implies Herstein 1957, Theorem 3.1, for the same
reason. -/
theorem herstein_of_cusack (H : cusack1975Corollary5.{u}) :
    herstein1957Theorem31.{u} :=
  herstein_of_bresar (bresar_iff_cusack.mpr H)

/-! ## The converse fails in general (Brešar 1988, p. 1003)

Brešar records on p. 1003 that every derivation is a Jordan derivation and that
the converse is false in general.  The witnesses below are on `ZMod 4`, a
commutative ring with `4 = 0`: the doubling map is an additive Jordan derivation
(even though the Jordan condition is not vacuous there) but not a derivation.
The same map is not a Jordan derivation in Herstein's square form, which is the
paper's point (lines 186--189) that the two forms differ without
2-torsion-freeness.  The last theorem of the section is the paper's remark
(line 186) that in a commutative ring in which every element is 2-torsion every
additive map satisfies the `∘` condition.
-/

/-- The doubling map `x ↦ 2 * x`. -/
def double (R : Type*) [CommRing R] : R →+ R where
  toFun x := 2 * x
  map_zero' := by simp
  map_add' x y := by simp only [mul_add]

/-- In a commutative ring with `4 = 0` the doubling map is a Jordan derivation in
the paper's `∘` form (Brešar 1988, p. 1003, where the converse fails). -/
theorem double_jder {R : Type*} [CommRing R] (h4 : (4 : R) = 0) : JDer (double R) := by
  intro x y
  simp only [jordan, double, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  linear_combination (-(x * y)) * h4

/-- The doubling map is a Jordan derivation on `ZMod 4`
(Brešar 1988, p. 1003). -/
theorem double_jder_zmod4 : JDer (double (ZMod 4)) := double_jder (by decide)

/-- The doubling map on `ZMod 4` is **not** a derivation: at `x = y = 1` the
Leibniz rule reads `2 = 2 + 2 = 0`.  With `der_jder` this makes the inclusion
`Der ⊊ JDer` proper, which is Brešar 1988, p. 1003, "the converse is false in
general". -/
theorem double_not_der : ¬ Der (double (ZMod 4)) := by
  intro h
  have h11 : (2 : ZMod 4) = 2 + 2 := by simpa [double] using h 1 1
  have h20 : (2 : ZMod 4) = 0 := by rw [h11]; decide
  exact absurd h20 (by decide)

/-- The doubling map on `ZMod 4` is not a Jordan derivation in Herstein's square
form: at `x = 1` the square identity reads `2 = 2 + 2 = 0`.  So without
2-torsion-freeness the two forms of the Jordan condition are genuinely different,
as the paper says (lines 186--189). -/
theorem double_not_hersteinJordan : ¬ hersteinJordan (double (ZMod 4)) := by
  intro h
  have h1 : (2 : ZMod 4) = 2 + 2 := by simpa [double] using h 1
  have h20 : (2 : ZMod 4) = 0 := by rw [h1]; decide
  exact absurd h20 (by decide)

/-- The identity map of `ZMod 4` is **not** a Jordan derivation: at `x = y = 1`
the `∘` condition reads `2 = 2 + 2 = 0`.  So the Jordan condition is not vacuous
on `ZMod 4`, which is what makes `double_jder` a genuine witness and not an
artefact of the ring (Brešar 1988, p. 1003). -/
theorem id_not_jder_zmod4 : ¬ JDer (AddMonoidHom.id (ZMod 4)) := by
  intro h
  have h11 : (1 : ZMod 4) + 1 = 0 := by simpa [jordan] using h 1 1
  exact absurd h11 (by decide)

/-- In a commutative ring in which every element is 2-torsion, `x ∘ y = 0`, so
every additive map satisfies the `∘` condition (paper, line 186). -/
theorem jder_of_two_torsion {A : Type*} [CommRing A] (h2 : ∀ a : A, a + a = 0)
    (D : A →+ A) : JDer D := by
  have hj : ∀ a b : A, jordan a b = 0 := by
    intro a b
    have h := h2 (a * b)
    simp only [jordan]
    rw [show a * b + b * a = a * b + a * b from by ring]
    exact h
  intro x y
  rw [hj x y, hj (D x) y, hj x (D y), map_zero, add_zero]

/-! ## The bridge to the paper's Definition 2.1

The Jordan class of Herstein 1957 is the class of braided-symmetric derivations
for the swap: `x ·_τ y = x * y + y * x` (paper, line 191).  The paper's product
`μ + μ ∘ σ` and the derivation condition are restated here at the level of the
product, so that this module connects to the paper's own definition; they are the
paper's notions, not Herstein's, Cusack's or Brešar's, which is why they are not
in the prelude.
-/

/-- The paper's symmetrized product `x ·_σ y = μ(x ⊗ y) + μ(σ(x ⊗ y))`, for a
binary map `σ` in place of the linear involution of `A ⊗ A` (paper, §1). -/
def symm (σ : A → A → A) (x y : A) : A := x * y + σ x y * σ y x

/-- The paper's braided-symmetric derivation condition for a product `P`,
`D (P x y) = P (D x) y + P x (D y)`, Definition 2.1 of the paper. -/
def BSDerP (P : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (P x y) = P (D x) y + P x (D y)

/-- For the swap `σ x y = y` the symmetrized product is the Jordan product, so
the braided-symmetric derivations are exactly the Jordan derivations in the
paper's `∘` form (paper, line 191). -/
theorem bsderP_swap_iff_jder (D : A →+ A) :
    BSDerP (symm fun _ y => y) D ↔ JDer D := Iff.rfl

/-- Every derivation is a braided-symmetric derivation for the swap: the paper's
inclusion `Der(A) ⊆ BSDer_τ(A) = JDer(A)` (paper, line 191, after Brešar 1988,
p. 1003). -/
theorem der_bsderP_swap {D : A →+ A} (h : Der D) : BSDerP (symm fun _ y => y) D :=
  (bsderP_swap_iff_jder D).mpr (der_jder h)

/-- The doubling map on `ZMod 4` is a braided-symmetric derivation for the swap
and not a derivation (`double_not_der`), so for this algebra the paper's inclusion
`Der(A) ⊆ BSDer_τ(A)` is proper (paper, line 191; Brešar 1988, p. 1003). -/
theorem double_bsderP_swap_zmod4 : BSDerP (symm fun _ y => y) (double (ZMod 4)) :=
  (bsderP_swap_iff_jder _).mpr double_jder_zmod4

end RefJordanHerstein
