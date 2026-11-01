import Mathlib

/-!
# `f`-derivations: Benkovič (2015), §1, and the fixed-polynomial notion of
Beidar, Brešar, Chebotar and Martindale (2001), Theorem 4.3

`paper/braided-sym-deriv.tex` line 99 reads

> Benkovič (§1) treats derivations, Jordan derivations and Lie derivations as
> `f`-derivations, for `f = x₁x₂`, `x₁ ∘ x₂` and `[x₁, x₂]`, so that one
> identity for a multilinear polynomial `f` covers all three.

and line 100 adds that Beidar, Brešar, Chebotar and Martindale (2001),
Theorem 4.3, studied maps that act as derivations on a *fixed* multilinear
polynomial, earlier than Benkovič.

## Contents

* `fDerivation f D`: Benkovič 2015, §1. For a multilinear polynomial `f` in `n`
  noncommuting variables and an additive map `D`, this is the identity
  `D (f v) = ∑ i, f (Function.update v i (D (v i)))`, where `v : Fin n → A` is
  the `n`-tuple of arguments and the `i`-th summand replaces the `i`-th
  argument by its image. The same notion, for a fixed multilinear polynomial,
  is what Beidar, Brešar, Chebotar and Martindale 2001, Theorem 4.3, study.
* the three instances of Benkovič §1, each **proved** in both directions as an
  equivalence with the notion of the paper's introduction: `f = x₁x₂` is `Der`,
  `f = x₁ ∘ x₂` is `JDer`, `f = x₁x₂ - x₂x₁` is `LieDer`.
* additivity of the notion in `f` (`fDerivation_add`, `fDerivation_neg`,
  `fDerivation_sub`) — this is how Benkovič applies the definition to a general
  `f = ∑ π ∈ Sₙ, α_π x_{π(1)} ⋯ x_{π(n)}` — and its triviality for a vanishing
  `f`.
* the higher-degree instance `f = x₁x₂x₃ + x₃x₂x₁` (`JTripleDer`), which shows
  that the definition is genuinely `n`-ary. The paper does not use it.
* a witness over `ℤ` that for a **non**-multilinear `f` the notion is different
  from a derivation, so that multilinearity in Benkovič §1 is not decoration.
* a record of what the paper borrows from Beidar, Brešar, Chebotar and
  Martindale 2001: priority for the notion only, no theorem. Accordingly this
  module contains no hypothesis-Prop: the paper relies on no deep theorem of
  either entry, only on the definition, which is proved to match the three
  notions of the paper.

## Conventions

Products are those of an associative ring `A` and maps are additive
(`A →+ A`), as in the paper's introduction: "we say so when a result cited
below holds more generally for additive maps on rings". The Jordan product is
`x ∘ y = xy + yx` **without** the half, as in Herstein 1957, p. 1104, whom the
paper follows here (line 104), so characteristic `2` is allowed;
Bresar--Zelmanov 2025, Example 2.1 use `½(xy + yx)`, which is half of this.

## References

* Benkovič, D.: A note on `f`-derivations of triangular algebras. Aequationes
  Math. 89 (2015), 1207--1211. Section 1.
* Beidar, K. I., Brešar, M., Chebotar, M. A., Martindale, W. S., III: On
  Herstein's Lie map conjectures, II. J. Algebra 238 (2001), 239--264.
  Theorem 4.3.
* Herstein, I. N.: Jordan derivations of prime rings. Proc. Amer. Math. Soc. 8
  (1957), 1104--1110.
* Martindale, W. S., III: Lie derivations of primitive rings. Michigan Math. J.
  11 (1964), 183--187.
-/

namespace RefFDerivation

variable {A : Type*} [Ring A]

/-! ## Prelude (may be lifted)

The notions of the paper's introduction, in the paper's conventions, so that
the three instances below can be stated against them. -/

/-- The Jordan product without the half, `x ∘ y = xy + yx`. The paper follows
Herstein 1957, p. 1104, and does not divide by `2`, so that characteristic `2`
is allowed (`paper/braided-sym-deriv.tex` line 104); `½(xy + yx)` is the Jordan
product of Bresar--Zelmanov 2025, Example 2.1. -/
def jordan (x y : A) : A := x * y + y * x

/-- The commutator `[x, y] = xy - yx`, the Lie product of the associative
algebra `A` (`paper/braided-sym-deriv.tex` line 98). -/
def commutator (x y : A) : A := x * y - y * x

/-- A derivation: `D (xy) = D x * y + x * D y` for an additive map `D`. The
notion goes back to Jacobson 1937, Part I, who studied derivations of an
arbitrary nonassociative algebra; for an associative algebra the derivations
are exactly the `1`-cocycles of Hochschild 1945, §§2 and 4.
`paper/braided-sym-deriv.tex` line 95. -/
def Der (D : A →+ A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- A Jordan derivation in the `∘` form, `D (x ∘ y) = D x ∘ y + x ∘ D y`, with
`∘` without the half (Herstein 1957, p. 1104; `paper/braided-sym-deriv.tex`
line 104). -/
def JDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (jordan x y) = jordan (D x) y + jordan x (D y)

/-- A Lie derivation: `D [x, y] = [D x, y] + [x, D y]`
(Martindale 1964, p. 183; `paper/braided-sym-deriv.tex` line 98). -/
def LieDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (commutator x y) = commutator (D x) y + commutator x (D y)

/-- Every derivation is a Jordan derivation. The `∘` form of the paper
immediately gives this because `D` is additive; Herstein 1957, p. 1104, states
the square form (`paper/braided-sym-deriv.tex` line 180). -/
theorem der_jder {D : A →+ A} (h : Der D) : JDer D := by
  intro x y
  simp only [jordan, map_add, h x y, h y x]
  abel

/-- Every derivation is a Lie derivation: the Leibniz rule for the commutator
(Martindale 1964, p. 183; `paper/braided-sym-deriv.tex` line 98). -/
theorem der_lie {D : A →+ A} (h : Der D) : LieDer D := by
  intro x y
  simp only [commutator, map_sub, h x y, h y x]
  abel

/-! ## `f`-derivations

Benkovič 2015, §1, in the additive form of the paper's introduction. -/

/-- **`f`-derivations** (Benkovič 2015, §1). For a multilinear polynomial `f` in
`n` noncommuting variables and an additive map `D : A →+ A`, Benkovič calls `D`
an `f`-derivation if

`D (f (x₁, …, xₙ)) = ∑ i, f (x₁, …, x_{i-1}, D x_i, x_{i+1}, …, xₙ)`

for all `x₁, …, xₙ ∈ A`. In the encoding here the `n`-tuple is `v : Fin n → A`
and the `i`-th summand is `f` evaluated at `Function.update v i (D (v i))`, that
is, at `v` with its `i`-th entry replaced by `D (v i)`.

The same notion, for a fixed multilinear polynomial, is what Beidar, Brešar,
Chebotar and Martindale 2001, Theorem 4.3, study; the paper cites them as prior
art on line 100 and quotes no statement of theirs. -/
def fDerivation {n : ℕ} (f : (Fin n → A) → A) (D : A →+ A) : Prop :=
  ∀ v : Fin n → A, D (f v) = ∑ i : Fin n, f (Function.update v i (D (v i)))

/-- `f`-derivations are additive in the polynomial. Benkovič 2015, §1 writes
`f` as a sum `∑ π ∈ Sₙ, α_π x_{π(1)} ⋯ x_{π(n)}` over the symmetric group, so
this is how the definition is applied to a general `f`: the sum of an
`f`-derivation and a `g`-derivation is an `(f + g)`-derivation. -/
theorem fDerivation_add {n : ℕ} {f g : (Fin n → A) → A} {D : A →+ A}
    (hf : fDerivation f D) (hg : fDerivation g D) :
    fDerivation (fun v => f v + g v) D := by
  intro v
  change D (f v + g v) = ∑ i : Fin n,
    (f (Function.update v i (D (v i))) + g (Function.update v i (D (v i))))
  rw [map_add, hf v, hg v, Finset.sum_add_distrib]

/-- `f`-derivations for `f` are `f`-derivations for `-f`: with
`fDerivation_add` this makes the set of polynomials for which a fixed `D` is a
derivation an additive subgroup. Benkovič 2015, §1: the coefficients `α_π` of
`f` may be negative. -/
theorem fDerivation_neg {n : ℕ} {f : (Fin n → A) → A} {D : A →+ A}
    (hf : fDerivation f D) : fDerivation (fun v => -f v) D := by
  intro v
  change D (-f v) = ∑ i : Fin n, -(f (Function.update v i (D (v i))))
  rw [map_neg, hf v, Finset.sum_neg_distrib]

/-- `f`-derivations are subtractive in the polynomial (Benkovič 2015, §1). This
is the form in which the instance `f = x₁x₂ - x₂x₁` is obtained from the two
monomials `x₁x₂` and `x₂x₁`. -/
theorem fDerivation_sub {n : ℕ} {f g : (Fin n → A) → A} {D : A →+ A}
    (hf : fDerivation f D) (hg : fDerivation g D) :
    fDerivation (fun v => f v - g v) D := by
  intro v
  change D (f v - g v) = ∑ i : Fin n,
    (f (Function.update v i (D (v i))) - g (Function.update v i (D (v i))))
  rw [map_sub, hf v, hg v, Finset.sum_sub_distrib]

/-- If the polynomial vanishes identically then every additive map is an
`f`-derivation. Benkovič 2015, §1 takes `f` to have a nonzero coefficient sum
precisely to exclude this degeneracy; the instance `f = x₁x₂ - x₂x₁` below is of
this kind exactly when `A` is commutative. -/
theorem fDerivation_of_eq_zero {n : ℕ} {f : (Fin n → A) → A} (hf : ∀ v, f v = 0)
    (D : A →+ A) : fDerivation f D := by
  intro v
  simp [hf]

/-! ## The three instances of Benkovič 2015, §1

Line 99 of the paper: `f = x₁x₂`, `x₁ ∘ x₂`, `[x₁, x₂]`. Each is proved, in
both directions, to be exactly the corresponding notion of the introduction. -/

/-- Benkovič 2015, §1, the instance `f = x₁x₂`: an additive map is an
`(x₁x₂)`-derivation exactly when it is a derivation. -/
theorem fDerivation_mul_iff (D : A →+ A) :
    fDerivation (fun v : Fin 2 → A => v 0 * v 1) D ↔ Der D := by
  constructor
  · intro h x y
    have h' := h (fun i : Fin 2 => if i = 0 then x else y)
    rw [Fin.sum_univ_two] at h'
    simpa using h'
  · intro h v
    have h' := h (v 0) (v 1)
    rw [Fin.sum_univ_two]
    simpa using h'

/-- Benkovič 2015, §1, the instance `f = x₁ ∘ x₂ = x₁x₂ + x₂x₁`, with the
Jordan product without the half (Herstein 1957, p. 1104): an additive map is an
`(x₁ ∘ x₂)`-derivation exactly when it is a Jordan derivation. -/
theorem fDerivation_jordan_iff (D : A →+ A) :
    fDerivation (fun v : Fin 2 → A => v 0 * v 1 + v 1 * v 0) D ↔ JDer D := by
  constructor
  · intro h x y
    have h' := h (fun i : Fin 2 => if i = 0 then x else y)
    rw [Fin.sum_univ_two] at h'
    simp only [jordan]
    simpa using h'
  · intro h v
    have h' := h (v 0) (v 1)
    simp only [jordan] at h'
    rw [Fin.sum_univ_two]
    simpa using h'

/-- Benkovič 2015, §1, the instance `f = [x₁, x₂] = x₁x₂ - x₂x₁`: an additive
map is an `[x₁, x₂]`-derivation exactly when it is a Lie derivation
(Martindale 1964, p. 183). -/
theorem fDerivation_commutator_iff (D : A →+ A) :
    fDerivation (fun v : Fin 2 → A => v 0 * v 1 - v 1 * v 0) D ↔ LieDer D := by
  constructor
  · intro h x y
    have h' := h (fun i : Fin 2 => if i = 0 then x else y)
    rw [Fin.sum_univ_two] at h'
    simp only [commutator]
    simpa using h'
  · intro h v
    have h' := h (v 0) (v 1)
    simp only [commutator] at h'
    rw [Fin.sum_univ_two]
    simpa using h'

/-- Benkovič 2015, §1, line 99 of the paper, converse direction made explicit: a
derivation is an `(x₁ ∘ x₂)`-derivation. -/
theorem der_fDerivation_jordan (D : A →+ A) (h : Der D) :
    fDerivation (fun v : Fin 2 → A => v 0 * v 1 + v 1 * v 0) D :=
  (fDerivation_jordan_iff D).mpr (der_jder h)

/-- Benkovič 2015, §1, line 99 of the paper, converse direction made explicit: a
derivation is an `[x₁, x₂]`-derivation (Martindale 1964, p. 183). -/
theorem der_fDerivation_commutator (D : A →+ A) (h : Der D) :
    fDerivation (fun v : Fin 2 → A => v 0 * v 1 - v 1 * v 0) D :=
  (fDerivation_commutator_iff D).mpr (der_lie h)

/-- For `n = 1` and `f = x₁` the notion is vacuous: every additive map is an
`x₁`-derivation. This is why the `f`-derivation literature takes the degree of
`f` to be at least `2` (Benkovič 2015, §1 studies the three degree-`2` instances
of line 99 of the paper). -/
theorem fDerivation_deg_one (D : A →+ A) :
    fDerivation (fun v : Fin 1 → A => v 0) D := by
  intro v
  rw [Fin.sum_univ_one]
  simp

/-! ## A non-multilinear `f`: the notion is strictly weaker than a derivation

Benkovič 2015, §1 takes `f` to be *multilinear*: a sum of monomials
`x_{π(1)} ⋯ x_{π(n)}`, each using every one of the `n` variables exactly once.
The next three declarations show that the multilinearity is essential: for the
non-multilinear `f (x) = x²` on `ℤ` the identity map is an `f`-derivation but
not a derivation. (For the multilinear `f = x₁x₂` the two notions coincide by
`fDerivation_mul_iff`.) -/

/-- For the non-multilinear `f (x) = x²` (one variable, used twice) on `ℤ`, the
identity map is an `f`-derivation: `D (x²) = (D x)²` holds for `D = id`
(Benkovič 2015, §1 requires `f` multilinear, so this `f` is outside the
notion's scope; the example delimits it). -/
theorem id_int_fDerivation_sq :
    fDerivation (fun v : Fin 1 → ℤ => v 0 * v 0) (AddMonoidHom.id ℤ) := by
  intro v
  rw [Fin.sum_univ_one]
  simp

/-- The identity map of `ℤ` is not a derivation: `1 = id (1 · 1)` but
`id 1 · 1 + 1 · id 1 = 2` (Jacobson 1937, Part I, and Hochschild 1945, §2, for
the notion of derivation). -/
theorem id_int_not_der : ¬ Der (AddMonoidHom.id ℤ) := by
  intro h
  have h1 := h 1 1
  simp only [AddMonoidHom.id_apply, mul_one] at h1
  omega

/-- The two notions therefore differ: some additive map on `ℤ` is an
`f`-derivation for some `f` and not a derivation (Benkovič 2015, §1 for the
notion, and the multilinearity hypothesis that this example steps outside of). -/
theorem exists_fDerivation_not_der :
    ∃ (f : (Fin 1 → ℤ) → ℤ) (D : ℤ →+ ℤ), fDerivation f D ∧ ¬ Der D :=
  ⟨fun v => v 0 * v 0, AddMonoidHom.id ℤ, id_int_fDerivation_sq, id_int_not_der⟩

/-! ## A higher-degree instance: `f = x₁x₂x₃ + x₃x₂x₁`

The paper needs only the three degree-`2` instances of line 99; this section is
here because `fDerivation` is genuinely `n`-ary and a degree-`3` instance shows
that the sum over `Fin n` is the right shape. Benkovič 2015, §1 for the notion. -/

/-- The **Jordan triple derivation** identity, the instance
`f = x₁x₂x₃ + x₃x₂x₁` of `fDerivation` for `n = 3`: the image of `xyz + zyx`
is the sum of the six terms obtained by replacing one factor by its image,
listed in the order in which the sum `∑ i, f (…, D xᵢ, …)` meets them. -/
def JTripleDer (D : A →+ A) : Prop :=
  ∀ x y z : A, D (x * y * z + z * y * x) =
    (D x * y * z + z * y * D x) + (x * D y * z + z * D y * x)
      + (x * y * D z + D z * y * x)

/-- Benkovič 2015, §1, the instance `f = x₁x₂x₃ + x₃x₂x₁` for `n = 3`: an
additive map is an `f`-derivation exactly when it satisfies the Jordan triple
derivation identity `JTripleDer`. -/
theorem fDerivation_jordanTriple_iff (D : A →+ A) :
    fDerivation (fun v : Fin 3 → A => v 0 * v 1 * v 2 + v 2 * v 1 * v 0) D ↔
      JTripleDer D := by
  constructor
  · intro h x y z
    have h' : D (x * y * z + z * y * x) =
        (D x * y * z + z * y * D x) + (x * D y * z + z * D y * x)
          + (x * y * D z + D z * y * x) := by
      simpa [Fin.sum_univ_three] using
        h (fun i : Fin 3 => if i = 0 then x else if i = 1 then y else z)
    rw [h']
  · intro h v
    have h' : D (v 0 * v 1 * v 2 + v 2 * v 1 * v 0) =
        (D (v 0) * v 1 * v 2 + v 2 * v 1 * D (v 0))
          + (v 0 * D (v 1) * v 2 + v 2 * D (v 1) * v 0)
          + (v 0 * v 1 * D (v 2) + D (v 2) * v 1 * v 0) :=
      h (v 0) (v 1) (v 2)
    simpa [Fin.sum_univ_three] using h'

/-! ## Beidar, Brešar, Chebotar and Martindale 2001, Theorem 4.3

`paper/braided-sym-deriv.tex` line 100 cites this entry only to record that maps
acting as derivations on a *fixed* multilinear polynomial were studied before
Benkovič (the changelog of the paper states the same: "Theorem 4.3 really is
about a fixed multilinear polynomial"). The paper quotes no statement from the
entry and no later argument of the paper uses one, so no theorem of the
reference is formalized here and no hypothesis-Prop is stated: the notion that
the citation names is exactly `fDerivation` above, whose docstring carries the
joint attribution.

The same holds for Benkovič 2015 itself: the paper takes only the definition
from §1 (line 99), not the results on triangular algebras, so there is no deep
theorem of either reference for this module to take as a hypothesis. -/

end RefFDerivation
