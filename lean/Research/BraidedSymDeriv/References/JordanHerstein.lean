import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# Jordan derivations: Herstein 1957, Cusack 1975, Brešar 1988

The paper (§1, lines 104--113 and 180--191) uses four facts from this cluster:

* Herstein 1957, p. 1104 states the Jordan derivation condition first in the
  **`∘` form** — "for all a, b: `(a ∘ b)' = a' ∘ b + a ∘ b'`, written out as
  `(ab + ba)' = a'b + ab' + b'a + ba'`" — and then says that "for most of this
  paper all rings considered will be of characteristic not 2; for such rings a
  Jordan derivation can be defined by `(a + b)' = a' + b'` and
  `(a²)' = aa' + a'a`". The square form is therefore Herstein's
  characteristic-≠2 simplification, not his general definition; the paper's §1
  attributes the square form to p. 1104 without recording that restriction (see
  `results/references-formalization.md`, §3.1). Theorem 3.1 of Herstein — on a
  prime ring of characteristic different from 2 every Jordan derivation is a
  derivation — is stated below as a hypothesis;
* Cusack 1975, Corollary 5 extends this to 2-torsion-free semiprime rings, and
  Cusack 1975, §2 studies Jordan derivations through the defect
  `d(a,b) = D(ab) - aD(b) - (Da)b`;
* Brešar 1988 gives the three ring conditions (prime, semiprime, 2-torsion-free,
  p. 1003), the remark that every derivation is a Jordan derivation and that the
  converse fails in general, and Theorem 1, an independent proof of Cusack's
  Corollary 5.

The content that is *elementary* is the linearisation: Herstein's square form
implies the `∘` form in **every** characteristic, with no torsion hypothesis.
(The converse needs 2-torsion-freeness, which is exactly what the paper's §1
remark says.) Brešar states his Proposition 2(i), the same linearisation, under
his blanket 2-torsion-free hypothesis; the hypothesis is not needed for it.

Theorem 3.1 of Herstein, Corollary 5 of Cusack and Theorem 1 of Brešar are
research results of functional-identity theory. They are *stated* here as
`Prop`-valued hypotheses and never proved, and nothing in this module stands in
for them.

## Main results

* `RefJordanHerstein.linearisation`: the pure ring identity behind the
  linearisation, with no hypothesis on `D`.
* `RefJordanHerstein.herstein_imp_jder`: Herstein's square form implies the `∘`
  form, in every characteristic.
* `RefJordanHerstein.jder_imp_herstein`: the converse under 2-torsion-freeness.
* `RefJordanHerstein.cusackDefect`: Cusack's defect is the paper's `E_D`.
* `RefJordanHerstein.hersteinTheorem`, `cusackCorollary`, `bresarTheorem`: the
  three deep theorems as hypotheses, with consumers.
* `RefJordanHerstein.Witness`: in a commutative ring of characteristic 2 the `∘`
  condition is vacuous, so the identity map of `F₂` is a Jordan derivation and
  not a derivation — the paper's own remark, and the reason Brešar's "the
  converse fails in general" holds.

## References

* Cusack, J. M.: Jordan derivations on rings. Proc. Amer. Math. Soc. 53 (1975),
  321--324, §2 and Corollary 5.
* Herstein, I. N.: Jordan derivations of prime rings. Proc. Amer. Math. Soc. 8
  (1957), 1104--1110, p. 1104 and Theorem 3.1.
* Bresar, M.: Jordan derivations on semiprime rings. Proc. Amer. Math. Soc. 104
  (1988), 1003--1006, p. 1003, Proposition 2 and Theorem 1.
-/

namespace RefJordanHerstein

open Ref

variable {A : Type*} [Ring A]

/-! ## The linearisation -/

/-- The pure ring identity behind the linearisation of Herstein's condition:
the difference of the `(x + y)` instance of `D(x²) = D(x)x + xD(x)` and the two
instances at `x` and at `y` is the defect of the `∘` condition. No hypothesis on
`D` is used, and no division by 2. -/
theorem linearisation (D : A →+ A) (x y : A) :
    (D ((x + y) * (x + y)) - (D (x + y) * (x + y) + (x + y) * D (x + y)))
        - (D (x * x) - (D x * x + x * D x))
        - (D (y * y) - (D y * y + y * D y))
      = (D (x * y) + D (y * x))
        - ((D x * y + x * D y) + (D y * x + y * D x)) := by
  simp only [map_add, mul_add, add_mul]
  abel

/-- **Herstein 1957, p. 1104 implies the `∘` form**, in every characteristic. -/
theorem herstein_imp_jder (D : A →+ A) (h : hersteinJordan D) : JDer D := by
  intro x y
  have key := linearisation D x y
  rw [show D ((x + y) * (x + y)) - (D (x + y) * (x + y) + (x + y) * D (x + y)) = 0 from by
        rw [h (x + y)]; abel,
      show D (x * x) - (D x * x + x * D x) = 0 from by rw [h x]; abel,
      show D (y * y) - (D y * y + y * D y) = 0 from by rw [h y]; abel,
      sub_self, sub_zero] at key
  have hsum : D (x * y) + D (y * x)
      = (D x * y + x * D y) + (D y * x + y * D x) := sub_eq_zero.mp key.symm
  simp only [jordan, map_add, hsum]
  abel

/-- The converse, under 2-torsion-freeness: setting `y = x` in the `∘` form
leaves `2(D(x²) - D(x)x - xD(x)) = 0`, and `2` is cancellable. This is the
statement of the paper's §1 remark. -/
theorem jder_imp_herstein (D : A →+ A) (h2 : TwoTorsionFree A) (h : JDer D) :
    hersteinJordan D := by
  intro x
  have hx := h x x
  simp only [jordan, map_add] at hx
  have hsum : D (x * x) + D (x * x)
      = (D x * x + x * D x) + (D x * x + x * D x) := by
    rw [hx]
    abel
  have h0 : (D (x * x) - (D x * x + x * D x))
      + (D (x * x) - (D x * x + x * D x)) = 0 := by
    have hdiff : (D (x * x) - (D x * x + x * D x))
        + (D (x * x) - (D x * x + x * D x))
        = (D (x * x) + D (x * x))
          - ((D x * x + x * D x) + (D x * x + x * D x)) := by
      abel
    rw [hdiff, hsum, sub_self]
  exact sub_eq_zero.mp (h2 _ h0)

/-- Under 2-torsion-freeness the two forms of the Jordan condition agree, which
is the sentence of the paper's §1 (lines 181--186). -/
theorem herstein_iff_jder (D : A →+ A) (h2 : TwoTorsionFree A) :
    hersteinJordan D ↔ JDer D :=
  ⟨herstein_imp_jder D, jder_imp_herstein D h2⟩

/-! ## Cusack's defect -/

/-- Cusack 1975, §2 writes the defect of a Jordan derivation as
`d(a,b) = D(ab) - aD(b) - (Da)b`. It is the paper's `E_D`, the two orderings of
the two middle terms differing by commutativity of addition in `A`. -/
def cusackDefect (D : A →+ A) (a b : A) : A := D (a * b) - a * D b - D a * b

/-- Cusack's defect is the paper's Leibniz defect, Definition 3.1. -/
theorem cusackDefect_eq (D : A →+ A) (a b : A) :
    cusackDefect D a b = leibnizDefect D a b := by
  simp only [cusackDefect, leibnizDefect]
  abel

/-! ## The three deep theorems, as hypotheses

None of the three is proved here. Each is a `Prop`-valued definition, so every
place that uses one carries it as an explicit hypothesis, and the statement of
the theorem is machine-checked even where its proof is not available. -/

/-- **Herstein 1957, Theorem 3.1**: on a prime ring where 2 is cancellable, every
Jordan derivation is a derivation. Not proved here. -/
def hersteinTheorem (R : Type*) [Ring R] : Prop :=
  PrimeRing R → TwoTorsionFree R → ∀ D : R →+ R, JDer D → Der D

/-- **Cusack 1975, Corollary 5**: on a semisimple (in particular a 2-torsion-free
semiprime) ring every Jordan derivation is a derivation. The semiprime version is
the one the paper uses; `bresarTheorem` is the same statement. Not proved here. -/
def cusackCorollary (R : Type*) [Ring R] : Prop :=
  TwoTorsionFree R → SemiprimeRing R → ∀ D : R →+ R, JDer D → Der D

/-- **Brešar 1988, Theorem 1**: on a 2-torsion-free semiprime ring every Jordan
derivation is a derivation. This is the form the paper quotes as its Theorem 3.4
and takes as a hypothesis in Corollary 3.5. Not proved here. -/
def bresarTheorem (R : Type*) [Ring R] : Prop :=
  TwoTorsionFree R → SemiprimeRing R → ∀ D : R →+ R, JDer D → Der D

/-- Consumer of `bresarTheorem`, in the shape of the paper's Corollary 3.5: a
Jordan derivation of a 2-torsion-free semiprime ring is a derivation, and a
derivation in Herstein's square form is a derivation. -/
theorem jder_eq_der_of_bresar {R : Type*} [Ring R] (h : bresarTheorem R)
    (h2 : TwoTorsionFree R) (hsp : SemiprimeRing R) (D : R →+ R) :
    JDer D ↔ Der D :=
  ⟨h h2 hsp D, der_jder⟩

/-- Consumer of `hersteinTheorem`: a prime ring of characteristic different from
2 has the same property, since a prime ring is semiprime. -/
theorem jder_eq_der_of_herstein {R : Type*} [Ring R] (h : hersteinTheorem R)
    (hp : PrimeRing R) (h2 : TwoTorsionFree R) (D : R →+ R) :
    JDer D ↔ Der D :=
  ⟨h hp h2 D, der_jder⟩

/-! ## The converse fails in general -/

namespace Witness

/-- In a commutative ring of characteristic 2 the Jordan product vanishes, so
every additive map satisfies the `∘` condition — the sentence of the paper's §1:
"When char K = 2 and A is commutative, `x ∘ y = 0`, and every linear map
satisfies the `∘` condition." -/
theorem jordan_eq_zero (x y : ZMod 2) : Ref.jordan x y = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hmul : x * y + y * x = (2 : ZMod 2) * (x * y) := by
    rw [two_mul, mul_comm y x]
  simp only [Ref.jordan, hmul, h2, zero_mul]

/-- Every additive map of `F₂` is a Jordan derivation. -/
theorem jder (D : ZMod 2 →+ ZMod 2) : Ref.JDer D := by
  intro x y
  rw [jordan_eq_zero, jordan_eq_zero, jordan_eq_zero]
  simp

/-- The identity map of `F₂` is not a derivation: `1 · 1 = 1` but
`1 · 1 + 1 · 1 = 0`. -/
theorem id_not_der : ¬ Ref.Der (AddMonoidHom.id (ZMod 2)) := by
  intro h
  have h1 := h 1 1
  simp only [AddMonoidHom.id_apply, mul_one] at h1
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h2] at h1
  exact one_ne_zero h1

end Witness

end RefJordanHerstein
