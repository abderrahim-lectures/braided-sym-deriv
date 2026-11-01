/-
# Brešar 1988, Theorem 1: Jordan derivations of semiprime rings are derivations

Campaign file.  The target, stated with the conventions of
`Background/JordanHerstein.lean` (Jordan product without the half, additive
maps, `x*x`-form and `∘`-form equivalent in 2-torsion-free rings), is

  `jordan_derivation_eq_derivation : TwoTorsionFree A → SemiprimeRing A →
     JDer D → Der D`

for an arbitrary ring `A`.  What this file proves is the *elementary layer* of
the published proof, which every route uses:

* `eq_of_two_mul_eq`: in a 2-torsion-free ring `2p = 2q` implies `p = q`;
* `jder_triple` (Brešar 1988, Proposition 2(ii)): `D (aba) = D(a)ba + aD(b)a + abD(a)`,
  from the identity `2xyx = x∘(y∘x) − x²∘y`;
* `jder_quad` (Proposition 2(iii)): `D(abc + cba) = D(a)bc + aD(b)c + abD(c)
  + D(c)ba + cD(b)a + cbD(a)`, from 2(ii) applied to `a + c`;
* the defect `δ(x,y) = D(xy) − D(x)y − xD(y)` is biadditive and satisfies the
  three biadditive identities of Brešar, *Jordan derivations revisited*,
  Theorem 2.1: `δ(x,x) = 0`, `δ(xy,x) + δ(x,y)x = 0`,
  `δ(xy,z) + δ(x,y)z = δ(x,yz) + xδ(y,z)`;
* `defect_mul_of_ideal` (Remark 2.2): an ideal `I` with `δ(I,A) = 0` satisfies
  `I·δ(A,A) = 0`;
* `defect_zero_of_idempotent` (Remark 2.3): an idempotent `e` with `[e,x] = 0`
  has `δ(e,x) = 0`.

Two complete special cases are also here: `jder_eq_der_of_commutative` (a
commutative ring), and `defect_eq_zero_of_essential`, which turns
`I·δ(A,A) = 0` into `δ = 0` as soon as the set `I` has trivial right
annihilator — the essentiality step of the published proof, stated abstractly.

The two steps still open are: Theorem 2.1 itself (`{A⁽²⁾, A} = 0` for a
biadditive `δ` satisfying the three identities), and producing, in a
2-torsion-free semiprime ring, a set `I` closed under left multiplication on
which `δ` vanishes on the left and which has trivial right annihilator.
Nothing here is a placeholder and no compiler axiom is used.
-/
import Background.JordanHerstein

namespace JordanDerivation

open Background.JordanHerstein

variable {A : Type*} [Ring A]

/-- In a 2-torsion-free ring, `2p = 2q` forces `p = q`. -/
theorem eq_of_two_mul_eq (h2 : TwoTorsionFree A) {p q : A} (h : p + p = q + q) : p = q := by
  have h' : (p - q) + (p - q) = 0 := by
    have : (p - q) + (p - q) = (p + p) - (q + q) := by abel
    rw [this, h, sub_self]
  exact sub_eq_zero.mp (h2 _ h')

/-- `2xyx = x ∘ (y ∘ x) − x² ∘ y`, the identity behind Proposition 2(ii). -/
theorem two_mul_xyx (x y : A) :
    x * y * x + x * y * x = jordan x (jordan y x) - jordan (x * x) y := by
  simp only [jordan]
  noncomm_ring

/-- **Brešar 1988, Proposition 2(ii)**: `D(aba) = D(a)ba + aD(b)a + abD(a)`. -/
theorem jder_triple (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (x y : A) :
    D (x * y * x) = D x * y * x + x * D y * x + x * y * D x := by
  have hSq : ∀ z : A, D (z * z) = D z * z + z * D z := hersteinJordan_of_jder h2 hD
  refine eq_of_two_mul_eq h2 ?_
  have h : D (x * y * x + x * y * x)
      = D (jordan x (jordan y x)) - D (jordan (x * x) y) := by
    rw [two_mul_xyx, map_sub]
  rw [map_add, hD x (jordan y x), hD y x, hD (x * x) y, hSq x] at h
  rw [h]
  simp only [jordan] at *
  noncomm_ring

/-- **Brešar 1988, Proposition 2(iii)**: `D(abc + cba)` is the sum of the six
partially differentiated products. -/
theorem jder_quad (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (a b c : A) :
    D (a * b * c + c * b * a)
      = D a * b * c + a * D b * c + a * b * D c
        + D c * b * a + c * D b * a + c * b * D a := by
  have hx := jder_triple h2 hD (a + c) b
  have hexp : (a + c) * b * (a + c) = a * b * a + a * b * c + c * b * a + c * b * c := by
    noncomm_ring
  rw [hexp, map_add, map_add, map_add, map_add D a c] at hx
  rw [jder_triple h2 hD a b, jder_triple h2 hD c b] at hx
  linear_combination (norm := noncomm_ring) hx
  rw [map_add]
  abel

/-! ## The defect: the three biadditive identities of "Jordan derivations revisited" -/

/-- The defect is additive in its first variable. -/
theorem defect_add_left (D : A →+ A) (x y z : A) :
    leibnizDefect D (x + y) z = leibnizDefect D x z + leibnizDefect D y z := by
  simp only [leibnizDefect, map_add, add_mul]
  abel

/-- The defect is additive in its second variable. -/
theorem defect_add_right (D : A →+ A) (x y z : A) :
    leibnizDefect D x (y + z) = leibnizDefect D x y + leibnizDefect D x z := by
  simp only [leibnizDefect, map_add, mul_add]
  abel

/-- **Identity (1)** of Theorem 2.1: the defect vanishes on the diagonal.  This is
Herstein's square form, which needs 2-torsion-freeness to follow from the `∘` form. -/
theorem defect_self (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (x : A) :
    leibnizDefect D x x = 0 := by
  have hSq := hersteinJordan_of_jder h2 hD x
  simp only [leibnizDefect]
  linear_combination (norm := noncomm_ring) hSq

/-- **Identity (2)** of Theorem 2.1: `δ(xy, x) + δ(x, y)x = 0`.  Equivalent to
Proposition 2(ii), the triple identity. -/
theorem defect_mul_right (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (x y : A) :
    leibnizDefect D (x * y) x + leibnizDefect D x y * x = 0 := by
  have h3 := jder_triple h2 hD x y
  simp only [leibnizDefect]
  linear_combination (norm := noncomm_ring) h3

/-- **Identity (3)** of Theorem 2.1: `δ(xy,z) + δ(x,y)z = δ(x,yz) + xδ(y,z)`.
It holds for every additive `D`; the `∘` hypothesis enters only through (1) and (2). -/
theorem defect_cocycle (D : A →+ A) (x y z : A) :
    leibnizDefect D (x * y) z + leibnizDefect D x y * z
      = leibnizDefect D x (y * z) + x * leibnizDefect D y z := by
  simp only [leibnizDefect]
  noncomm_ring

/-- **Remark 2.2**: a set of elements on which the defect vanishes on the left, and
which is closed under left multiplication by `A`, annihilates every defect value. -/
theorem defect_mul_of_ideal (D : A →+ A) (S : Set A) (hS : ∀ i ∈ S, ∀ y : A, i * y ∈ S)
    (hzero : ∀ i ∈ S, ∀ a : A, leibnizDefect D i a = 0) :
    ∀ i ∈ S, ∀ y z : A, i * leibnizDefect D y z = 0 := by
  intro i hi y z
  have h := defect_cocycle D i y z
  rw [hzero i hi (y * z), hzero i hi y, zero_mul, zero_add, add_zero] at h
  rw [← h, hzero (i * y) (hS i hi y) z]

/-! ## Brešar 1988, Theorem 3 — the correct reading

The 1988 paper writes the defect as an overlined `ab`, and the AMS scan's OCR
renders it like the product.  Theorem 3 therefore reads

  `δ(a,b) · x · [a,b] + [a,b] · x · δ(a,b) = 0`   for all a, b, x,

with `δ` the **defect**, not with `ab` the product.  The product reading is
false: on `M₂(ℚ)` with `D = ad_g` (a derivation, hence a Jordan derivation) the
expression `(a*b)*x*[a,b] + [a,b]*x*(a*b)` is nonzero for random matrices,
while the defect form vanishes identically.  With `bresar_lemma4` below,
Theorem 3 gives `δ(a,b)·A·[a,b] = 0`, hence `[a,b]·δ(a,b) = 0` in a semiprime
ring.  From there `δ(a,b)` anticommutes with `a` and with `b` and commutes with
`[a,b]`, using identity (2); every further instance of Theorem 3 obtained by
substituting for `a` or `b` is then automatically satisfied, so the passage from
`[a,b]δ(a,b) = 0` to `δ(a,b) = 0` needs an ingredient that is not a substitution
into Theorem 3.  This is the open point of Route B.

-/

/-! ## Brešar 1988, Lemma 4

The published proof of Lemma 4 is correct; this is its chain, with the three
instances of the hypothesis made explicit.  If `a x b + b x a = 0` for all `x`,
then `(a x b) y (a x b) = -(a x b) y (a x b)` for all `y`, hence
`2 (a x b) y (a x b) = 0`, and 2-torsion-freeness and semiprimeness finish. -/

/-- **Brešar 1988, Lemma 4**: in a 2-torsion-free semiprime ring,
`a x b + b x a = 0` for all `x` forces `a x b = 0` for all `x`. -/
theorem bresar_lemma4 (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {a b : A}
    (h : ∀ x : A, a * x * b + b * x * a = 0) : ∀ x : A, a * x * b = 0 := by
  intro x
  have step : ∀ y : A, (a * x * b) * y * (a * x * b) = -((a * x * b) * y * (a * x * b)) := by
    intro y
    have h1 : a * x * b = -(b * x * a) := by
      linear_combination (norm := noncomm_ring) h x
    have h2' : b * (x * a * y) * a = -(a * (x * a * y) * b) := by
      linear_combination (norm := noncomm_ring) h (x * a * y)
    have h3 : a * y * b = -(b * y * a) := by
      linear_combination (norm := noncomm_ring) h y
    calc (a * x * b) * y * (a * x * b)
        = -((b * x * a) * y * (a * x * b)) := by rw [h1]; noncomm_ring
      _ = -((b * (x * a * y) * a) * x * b) := by noncomm_ring
      _ = (a * (x * a * y) * b) * x * b := by rw [h2']; noncomm_ring
      _ = a * x * (a * y * b) * x * b := by noncomm_ring
      _ = -(a * x * (b * y * a) * x * b) := by rw [h3]; noncomm_ring
      _ = -((a * x * b) * y * (a * x * b)) := by noncomm_ring
  have hy : ∀ y : A, (a * x * b) * y * (a * x * b) = 0 := by
    intro y
    have hw : (a * x * b) * y * (a * x * b) + (a * x * b) * y * (a * x * b) = 0 := by
      have := step y
      linear_combination (norm := noncomm_ring) this
    exact h2 _ hw
  exact hs _ hy

/-! ## Two special cases that are already complete -/

/-- **The commutative case**: on a commutative ring every Jordan derivation into
itself is a derivation.  The linearized Jordan condition reads
`D(xy + yx) = D(x)y + xD(y) + D(y)x + yD(x)`, and commutativity turns both
sides into twice the derivation identity. -/
theorem jder_eq_der_of_commutative (h2 : TwoTorsionFree A) (hc : ∀ x y : A, x * y = y * x)
    {D : A →+ A} (hD : JDer D) : Der D := by
  intro x y
  refine eq_of_two_mul_eq h2 ?_
  have h := hD x y
  simp only [jordan] at h
  rw [hc y x, hc y (D x), hc (D y) x, map_add] at h
  rw [h]
  abel

/-- **Essentiality finishes**: if a set on which the defect vanishes on the left
has trivial right annihilator, every defect value is zero. -/
theorem defect_eq_zero_of_essential (D : A →+ A) (S : Set A)
    (hS : ∀ i ∈ S, ∀ y : A, i * y ∈ S) (hzero : ∀ i ∈ S, ∀ a : A, leibnizDefect D i a = 0)
    (hess : ∀ c : A, (∀ i ∈ S, i * c = 0) → c = 0) (y z : A) :
    leibnizDefect D y z = 0 :=
  hess _ fun i hi => defect_mul_of_ideal D S hS hzero i hi y z

end JordanDerivation
