/-
# Brešar 1988, Theorem 1: every Jordan derivation of a 2-torsion-free semiprime
ring is a derivation

M. Brešar, *Jordan derivations on semiprime rings*, Proc. Amer. Math. Soc. 104
(1988), 1003--1006, Theorem 1.  This file proves it, so that the theorem is no
longer a hypothesis anywhere in the development: `Background.JordanHerstein`
states it as a `Prop`, and `bresar1988Theorem1_holds` below
discharges it, which makes the paper's Corollary 3.5 unconditional.

The proof is the paper's own, in its numbering: Proposition 2 (i),(ii),(iii);
the defect is biadditive, alternating, and satisfies the cocycle identity;
Theorem 3 (`w(a,b)·x·[a,b] + [a,b]·x·w(a,b) = 0`, where the paper's overlined
`ab` is the defect); Lemma 4; and then the endgame of Theorem 1's proof, which
is the part the paper does not spell out: the defect annihilates every
commutator (`five`--`eight`), is central (`defect_central`), satisfies
`2w² = w·D[a,b]` (`nine`), `4w² + Dw·[a,b] + [a,b]·Dw = 0` (`ten`), hence
`4w³ = 0` (`eleven`) and, by 2-torsion-freeness and semiprimeness, `w = 0`
(`twelve`).

Provenance: the proof was produced by member `m2` of the Ultramath swarm
`smvxzvgty` (campaign "prove Brešar 1988, Theorem 1"), and checked here: it
elaborates under the project's own toolchain with no `sorry`, no
`native_decide` and no new axiom, footprint
`{propext, Classical.choice, Quot.sound}`.
-/
import Background.JordanHerstein

/-- `linear_combination` leaves `(-1) • x` behind; normalise it away before
`noncomm_ring`. -/
macro "NC" : tactic =>
  `(tactic| first | noncomm_ring | (simp only [neg_one_smul, neg_neg]; noncomm_ring))

namespace Bresar1988

open Background.JordanHerstein

universe u

variable {A : Type*} [Ring A]

/-! ## The defect is biadditive and alternating -/

theorem defect_add_left (D : A →+ A) (x y z : A) :
    leibnizDefect D (x + y) z = leibnizDefect D x z + leibnizDefect D y z := by
  simp only [leibnizDefect, map_add, add_mul]
  abel

theorem defect_add_right (D : A →+ A) (x y z : A) :
    leibnizDefect D x (y + z) = leibnizDefect D x y + leibnizDefect D x z := by
  simp only [leibnizDefect, map_add, mul_add]
  abel

/-- `w(a,b) = -w(b,a)`: exactly the Jordan condition. -/
theorem defect_skew {D : A →+ A} (hD : JDer D) (x y : A) :
    leibnizDefect D x y + leibnizDefect D y x = 0 := by
  have h := hD x y
  simp only [jordan, map_add, leibnizDefect] at h ⊢
  linear_combination (norm := noncomm_ring) h

theorem defect_skew' {D : A →+ A} (hD : JDer D) (x y : A) :
    leibnizDefect D x y = - leibnizDefect D y x := by
  have h := defect_skew hD x y
  exact eq_neg_iff_add_eq_zero.mpr h

/-- Herstein's square form on a 2-torsion-free ring. -/
theorem sq_of_jder (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (x : A) :
    D (x * x) = D x * x + x * D x := by
  have hd : D (x * x) + D (x * x) = (D x * x + x * D x) + (D x * x + x * D x) := by
    have h := hD x x
    simp only [jordan, map_add] at h
    linear_combination (norm := noncomm_ring) h
  have hz : (D (x * x) - (D x * x + x * D x)) + (D (x * x) - (D x * x + x * D x)) = 0 := by
    have h1 : (D (x * x) - (D x * x + x * D x)) + (D (x * x) - (D x * x + x * D x))
        = (D (x * x) + D (x * x))
          - ((D x * x + x * D x) + (D x * x + x * D x)) := by abel
    rw [h1, hd]; abel
  exact sub_eq_zero.mp (h2 _ hz)

/-- `w(a,a) = 0`. -/
theorem defect_self (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (x : A) :
    leibnizDefect D x x = 0 := by
  have h := sq_of_jder h2 hD x
  simp only [leibnizDefect]
  linear_combination (norm := noncomm_ring) h

/-! ## Proposition 2 of Brešar 1988 -/

/-- Proposition 2 (i). -/
theorem prop2_i {D : A →+ A} (hD : JDer D) (a b : A) :
    D (a * b + b * a) = D a * b + a * D b + D b * a + b * D a := by
  have h := hD a b
  simp only [jordan, map_add] at h
  rw [map_add, h]
  abel

/-- Proposition 2 (ii): `D(aba) = D(a)ba + aD(b)a + abD(a)`. -/
theorem prop2_ii (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (a b : A) :
    D (a * b * a) = D a * b * a + a * D b * a + a * b * D a := by
  have hsq : D (a * a) = D a * a + a * D a := sq_of_jder h2 hD a
  -- the two `∘`-products are related by adding `a b a + a b a`
  have hsplit : D (jordan (jordan a b) a) = D (jordan (a * a) b) + (D (a * b * a) + D (a * b * a)) := by
    rw [show jordan (jordan a b) a = jordan (a * a) b + (a * b * a + a * b * a) from by
      simp only [jordan]; noncomm_ring]
    rw [map_add, map_add]
  have h1 : D (jordan (jordan a b) a) =
      jordan (D (jordan a b)) a + jordan (jordan a b) (D a) := hD _ a
  have h2' : D (jordan a b) = jordan (D a) b + jordan a (D b) := hD a b
  have h3 : D (jordan (a * a) b) = jordan (D (a * a)) b + jordan (a * a) (D b) := hD _ b
  have hsub : jordan (D (jordan a b)) a + jordan (jordan a b) (D a)
      = (jordan (D (a * a)) b + jordan (a * a) (D b)) + (D (a * b * a) + D (a * b * a)) := by
    rw [← h1, ← h3]
    exact hsplit
  rw [h2', hsq] at hsub
  have hsub3 : (jordan (jordan (D a) b + jordan a (D b)) a + jordan (jordan a b) (D a))
      - (jordan (D a * a + a * D a) b + jordan (a * a) (D b))
      = D (a * b * a) + D (a * b * a) := by
    rw [hsub]; abel
  have key : D (a * b * a) + D (a * b * a)
      = (D a * b * a + a * D b * a + a * b * D a) + (D a * b * a + a * D b * a + a * b * D a) := by
    rw [← hsub3]
    simp only [jordan]
    noncomm_ring
  have hz : (D (a * b * a) - (D a * b * a + a * D b * a + a * b * D a))
      + (D (a * b * a) - (D a * b * a + a * D b * a + a * b * D a)) = 0 := by
    have h1' : (D (a * b * a) - (D a * b * a + a * D b * a + a * b * D a))
        + (D (a * b * a) - (D a * b * a + a * D b * a + a * b * D a))
        = (D (a * b * a) + D (a * b * a))
          - ((D a * b * a + a * D b * a + a * b * D a)
            + (D a * b * a + a * D b * a + a * b * D a)) := by abel
    rw [h1', key]; abel
  exact sub_eq_zero.mp (h2 _ hz)

/-- Proposition 2 (iii): the trilinear form, by polarisation of (ii). -/
theorem prop2_iii (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (a b c : A) :
    D (a * b * c + c * b * a)
      = D a * b * c + a * D b * c + a * b * D c
        + D c * b * a + c * D b * a + c * b * D a := by
  have h1 := prop2_ii h2 hD (a + c) b
  have ha := prop2_ii h2 hD a b
  have hc := prop2_ii h2 hD c b
  have hsplit : D ((a + c) * b * (a + c))
      = D (a * b * a) + (D (a * b * c) + (D (c * b * a) + D (c * b * c))) := by
    rw [show (a + c) * b * (a + c) = a * b * a + (a * b * c + (c * b * a + c * b * c)) from by
      noncomm_ring]
    rw [map_add, map_add, map_add]
  have key : D (a * b * a) + (D (a * b * c) + (D (c * b * a) + D (c * b * c)))
      = (D a + D c) * b * (a + c) + (a + c) * D b * (a + c) + (a + c) * b * (D a + D c) := by
    rw [← hsplit]; simpa only [map_add] using h1
  have h2' : D (a * b * c) + D (c * b * a)
      = ((D a + D c) * b * (a + c) + (a + c) * D b * (a + c) + (a + c) * b * (D a + D c))
        - ((D a * b * a + a * D b * a + a * b * D a) + (D c * b * c + c * D b * c + c * b * D c)) := by
    rw [← key, ha, hc]; abel
  rw [map_add, h2']
  noncomm_ring

/-- Axiom (3): the cocycle identity for the defect. -/
theorem defect_cocycle (D : A →+ A) (a b c : A) :
    leibnizDefect D (a * b) c + leibnizDefect D a b * c = leibnizDefect D a (b * c) + a * leibnizDefect D b c := by
  simp only [leibnizDefect]
  noncomm_ring

/-! ## Theorem 3 of Brešar 1988

`w(a,b) * x * [a,b] + [a,b] * x * w(a,b) = 0`. -/

theorem thm3 (h2 : TwoTorsionFree A) {D : A →+ A} (hD : JDer D) (a b x : A) :
    leibnizDefect D a b * x * (a * b - b * a) + (a * b - b * a) * x * leibnizDefect D a b = 0 := by
  have p1 := prop2_ii h2 hD a (b * x * b)
  have p2 := prop2_ii h2 hD b x
  have p3 := prop2_ii h2 hD b (a * x * a)
  have p4 := prop2_ii h2 hD a x
  have c1 : D ((a * b) * x * (b * a) + (b * a) * x * (a * b))
      = D (a * (b * x * b) * a) + D (b * (a * x * a) * b) := by
    rw [show (a * b) * x * (b * a) + (b * a) * x * (a * b)
        = a * (b * x * b) * a + b * (a * x * a) * b from by noncomm_ring, map_add]
  have hab : D (a * b) = D a * b + a * D b + leibnizDefect D a b := by
    simp only [leibnizDefect]; abel
  have hba : D (b * a) = D b * a + b * D a - leibnizDefect D a b := by
    have hs := defect_skew hD b a
    simp only [leibnizDefect] at hs ⊢
    exact eq_sub_iff_add_eq.mpr (by linear_combination (norm := NC) hs)
  set E1 : A := (D a * (b * x * b) * a
        + a * (D b * x * b + b * D x * b + b * x * D b) * a + a * (b * x * b) * D a)
      + (D b * (a * x * a) * b
        + b * (D a * x * a + a * D x * a + a * x * D a) * b + b * (a * x * a) * D b) with hE1
  set E2 : A := (D a * b + a * D b + leibnizDefect D a b) * x * (b * a) + (a * b) * D x * (b * a)
      + (a * b) * x * (D b * a + b * D a - leibnizDefect D a b)
      + (D b * a + b * D a - leibnizDefect D a b) * x * (a * b) + (b * a) * D x * (a * b)
      + (b * a) * x * (D a * b + a * D b + leibnizDefect D a b) with hE2
  have A1 : D ((a * b) * x * (b * a) + (b * a) * x * (a * b)) = E1 := by
    rw [hE1, c1, p1, p3, p2, p4]
    try noncomm_ring
  have A2 : D ((a * b) * x * (b * a) + (b * a) * x * (a * b)) = E2 := by
    rw [hE2, prop2_iii h2 hD (a * b) x (b * a), hab, hba]
    try noncomm_ring
  have hE : E1 = E2 := A1.symm.trans A2
  have hgoal : leibnizDefect D a b * x * (a * b - b * a) + (a * b - b * a) * x * leibnizDefect D a b
      = E1 - E2 := by
    rw [hE1, hE2]; noncomm_ring
  rw [hgoal, hE, sub_self]

/-! ## Lemma 4 of Brešar 1988 (with a correct proof)

If `p x q + q x p = 0` for all `x`, then `p x q = 0`: for arbitrary `m, n` the element
`u = p m q n p m q` satisfies `u = -u`, and then semiprimeness finishes. -/

theorem lemma4 (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {p q : A}
    (h : ∀ x : A, p * x * q + q * x * p = 0) (m : A) : p * m * q = 0 := by
  refine hs (p * m * q) (fun n => ?_)
  have hA : q * n * p = -(p * n * q) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h n
  have hB : p * (n * q * m) * q = -(q * (n * q * m) * p) :=
    eq_neg_iff_add_eq_zero.mpr (h (n * q * m))
  have hC : q * m * p = -(p * m * q) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h m
  have key : (p * m * q) * n * (p * m * q) = -((p * m * q) * n * (p * m * q)) := by
    calc (p * m * q) * n * (p * m * q)
        = p * m * (q * n * p) * m * q := by noncomm_ring
      _ = p * m * (-(p * n * q)) * m * q := by rw [hA]
      _ = -(p * m * (p * (n * q * m) * q)) := by noncomm_ring
      _ = p * m * (q * (n * q * m) * p) := by rw [hB]; try noncomm_ring
      _ = p * m * q * n * (q * m * p) := by noncomm_ring
      _ = -((p * m * q) * n * (p * m * q)) := by rw [hC]; try noncomm_ring
  exact h2 _ (eq_neg_iff_add_eq_zero.mp key)

/-- (5) of Brešar 1988: `w(a,b) * x * [a,b] = 0`. -/
theorem five (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b x : A) : leibnizDefect D a b * x * (a * b - b * a) = 0 :=
  lemma4 h2 hs (fun y => thm3 h2 hD a b y) x

/-- (6) of Brešar 1988: `w(a,b) * x * [a,c] = 0`. -/
theorem six (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b c x : A) : leibnizDefect D a b * x * (a * c - c * a) = 0 := by
  have h5 : ∀ y, leibnizDefect D a b * y * (a * b - b * a) = 0 := fun y => five h2 hs hD a b y
  have lin : leibnizDefect D a b * x * (a * c - c * a) + leibnizDefect D a c * x * (a * b - b * a) = 0 := by
    have h0 := five h2 hs hD a (b + c) x
    rw [defect_add_right, show a * (b + c) - (b + c) * a = (a * b - b * a) + (a * c - c * a) from by
      noncomm_ring] at h0
    have h1 := h5 x
    have h2' := five h2 hs hD a c x
    linear_combination (norm := NC) h0 - h1 - h2'
  refine hs (leibnizDefect D a b * x * (a * c - c * a)) (fun y => ?_)
  have hlt : leibnizDefect D a c * x * (a * b - b * a) = -(leibnizDefect D a b * x * (a * c - c * a)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact lin
  have e1 : (leibnizDefect D a b * x * (a * c - c * a)) * y * (leibnizDefect D a b * x * (a * c - c * a))
      = - ((leibnizDefect D a b * x * (a * c - c * a)) * y * (leibnizDefect D a c * x * (a * b - b * a))) := by
    rw [hlt]; noncomm_ring
  have e2 : (leibnizDefect D a b * x * (a * c - c * a)) * y * (leibnizDefect D a c * x * (a * b - b * a))
      = leibnizDefect D a b * (x * (a * c - c * a) * y * leibnizDefect D a c * x) * (a * b - b * a) := by
    noncomm_ring
  rw [e1, e2, h5 (x * (a * c - c * a) * y * leibnizDefect D a c * x)]
  simp

/-- (7) of Brešar 1988: `w(a,b) * x * [d,c] = 0`. -/
theorem seven (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b c d x : A) : leibnizDefect D a b * x * (d * c - c * d) = 0 := by
  have h6 : ∀ z, leibnizDefect D a b * z * (a * c - c * a) = 0 := fun z => six h2 hs hD a b c z
  have lin : leibnizDefect D a b * x * (d * c - c * d) + leibnizDefect D d b * x * (a * c - c * a) = 0 := by
    have h0 := six h2 hs hD (a + d) b c x
    rw [defect_add_left, show (a + d) * c - c * (a + d) = (a * c - c * a) + (d * c - c * d) from by
      noncomm_ring] at h0
    have h1 := h6 x
    have h2' := six h2 hs hD d b c x
    linear_combination (norm := NC) h0 - h1 - h2'
  refine hs (leibnizDefect D a b * x * (d * c - c * d)) (fun y => ?_)
  have hlt : leibnizDefect D d b * x * (a * c - c * a) = -(leibnizDefect D a b * x * (d * c - c * d)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact lin
  have e1 : (leibnizDefect D a b * x * (d * c - c * d)) * y * (leibnizDefect D a b * x * (d * c - c * d))
      = - ((leibnizDefect D a b * x * (d * c - c * d)) * y * (leibnizDefect D d b * x * (a * c - c * a))) := by
    rw [hlt]; noncomm_ring
  have e2 : (leibnizDefect D a b * x * (d * c - c * d)) * y * (leibnizDefect D d b * x * (a * c - c * a))
      = leibnizDefect D a b * (x * (d * c - c * d) * y * leibnizDefect D d b * x) * (a * c - c * a) := by
    noncomm_ring
  rw [e1, e2, h6 (x * (d * c - c * d) * y * leibnizDefect D d b * x)]
  simp

/-- (8) of Brešar 1988: `w(a,b) * [d,c] = 0`. -/
theorem eight (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b d c : A) : leibnizDefect D a b * (d * c - c * d) = 0 := by
  have h7 : ∀ x, leibnizDefect D a b * x * (d * c - c * d) = 0 := fun x => seven h2 hs hD a b c d x
  refine hs (leibnizDefect D a b * (d * c - c * d)) (fun y => ?_)
  have h := h7 ((d * c - c * d) * y * leibnizDefect D a b)
  have e : (leibnizDefect D a b * (d * c - c * d)) * y * (leibnizDefect D a b * (d * c - c * d))
      = leibnizDefect D a b * ((d * c - c * d) * y * leibnizDefect D a b) * (d * c - c * d) := by noncomm_ring
  rw [e, h]

/-- The defect `w(a,b)` is central. -/
theorem defect_central (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A}
    (hD : JDer D) (a b c : A) : leibnizDefect D a b * c = c * leibnizDefect D a b := by
  have h7 : ∀ x, leibnizDefect D a b * x * (leibnizDefect D a b * c - c * leibnizDefect D a b) = 0 :=
    fun x => seven h2 hs hD a b c (leibnizDefect D a b) x
  have hmain : leibnizDefect D a b * c - c * leibnizDefect D a b = 0 := by
    refine hs (leibnizDefect D a b * c - c * leibnizDefect D a b) (fun y => ?_)
    have e : (leibnizDefect D a b * c - c * leibnizDefect D a b) * y * (leibnizDefect D a b * c - c * leibnizDefect D a b)
        = leibnizDefect D a b * (c * y) * (leibnizDefect D a b * c - c * leibnizDefect D a b)
          - c * (leibnizDefect D a b * y * (leibnizDefect D a b * c - c * leibnizDefect D a b)) := by noncomm_ring
    rw [e, h7 (c * y), h7 y]
    simp
  exact sub_eq_zero.mp hmain

/-- (9) of Brešar 1988: `2 w² = w · D([a,b])`. -/
theorem nine (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b : A) :
    leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b
      = leibnizDefect D a b * D (a * b - b * a) := by
  have e0 : leibnizDefect D a b + leibnizDefect D a b
      = D (a * b - b * a) - (D a * b - b * D a) + (D b * a - a * D b) := by
    have hdw : leibnizDefect D a b + leibnizDefect D a b = leibnizDefect D a b - leibnizDefect D b a := by
      have h := defect_skew' hD b a
      rw [h]; abel
    rw [hdw]
    simp only [leibnizDefect, map_sub]
    abel
  have h8a : leibnizDefect D a b * (D a * b - b * D a) = 0 := eight h2 hs hD a b (D a) b
  have h8b : leibnizDefect D a b * (D b * a - a * D b) = 0 := eight h2 hs hD a b (D b) a
  have e2 := congrArg (fun t => leibnizDefect D a b * t) e0
  calc leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b
      = leibnizDefect D a b * (leibnizDefect D a b + leibnizDefect D a b) := by rw [mul_add]
    _ = leibnizDefect D a b * (D (a * b - b * a) - (D a * b - b * D a) + (D b * a - a * D b)) := e2
    _ = leibnizDefect D a b * D (a * b - b * a) - leibnizDefect D a b * (D a * b - b * D a)
          + leibnizDefect D a b * (D b * a - a * D b) := by rw [mul_add, mul_sub]
    _ = leibnizDefect D a b * D (a * b - b * a) := by rw [h8a, h8b, sub_zero, add_zero]

/-- (10) of Brešar 1988: `4 w² + D(w)[a,b] + [a,b]D(w) = 0`. -/
theorem ten (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b : A) :
    (leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b)
        + (leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b)
        + D (leibnizDefect D a b) * (a * b - b * a) + (a * b - b * a) * D (leibnizDefect D a b) = 0 := by
  have hwu : leibnizDefect D a b * (a * b - b * a) = 0 := eight h2 hs hD a b a b
  have huw : (a * b - b * a) * leibnizDefect D a b = 0 := by
    rw [← defect_central h2 hs hD a b (a * b - b * a)]
    exact hwu
  have h9 := nine h2 hs hD a b
  have hc : leibnizDefect D a b * D (a * b - b * a) = D (a * b - b * a) * leibnizDefect D a b :=
    defect_central h2 hs hD a b (D (a * b - b * a))
  have h4a : leibnizDefect D a b * D (a * b - b * a) + D (a * b - b * a) * leibnizDefect D a b
      = (leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b)
        + (leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b) := by
    rw [hc.symm, ← h9]
  have hJ : 0 = (D (leibnizDefect D a b) * (a * b - b * a) + (a * b - b * a) * D (leibnizDefect D a b))
      + (leibnizDefect D a b * D (a * b - b * a) + D (a * b - b * a) * leibnizDefect D a b) := by
    have h := hD (leibnizDefect D a b) (a * b - b * a)
    simp only [jordan] at h
    rw [hwu, huw, add_zero, map_zero] at h
    exact h
  rw [← h4a]
  simpa only [add_assoc, add_comm, add_left_comm] using hJ.symm

/-- (11) of Brešar 1988: `4 w³ = 0`. -/
theorem eleven (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b : A) :
    leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b
        + (leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b
          + leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b) = 0 := by
  have h10 := ten h2 hs hD a b
  have hwu : leibnizDefect D a b * (a * b - b * a) = 0 := eight h2 hs hD a b a b
  have hcDw : leibnizDefect D a b * D (leibnizDefect D a b) = D (leibnizDefect D a b) * leibnizDefect D a b :=
    defect_central h2 hs hD a b (D (leibnizDefect D a b))
  have k1 : leibnizDefect D a b * (D (leibnizDefect D a b) * (a * b - b * a)) = 0 := by
    rw [← mul_assoc, hcDw, mul_assoc, hwu, mul_zero]
  have k2 : leibnizDefect D a b * ((a * b - b * a) * D (leibnizDefect D a b)) = 0 := by
    rw [← mul_assoc, hwu, zero_mul]
  have hdist : leibnizDefect D a b * ((leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b)
        + (leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b)
        + D (leibnizDefect D a b) * (a * b - b * a) + (a * b - b * a) * D (leibnizDefect D a b))
      = (leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b + leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b
          + (leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b
            + leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b))
        + (leibnizDefect D a b * (D (leibnizDefect D a b) * (a * b - b * a))
          + leibnizDefect D a b * ((a * b - b * a) * D (leibnizDefect D a b))) := by noncomm_ring
  have hm := congrArg (fun t => leibnizDefect D a b * t) h10
  rw [mul_zero, hdist, k1, k2, add_zero, add_zero] at hm
  exact hm

/-- `w(a,b)³ = 0`. -/
theorem defect_cube (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A}
    (hD : JDer D) (a b : A) : leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b = 0 := by
  have h4 := eleven h2 hs hD a b
  exact h2 _ (h2 _ h4)

/-- (12) of Brešar 1988: the defect vanishes. -/
theorem twelve (h2 : TwoTorsionFree A) (hs : SemiprimeRing A) {D : A →+ A} (hD : JDer D)
    (a b : A) : leibnizDefect D a b = 0 := by
  have hcube : leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b = 0 := defect_cube h2 hs hD a b
  have hcw : ∀ c : A, leibnizDefect D a b * c = c * leibnizDefect D a b := fun c => defect_central h2 hs hD a b c
  have hw2 : leibnizDefect D a b * leibnizDefect D a b = 0 := by
    refine hs (leibnizDefect D a b * leibnizDefect D a b) (fun y => ?_)
    have hc2 : (leibnizDefect D a b * leibnizDefect D a b) * y = y * (leibnizDefect D a b * leibnizDefect D a b) := by
      calc (leibnizDefect D a b * leibnizDefect D a b) * y = leibnizDefect D a b * (leibnizDefect D a b * y) := by rw [mul_assoc]
        _ = leibnizDefect D a b * (y * leibnizDefect D a b) := by rw [hcw y]
        _ = (leibnizDefect D a b * y) * leibnizDefect D a b := by rw [← mul_assoc]
        _ = (y * leibnizDefect D a b) * leibnizDefect D a b := by rw [hcw y]
        _ = y * (leibnizDefect D a b * leibnizDefect D a b) := by rw [← mul_assoc]
    calc (leibnizDefect D a b * leibnizDefect D a b) * y * (leibnizDefect D a b * leibnizDefect D a b)
        = y * (leibnizDefect D a b * leibnizDefect D a b) * (leibnizDefect D a b * leibnizDefect D a b) := by rw [hc2]
      _ = y * (leibnizDefect D a b * leibnizDefect D a b * leibnizDefect D a b) * leibnizDefect D a b := by noncomm_ring
      _ = 0 := by rw [hcube, mul_zero, zero_mul]
  refine hs (leibnizDefect D a b) (fun y => ?_)
  calc leibnizDefect D a b * y * leibnizDefect D a b = (leibnizDefect D a b * y) * leibnizDefect D a b := rfl
    _ = (y * leibnizDefect D a b) * leibnizDefect D a b := by rw [hcw y]
    _ = y * (leibnizDefect D a b * leibnizDefect D a b) := by rw [← mul_assoc]
    _ = 0 := by rw [hw2, mul_zero]

/-! ## Brešar 1988, Theorem 1 -/

/-- **Brešar 1988, Theorem 1.**  Every Jordan derivation of a 2-torsion-free semiprime ring
is a derivation. -/
theorem jordan_derivation_eq_derivation (h2 : TwoTorsionFree A) (hs : SemiprimeRing A)
    {D : A →+ A} (hD : JDer D) : Der D := by
  intro x y
  have h := twelve h2 hs hD x y
  simp only [leibnizDefect, sub_sub] at h
  exact sub_eq_zero.mp h




/-! ## Brešar 1988, Theorem 1 discharges the hypothesis of the development -/

/-- **Brešar 1988, Theorem 1**, in the form in which the rest of the development
uses it: the `Prop` that `Background/JordanHerstein.lean` had left as a
hypothesis is now a theorem. -/
theorem bresar1988Theorem1_holds : Background.JordanHerstein.bresar1988Theorem1.{u} := by
  intro R _ h2 hs D hD
  exact jordan_derivation_eq_derivation h2 hs hD

/-- The same theorem in unfolded form, which is how other files consume it. -/
theorem bresar1988Theorem1_apply :
    ∀ (R : Type u) [Ring R], Background.JordanHerstein.TwoTorsionFree R →
      Background.JordanHerstein.SemiprimeRing R →
      ∀ D : R →+ R, Background.JordanHerstein.JDer D → Background.JordanHerstein.Der D :=
  bresar1988Theorem1_holds

/-! ## The two other cited theorems

`Background/JordanHerstein.lean` states three cited theorems as `Prop`s.  Two of
them are now closed from Brešar's, and the docstrings say exactly how, because
closing a *statement* is not the same as reproducing the historical argument:

* Cusack 1975, Corollary 5 is the *same* `Prop` as Brešar's Theorem 1 — the
  background file records that as `bresar_iff_cusack : ... ↔ ... := Iff.rfl` —
  so it closes with no work;
* Herstein 1957, Theorem 3.1 (prime rings with `2 ≠ 0`) follows because such a
  ring is 2-torsion-free (`twoTorsionFree_of_primeRing`) and semiprime
  (`prime_imp_semiprime`), which is precisely the generality Brešar proved.

Neither is Herstein's 1957 argument nor Cusack's 1975 one.  With these two in
hand the conditional consumers in `Background/JordanHerstein.lean`
(`der_of_jder_of_prime`, `der_of_hersteinJordan_of_prime`) can be applied with
`herstein1957Theorem31_holds` as their `H`, and none of the three cited theorems
remains a hypothesis anywhere in the development. -/

/-- **Cusack 1975, Corollary 5**, closed: the statement is Brešar's Theorem 1. -/
theorem cusack1975Corollary5_holds : Background.JordanHerstein.cusack1975Corollary5.{u} :=
  bresar1988Theorem1_holds

/-- **Herstein 1957, Theorem 3.1** (every Jordan derivation of a prime ring with
`2 ≠ 0` is a derivation), closed through Brešar's generalization: a prime ring
with `2 ≠ 0` is 2-torsion-free and semiprime. -/
theorem herstein1957Theorem31_holds : Background.JordanHerstein.herstein1957Theorem31.{u} := by
  intro R _ hprime h2 D hD
  exact bresar1988Theorem1_apply R
    (Background.JordanHerstein.twoTorsionFree_of_primeRing hprime h2)
    (Background.JordanHerstein.prime_imp_semiprime hprime) D hD

end Bresar1988

#print axioms Bresar1988.bresar1988Theorem1_holds
#print axioms Bresar1988.cusack1975Corollary5_holds
#print axioms Bresar1988.herstein1957Theorem31_holds
