/-
# The open question of Remark 4.6, reduced to one nilpotency

Remark 4.6 of the paper leaves open whether Theorem 4.1 survives dropping
commutativity while keeping reducedness.  The proof of Theorem 4.1 uses
commutativity exactly once: it makes the Leibniz defect `E_D` symmetric.  This
file isolates what is left, over an arbitrary ring, so that the open question
has a single named hypothesis instead of a proof obligation buried in a
paragraph.

Notation as in `General.lean` (the paper's Section 2 and 3):

* `x ·_{σ_α} y = xy + α(y)α(x)`, and `D` is a `σ_α`-derivation if it satisfies
  the Leibniz rule for that product;
* `Ed D x y = D(xy) - D(x)y - xD(y)` is its defect;
* for `Dα = αD`, the rule is equivalent to `Ed D x y + α(Ed D y x) = 0`
  (`bsd_iff_automorphism`), which is the only form used below.

Contents:

* `Ea_eq_lie`: the antisymmetric part `Ea D x y = Ed D x y - Ed D y x` of the
  defect is the Lie-derivation defect, `D[x,y] - [Dx,y] - [x,Dy]`; so `Ea = 0`
  says exactly that `D` is a derivation for the commutator bracket, and
  `symm_iff_Ea_zero` that it says exactly that the defect is symmetric;
* `Ea_alpha_fixed`: for `Dα = αD` the antisymmetric part takes values in the
  fixed ring `A₊ = {a | α a = a}` — the paper's Proposition 3.2(i) read on the
  two halves of `E_D`;
* `EaNilpotent`: the one hypothesis the general theorem still needs, namely
  that `Ea D x y` be nilpotent for all `x`, `y`.  In a reduced algebra `A₊` is
  reduced, so this would give `Ea = 0`;
* `thm41_of_nilpotent_Ea`: **the reduction**.  Over any ring with `2`
  invertible, a `σ_α`-derivation commuting with `α` whose antisymmetric defect
  is nilpotent, on a reduced algebra with `A = A₊ + A₋`, is a derivation.  The
  proof is `thm41_core` (the paper's Theorem 4.1 with commutativity replaced by
  symmetry of the defect) fed with the symmetry that reducedness supplies;
* `thm41_of_sq_zero_Ea`: the same with `Ea² = 0`, the form the finite witness of
  Remark 4.6 exhibits at all sixteen basis pairs;
* `Ed_alpha_of_*`: the defect respects the `α`-grading `A = A₊ ⊕ A₋`, with the
  sign `(-1)^{i+j}` on the value at a pair of grades `i, j`;
* `Ea_eq_zero_of_fixed_skew`: **the mixed pairs are free** — at a pair with one
  argument fixed and the other skew, the twisted Leibniz rule *is* the
  Lie-derivation rule, and `Ea` vanishes there;
* `thm41_of_even_even_odd_odd`: **the sharpened reduction**.  The defect on
  `A₊ × A₊` vanishes by Brešar's theorem applied to the fixed subring (it is a
  Jordan derivation there, and `A₊` is reduced and 2-torsion-free); so the
  theorem follows from the vanishing of `E` on `A₋ × A₋` alone, where it is
  alternating with values in the reduced ring `A₊`.  That odd-odd case is the
  whole of the open problem.

What is *not* here, and is the actual open problem: whether `E` vanishes on
`A₋ × A₋` (equivalently, whether `EaNilpotent` holds) for every reduced `A`.
Nothing in this file assumes it beyond the named hypotheses of the theorems, and
`EaNilpotent` is not derivable from `bsd_iff_automorphism` alone — at the finite
witness of Remark 4.6 the defect is nonzero at every pair.
-/
import Research.BraidedSymDeriv.General

namespace BSDGeneral

variable {A : Type*} [Ring A]

/-- The antisymmetric part of the Leibniz defect: `Ea(x,y) = E(x,y) - E(y,x)`.
`Ea = 0` is the symmetry of the defect. -/
def Ea (D : A → A) (x y : A) : A := Ed D x y - Ed D y x

section Auto

variable (α : A →+ A) (D : A →+ A)

/-- **The antisymmetric defect is the Lie-derivation defect**:
`Ea(x,y) = D[x,y] - [Dx,y] - [x,Dy]`.  Hence `Ea = 0` if and only if `D` is a
derivation of the commutator bracket, which is the form in which the open
question is attacked. -/
theorem Ea_eq_lie (x y : A) :
    Ea D x y = D (x * y - y * x) - (D x * y - y * D x) - (x * D y - D y * x) := by
  simp only [Ea, Ed, map_sub]
  noncomm_ring

/-- **The defect respects the `α`-grading.**  `E(A_i, A_j) ⊆ A_{i+j}`, and `α`
acts on the value by `(-1)^{i+j}`.  First case: both arguments fixed. -/
theorem Ed_alpha_of_fixed (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hx : α x = x) (hy : α y = y) : α (Ed D x y) = Ed D x y := by
  simp only [Ed, map_sub, hα, ← hDα, hx, hy]

/-- Second case: the first argument fixed, the second skew — the value is skew. -/
theorem Ed_alpha_of_fixed_skew (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hx : α x = x) (hy : α y = -y) : α (Ed D x y) = - Ed D x y := by
  simp only [Ed, map_sub, hα, ← hDα, hx, hy, map_neg, mul_neg]
  noncomm_ring

/-- Third case: the first argument skew, the second fixed — the value is skew. -/
theorem Ed_alpha_of_skew_fixed (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hx : α x = -x) (hy : α y = y) : α (Ed D x y) = - Ed D x y := by
  simp only [Ed, map_sub, hα, ← hDα, hx, hy, map_neg, neg_mul]
  noncomm_ring

/-- Fourth case: both arguments skew — the value is fixed. -/
theorem Ed_alpha_of_skew_skew (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hx : α x = -x) (hy : α y = -y) : α (Ed D x y) = Ed D x y := by
  simp only [Ed, map_sub, hα, ← hDα, hx, hy, map_neg, mul_neg, neg_mul]
  noncomm_ring

/-- `Ea` is alternating. -/
theorem Ea_skew (x y : A) : Ea D x y = - Ea D y x := by
  simp only [Ea]
  abel

/-- Symmetry of the defect and vanishing of its antisymmetric part are the same
statement. -/
theorem symm_iff_Ea_zero :
    (∀ x y : A, Ed D x y = Ed D y x) ↔ (∀ x y : A, Ea D x y = 0) := by
  constructor
  · intro h x y
    simp only [Ea, h x y, sub_self]
  · intro h x y
    have h0 : Ea D x y = 0 := h x y
    simpa only [Ea, sub_eq_zero] using h0

/-- **Proposition 3.2(i) on the two halves of the defect.**  For `Dα = αD`, the
twisted Leibniz rule is `Ed D x y + α(Ed D y x) = 0` (`bsd_iff_automorphism`),
and that identity alone forces the antisymmetric part of the defect into the
fixed ring `A₊ = {a | α a = a}`: `α(Ea D x y) = Ea D x y`.  (The symmetric part
lands in `A₋`; in the commutative case the defect is symmetric, so it is all in
`A₋`, which is what the proof of Theorem 4.1 uses.) -/
theorem Ea_alpha_fixed
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0) (x y : A) :
    α (Ea D x y) = Ea D x y := by
  have h1 : α (Ed D x y) = - Ed D y x := eq_neg_of_add_eq_zero_right (hE y x)
  have h2 : α (Ed D y x) = - Ed D x y := eq_neg_of_add_eq_zero_right (hE x y)
  simp only [Ea, map_sub, h1, h2]
  abel

/-- The one hypothesis the general theorem still needs: the antisymmetric part of
the defect is nilpotent at every pair.  In a reduced algebra this forces it to
vanish, and `thm41_of_nilpotent_Ea` then gives the theorem. -/
def EaNilpotent (D : A → A) : Prop := ∀ x y : A, ∃ n : ℕ, n ≠ 0 ∧ (Ea D x y) ^ n = 0

/-- A nilpotent element of a reduced algebra is zero. -/
theorem eq_zero_of_pow_eq_zero (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0)
    {z : A} (h : ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 0) : z = 0 := by
  obtain ⟨n, hn, hzn⟩ := h
  exact hred z n hn hzn

/-- In a commutative ring the defect is symmetric, so its antisymmetric part
vanishes.  This is the only place commutativity is used in the proof of Theorem
4.1, and here it is visible. -/
theorem Ea_eq_zero_of_comm (hcomm : ∀ x y : A, x * y = y * x) (x y : A) :
    Ea D x y = 0 := by
  have h1 : D (x * y) = D (y * x) := by rw [hcomm x y]
  have h2 : D x * y = y * D x := hcomm _ _
  have h3 : x * D y = D y * x := hcomm _ _
  simp only [Ea, Ed, sub_eq_zero, h1, h2, h3]
  abel

/-- Consequently the nilpotency hypothesis of the reduction is free in the
commutative case: it holds with `n = 1`. -/
theorem EaNilpotent_of_comm (hcomm : ∀ x y : A, x * y = y * x) :
    EaNilpotent D := fun x y =>
  ⟨1, one_ne_zero, by rw [pow_one, Ea_eq_zero_of_comm D hcomm]⟩

/-- **The mixed pairs are free.**  If one argument is fixed and the other skew,
the antisymmetric part of the defect vanishes: `Ea` is fixed while `E(x,y)` and
`E(y,x)` are both skew, so `Ea(x,y) ∈ A₊ ∩ A₋ = 0` in a ring where `2` is
cancellable.  (The twisted Leibniz rule at a mixed pair *is* the Lie-derivation
rule, which is what this says.) -/
theorem Ea_eq_zero_of_fixed_skew (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hx : α x = x) (hy : α y = -y) : Ea D x y = 0 := by
  have hfix := Ea_alpha_fixed α D hE x y
  have hxy : α (Ed D x y) = - Ed D x y := Ed_alpha_of_fixed_skew α D hα hDα hx hy
  have hyx : α (Ed D y x) = - Ed D y x := Ed_alpha_of_skew_fixed α D hα hDα hy hx
  have hneg : α (Ea D x y) = - Ea D x y := by
    simp only [Ea, map_sub, hxy, hyx]
    abel
  exact h2 _ (add_eq_zero_iff_eq_neg.mpr (hfix.symm.trans hneg))

/-- `Ea` is additive in its first argument. -/
theorem Ea_add_left (a b c : A) : Ea D (a + b) c = Ea D a c + Ea D b c := by
  simp only [Ea, Ed_add_left, Ed_add_right]
  abel

/-- `Ea` is additive in its second argument. -/
theorem Ea_add_right (a b c : A) : Ea D a (b + c) = Ea D a b + Ea D a c := by
  simp only [Ea, Ed_add_right, Ed_add_left]
  abel

/-- **The sharpened reduction.**  Suppose the defect vanishes on `A₊ × A₊`
(supplied by Brešar's theorem applied to the fixed subring — `D` restricted to
`A₊` is a Jordan derivation there, and `A₊` is reduced and 2-torsion-free), and
on `A₋ × A₋` (the part nobody has proved).  Then the antisymmetric part of the
defect vanishes, and `D` is a derivation.

So the general question of Remark 4.6 is *exactly* the odd-odd case: `E` on
`A₋ × A₋`, where it is alternating with values in the reduced ring `A₊`.  The
mixed pairs are free (`Ea_eq_zero_of_fixed_skew`) and in that case only the
symmetric part of `E` can survive. -/
theorem thm41_of_even_even_odd_odd
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0)
    (heven : ∀ x y : A, α x = x → α y = y → Ed D x y = 0)
    (hodd : ∀ x y : A, α x = -x → α y = -y → Ed D x y = 0) :
    ∀ x y : A, Ed D x y = 0 := by
  have hEa : ∀ x y : A, Ea D x y = 0 := by
    intro x y
    obtain ⟨xp, xq, hxp, hxq, hx⟩ := hdec x
    obtain ⟨yp, yq, hyp, hyq, hy⟩ := hdec y
    subst hx; subst hy
    simp only [Ea_add_left, Ea_add_right]
    have h1 : Ea D xp yp = 0 := by
      simp only [Ea, heven xp yp hxp hyp, heven yp xp hyp hxp, sub_self]
    have h2' : Ea D xp yq = 0 := Ea_eq_zero_of_fixed_skew α D hα hDα hE h2 hxp hyq
    have h3 : Ea D xq yp = 0 := by
      rw [Ea_skew D xq yp, Ea_eq_zero_of_fixed_skew α D hα hDα hE h2 hyp hxq, neg_zero]
    have h4 : Ea D xq yq = 0 := by
      simp only [Ea, hodd xq yq hxq hyq, hodd yq xq hyq hxq, sub_self]
    rw [h1, h2', h3, h4]
    abel
  have hsym : ∀ x y : A, Ed D x y = Ed D y x := (symm_iff_Ea_zero D).mpr hEa
  have hnil' : ∀ z : A, α z = -z → z * z = 0 → z = 0 := by
    intro z _ hzz
    exact hred z 2 (by norm_num) (by rwa [pow_two])
  exact thm41_core α D hα hDα hE hsym hdec h2 hnil'

/-- **The reduction of the open question.**  Let `A` be a ring with `2`
invertible, `α` an involutive automorphism (only multiplicativity and the
decomposition `A = A₊ + A₋` are used), and `D` a `σ_α`-derivation commuting with
`α`.  If `A` is reduced and the antisymmetric part of the defect of `D` is
nilpotent, then `D` is a derivation — with no commutativity hypothesis.

So the general question "does Theorem 4.1 survive dropping commutativity while
keeping reducedness?" is exactly the question whether `EaNilpotent` holds. -/
theorem thm41_of_nilpotent_Ea
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0)
    (hnil : EaNilpotent D) :
    ∀ x y : A, Ed D x y = 0 := by
  have hsym : ∀ x y : A, Ed D x y = Ed D y x := by
    refine (symm_iff_Ea_zero D).mpr (fun x y => ?_)
    exact eq_zero_of_pow_eq_zero hred (hnil x y)
  have hnil' : ∀ z : A, α z = -z → z * z = 0 → z = 0 := by
    intro z _ hzz
    exact hred z 2 (by norm_num) (by rwa [pow_two])
  exact thm41_core α D hα hDα hE hsym hdec h2 hnil'

/-- The same reduction with `Ea² = 0` in place of nilpotency — the form the
finite witness of Remark 4.6 exhibits at all sixteen basis pairs. -/
theorem thm41_of_sq_zero_Ea
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0)
    (hEa2 : ∀ x y : A, Ea D x y * Ea D x y = 0) :
    ∀ x y : A, Ed D x y = 0 := by
  refine thm41_of_nilpotent_Ea α D hα hDα hE hdec h2 hred (fun x y => ⟨2, by norm_num, ?_⟩)
  rw [pow_two]
  exact hEa2 x y

end Auto

end BSDGeneral
