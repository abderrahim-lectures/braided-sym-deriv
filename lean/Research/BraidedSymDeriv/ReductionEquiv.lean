/-
# The three equivalent forms of Remark 4.6's remaining case

`Reduction.lean` proves that the general question of Remark 4.6 is *implied by*
the vanishing of the defect on `A₋ × A₋` (`thm41_of_odd_odd`).  This file proves
the converse direction, and with it the equivalence that Remark 4.6 states as of
v77:

  (i)   `D` is a derivation,
  (ii)  `E_D = 0` on the mixed pairs `A₊ × A₋`,
  (iii) `E_D = 0` on the odd–odd pairs `A₋ × A₋`,

are equivalent, for a reduced ring `A` with `2` invertible, an involutive
multiplicative `α` splitting `A = A₊ + A₋`, and `D` satisfying the `σ_α`-Leibniz
rule and commuting with `α`.

The new content is `thm41_of_mixed`: if the defect vanishes on the mixed pairs,
then it is antisymmetric everywhere — even–even pairs are free by Brešar's
theorem applied to `A₊`, odd–odd pairs because the defect is alternating there
(`Ed_self_eq_zero_of_skew`, using `E(x,x) ∈ A₊` by parity and `∈ A₋` by
Proposition 3.2(i)) — and an antisymmetric defect makes `D` a Jordan derivation,
which is a derivation by Brešar 1988, Theorem 1.

The paper prints this as a paragraph of Remark 4.6 (v77); no numbered result is
added.
-/
import Research.BraidedSymDeriv.Reduction

namespace BSDGeneral

variable {A : Type*} [Ring A]

section Equivalence

variable (α : A →+ A) (D : A →+ A)

/-- **The defect is alternating on the skew part.**  For `x ∈ A₋`, parity gives
`α (E(x,x)) = E(x,x)` and Proposition 3.2(i) at `(x,x)` gives
`α (E(x,x)) = -E(x,x)`; so `E(x,x) + E(x,x) = 0`, and `2` is cancellable. -/
theorem Ed_self_eq_zero_of_skew
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    {x : A} (hx : α x = -x) : Ed D x x = 0 := by
  have hfix : α (Ed D x x) = Ed D x x :=
    Ed_alpha_of_skew_skew α D hα hDα hx hx
  have h : Ed D x x + Ed D x x = 0 := by
    simpa only [hfix] using hE x x
  exact h2 _ h

/-- **Antisymmetry on the skew part.**  `E(x+y, x+y) = 0` for skew `x`, `y`,
because `x + y` is skew; expanding it by additivity and using `E(x,x) = E(y,y) = 0`
gives `E(x,y) + E(y,x) = 0`. -/
theorem Ed_add_swap_of_skew
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    {x y : A} (hx : α x = -x) (hy : α y = -y) :
    Ed D x y + Ed D y x = 0 := by
  have hxy : α (x + y) = -(x + y) := by
    rw [map_add, hx, hy]
    abel
  have h := Ed_self_eq_zero_of_skew α D hα hDα hE h2 hxy
  rw [Ed_add_left, Ed_add_right, Ed_add_right,
      Ed_self_eq_zero_of_skew α D hα hDα hE h2 hx,
      Ed_self_eq_zero_of_skew α D hα hDα hE h2 hy] at h
  simpa using h

/-- **The mixed case implies the conclusion.**  If `E` vanishes on `A₊ × A₋` then
it is antisymmetric everywhere: even–even pairs are free (Brešar on `A₊`),
mixed pairs vanish by hypothesis in one order and by Proposition 3.2(i) in the
other, and odd–odd pairs are alternating.  An antisymmetric defect makes `D` a
Jordan derivation, hence a derivation by Brešar's theorem. -/
theorem thm41_of_mixed
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hα2 : ∀ x : A, α (α x) = x)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0)
    (hmixed : ∀ x y : A, α x = x → α y = -y → Ed D x y = 0) :
    ∀ x y : A, Ed D x y = 0 := by
  have heven : ∀ x y : A, α x = x → α y = y → Ed D x y = 0 :=
    fun x y hx hy => Ed_eq_zero_of_fixed α D hα hα2 hDα hE h2 hred hx hy
  have hskew_fixed : ∀ x y : A, α x = -x → α y = y → Ed D x y = 0 := by
    intro x y hx hy
    have h := hE x y
    rw [hmixed y x hy hx, map_zero, add_zero] at h
    exact h
  have hanti : ∀ x y : A, Ed D x y + Ed D y x = 0 := by
    intro x y
    obtain ⟨xp, xq, hxp, hxq, hx⟩ := hdec x
    obtain ⟨yp, yq, hyp, hyq, hy⟩ := hdec y
    subst hx
    subst hy
    simp only [Ed_add_left, Ed_add_right]
    rw [heven xp yp hxp hyp, heven yp xp hyp hxp,
        hmixed xp yq hxp hyq, hskew_fixed yq xp hyq hxp,
        hskew_fixed xq yp hxq hyp, hmixed yp xq hyp hxq]
    simpa using Ed_add_swap_of_skew α D hα hDα hE h2 hxq hyq
  have hjder : Background.JordanHerstein.JDer D := by
    intro x y
    have h := hanti x y
    simp only [Ed] at h
    have h1 : (D (x * y) + D (y * x)) -
        ((D x * y + y * D x) + (x * D y + D y * x)) = 0 := by
      have e : (D (x * y) + D (y * x)) -
            ((D x * y + y * D x) + (x * D y + D y * x))
          = (D (x * y) - D x * y - x * D y) +
            (D (y * x) - D y * x - y * D x) := by
        abel
      rw [e, h]
    simp only [Background.JordanHerstein.jordan, map_add]
    exact sub_eq_zero.mp h1
  have hsemi : Background.JordanHerstein.SemiprimeRing A := by
    intro a ha
    exact hred a 2 (by norm_num) (by simpa [pow_two] using ha 1)
  have hDer : Background.JordanHerstein.Der D :=
    Bresar1988.jordan_derivation_eq_derivation h2 hsemi hjder
  intro x y
  have h := hDer x y
  simp only [Ed, h]
  abel

/-- **Remark 4.6, (i) ⟺ (ii).**  A map in `BSDer_{σ_α}(A)^α` is a derivation exactly
when its defect vanishes on the mixed pairs. -/
theorem der_iff_mixed
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hα2 : ∀ x : A, α (α x) = x)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0) :
    (∀ x y : A, Ed D x y = 0) ↔ (∀ x y : A, α x = x → α y = -y → Ed D x y = 0) := by
  constructor
  · intro h x y _ _; exact h x y
  · intro h; exact thm41_of_mixed α D hα hα2 hDα hE hdec h2 hred h

/-- **Remark 4.6, (i) ⟺ (iii).**  A map in `BSDer_{σ_α}(A)^α` is a derivation exactly
when its defect vanishes on the odd–odd pairs. -/
theorem der_iff_odd_odd
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hα2 : ∀ x : A, α (α x) = x)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0) :
    (∀ x y : A, Ed D x y = 0) ↔ (∀ x y : A, α x = -x → α y = -y → Ed D x y = 0) := by
  constructor
  · intro h x y _ _; exact h x y
  · intro h; exact thm41_of_odd_odd α D hα hα2 hDα hE hdec h2 hred h

/-- **Remark 4.6, (ii) ⟺ (iii).**  The two remaining cases are equivalent: a
counterexample must have a nonzero defect on the mixed pairs as well as on the
odd–odd pairs. -/
theorem mixed_iff_odd_odd
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hα2 : ∀ x : A, α (α x) = x)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0) :
    (∀ x y : A, α x = x → α y = -y → Ed D x y = 0) ↔
      (∀ x y : A, α x = -x → α y = -y → Ed D x y = 0) :=
  (der_iff_mixed α D hα hα2 hDα hE hdec h2 hred).symm.trans
    (der_iff_odd_odd α D hα hα2 hDα hE hdec h2 hred)

/-- **Remark 4.6 in the paper's own terms.**  For a reduced ring `A` with `2`
invertible, an involutive multiplicative `α` splitting `A = A₊ + A₋`, and a map
`D` satisfying the `σ_α`-Leibniz rule and commuting with `α` — that is,
`D ∈ BSDer_{σ_α}(A)^α` — the three conditions are equivalent: `D` is a
derivation, its defect vanishes on the mixed pairs, and its defect vanishes on
the odd–odd pairs.  The mixed hypothesis alone already gives the conclusion
(`thm41_of_mixed`), so the odd–odd condition is not a weaker target. -/
theorem bsd_iff_mixed_and_odd_odd
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hα2 : ∀ x : A, α (α x) = x)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hBSD : ∀ x y : A, D (prodA α x y) = prodA α (D x) y + prodA α x (D y))
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hred : ∀ z : A, ∀ n : ℕ, n ≠ 0 → z ^ n = 0 → z = 0) :
    (∀ x y : A, Ed D x y = 0) ↔
      ((∀ x y : A, α x = x → α y = -y → Ed D x y = 0) ∧
       (∀ x y : A, α x = -x → α y = -y → Ed D x y = 0)) := by
  have hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0 :=
    (bsd_iff_automorphism α D hα hDα).1 hBSD
  constructor
  · intro h
    exact ⟨fun x y _ _ => h x y, fun x y _ _ => h x y⟩
  · rintro ⟨hm, _⟩
    exact thm41_of_mixed α D hα hα2 hDα hE hdec h2 hred hm

/-- **The corrected role of the hypothesis `D α = α D`** (the paragraph after
Proposition 3.2).  If the two remaining terms `E(x,y) + α(E(y,x))` vanish, then
membership in the class is *equivalent* to commuting with `α`: granted their
vanishing, `D` satisfies the `σ_α`-Leibniz rule exactly when `D α = α D`.  This
is what the paper now says; the earlier wording ("the two terms vanish exactly
when `D` lies in the class and commutes with `α`") is false in one direction: a
derivation with `D α ≠ α D` has both terms zero and is not in the class. -/
theorem bsd_iff_comm_of_defect
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0) :
    (∀ x y : A, D (prodA α x y) = prodA α (D x) y + prodA α x (D y)) ↔
      (∀ x : A, D (α x) = α (D x)) := by
  constructor
  · intro hBSD x
    have hres := residual_automorphism α D hα 1 x
    have h0 : D (prodA α 1 x) - prodA α (D 1) x - prodA α 1 (D x) = 0 := by
      rw [hBSD 1 x]
      abel
    rw [hE 1 x, zero_add, h0, mul_one] at hres
    exact sub_eq_zero.mp hres.symm
  · intro hcomm
    exact (bsd_iff_automorphism α D hα hcomm).2 hE

end Equivalence

end BSDGeneral
