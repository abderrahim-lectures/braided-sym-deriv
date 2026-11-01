/-
# The general identities of Sections 2 and 3, and the strengthened Theorem 4.1

The paper's results at their stated generality — arbitrary unital rings
(noncommutative, any dimension, any characteristic), additive maps, and
2-invertibility only where it is named.  Until v63.1 these identities were
kernel-checked only in an untracked review script; they are part of the
development now.

Conventions of the paper (Section 2, Section 3):
  x ·_σ y = μ(x⊗y) + μ(σ(x⊗y)),
  E_D(x,y) = D(xy) - D(x)y - x D(y)                                  (Definition 3.1)
  D is a braided-symmetric derivation for σ if D(x ·_σ y) = D(x) ·_σ y + x ·_σ D(y),
  σ_α(x⊗y) = α(y)⊗α(x); for an automorphism  x ·_{σ_α} y = xy + α(y)α(x) = xy + α(yx),
                        for an anti-automorphism x ·_{σ_α} y = xy + α(y)α(x) = xy + α(xy).

Contents:
* `residual_automorphism`, `residual_antiautomorphism`: the two residual
  identities displayed after the proof of Proposition 3.2, with no hypothesis
  relating `D` and `α`;
* `bsd_iff_automorphism`, `bsd_iff_antiautomorphism`: Proposition 3.2 (i) and
  (ii) as iff-statements; `derivation_iff_commutes`: Remark 3.3's first part;
* `cocycle`: the defect is a Hochschild 2-cocycle over an arbitrary ring
  (equation eq:cocycle);
* `thm41_core`: the strengthened Theorem 4.1 of the paper's proof (lines
  491–494) — over any ring, if `D` satisfies the twisted rule, its defect is
  symmetric and `A₋` has no nonzero square-zero element, then `D` is a
  derivation;
* the dictionary of Remark 2.4 with the hypotheses each row really needs
  (`bsd_id_iff_der`, `char_two_bsd_id_all`, `char_two_strict`, `bsd_neg_id_all`,
  `bsd_neg_tau_is_lie`);
* `sigmaAlpha`, `sigmaAlpha_involution` and `sigmaAlpha_involution_converse`:
  `σ_α = (α⊗α)∘τ` on `B ⊗[K] B`, an involution exactly when `α² = id` — the
  converse is the step the paper states without proof at line 291.
-/
import Mathlib

open scoped TensorProduct

namespace BSDGeneral

variable {A : Type*} [Ring A]

/-- Leibniz defect of a map `D` (paper, Definition 3.1). -/
def Ed (D : A → A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- Automorphism-type twisted product: `x ·_{σ_α} y = xy + α(y)α(x) = xy + α(yx)`. -/
def prodA (α : A → A) (x y : A) : A := x * y + α (y * x)

/-- Anti-automorphism-type twisted product: `x ·_{σ_α} y = xy + α(y)α(x) = xy + α(xy)`. -/
def prodB (α : A → A) (x y : A) : A := x * y + α (x * y)

section Auto

variable (α : A →+ A) (D : A →+ A)

/-- **Residual identity of Proposition 3.1, automorphism case** (paper, Section 3, displayed
right after the proof of Proposition 3.1), with no hypothesis relating `D` and `α`:
`D(x·y) - D(x)·y - x·D(y) = E_D(x,y) + α(E_D(y,x)) + (Dα - αD)(yx)`. -/
theorem residual_automorphism (hα : ∀ x y : A, α (x * y) = α x * α y) (x y : A) :
    D (prodA α x y) - prodA α (D x) y - prodA α x (D y)
      = Ed D x y + α (Ed D y x) + (D (α (y * x)) - α (D (y * x))) := by
  simp only [prodA, Ed, map_add, map_sub, hα]
  noncomm_ring

/-- **Proposition 3.1(i)**: if `D α = α D` then the `σ_α`-Leibniz rule is equivalent to
`E_D(x,y) + α(E_D(y,x)) = 0` for all `x, y`. -/
theorem bsd_iff_automorphism (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x)) :
    (∀ x y : A, D (prodA α x y) = prodA α (D x) y + prodA α x (D y))
      ↔ (∀ x y : A, Ed D x y + α (Ed D y x) = 0) := by
  have key : ∀ x y : A, D (α (y * x)) - α (D (y * x)) = 0 := by
    intro x y; rw [hDα]; abel
  constructor
  · intro h x y
    have hr := residual_automorphism α D hα x y
    rw [h x y, key x y, add_zero] at hr
    have h0 : prodA α (D x) y + prodA α x (D y) - prodA α (D x) y - prodA α x (D y) = 0 := by
      abel
    rw [h0] at hr
    exact hr.symm
  · intro h x y
    have hr := residual_automorphism α D hα x y
    rw [key x y, add_zero, h x y] at hr
    have h1 : D (prodA α x y) - prodA α (D x) y = prodA α x (D y) := sub_eq_zero.mp hr
    exact eq_add_of_sub_eq' h1

/-- **Remark 3.3**: a derivation `D` (`E_D = 0`) satisfies the `σ_α`-Leibniz rule iff it
commutes with `α`.  No 2-invertibility, no commutativity, no finite dimension. -/
theorem derivation_iff_commutes (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hder : ∀ x y : A, D (x * y) = D x * y + x * D y) :
    (∀ x y : A, D (prodA α x y) = prodA α (D x) y + prodA α x (D y))
      ↔ (∀ x : A, D (α x) = α (D x)) := by
  have hE : ∀ u v : A, Ed D u v = 0 := by
    intro u v; simp only [Ed, hder u v]; abel
  constructor
  · intro h x
    have hr := residual_automorphism α D hα 1 x
    rw [h 1 x, hE 1 x, hE x 1, zero_add] at hr
    have h0 : prodA α (D 1) x + prodA α 1 (D x) - prodA α (D 1) x - prodA α 1 (D x) = 0 := by
      abel
    rw [h0, map_zero, zero_add, mul_one] at hr
    exact sub_eq_zero.mp hr.symm
  · intro hcomm x y
    have hr := residual_automorphism α D hα x y
    have key : D (α (y * x)) - α (D (y * x)) = 0 := by rw [hcomm]; abel
    rw [hE x y, hE y x, map_zero, zero_add, key, add_zero] at hr
    have h1 : D (prodA α x y) - prodA α (D x) y = prodA α x (D y) := sub_eq_zero.mp hr
    exact eq_add_of_sub_eq' h1

/-- The defect is a Hochschild 2-cocycle (paper, equation (2.4)):
`aE(b,c) - E(ab,c) + E(a,bc) - E(a,b)c = 0`. -/
theorem cocycle (a b c : A) :
    a * Ed D b c - Ed D (a * b) c + Ed D a (b * c) - Ed D a b * c = 0 := by
  simp only [Ed]
  rw [show D (a * b * c) = D (a * (b * c)) from by rw [mul_assoc]]
  noncomm_ring

end Auto

section AntiAuto

variable (α : A →+ A) (D : A →+ A)

/-- **Residual identity, anti-automorphism case**: same shape with `α(E_D(x,y))` and `xy`. -/
theorem residual_antiautomorphism (hα : ∀ x y : A, α (x * y) = α y * α x) (x y : A) :
    D (prodB α x y) - prodB α (D x) y - prodB α x (D y)
      = Ed D x y + α (Ed D x y) + (D (α (x * y)) - α (D (x * y))) := by
  simp only [prodB, Ed, map_add, map_sub, hα]
  noncomm_ring

/-- **Proposition 3.1(ii)**: anti-automorphism case. -/
theorem bsd_iff_antiautomorphism (hα : ∀ x y : A, α (x * y) = α y * α x)
    (hDα : ∀ x : A, D (α x) = α (D x)) :
    (∀ x y : A, D (prodB α x y) = prodB α (D x) y + prodB α x (D y))
      ↔ (∀ x y : A, Ed D x y + α (Ed D x y) = 0) := by
  have key : ∀ x y : A, D (α (x * y)) - α (D (x * y)) = 0 := by
    intro x y; rw [hDα]; abel
  constructor
  · intro h x y
    have hr := residual_antiautomorphism α D hα x y
    rw [h x y, key x y, add_zero] at hr
    have h0 : prodB α (D x) y + prodB α x (D y) - prodB α (D x) y - prodB α x (D y) = 0 := by
      abel
    rw [h0] at hr
    exact hr.symm
  · intro h x y
    have hr := residual_antiautomorphism α D hα x y
    rw [key x y, add_zero, h x y] at hr
    have h1 : D (prodB α x y) - prodB α (D x) y = prodB α x (D y) := sub_eq_zero.mp hr
    exact eq_add_of_sub_eq' h1

end AntiAuto


/-! ## Theorem 4.1: the cocycle argument at the generality of the paper's stronger statement -/

theorem Ed_add_left (D : A →+ A) (a b c : A) :
    Ed D (a + b) c = Ed D a c + Ed D b c := by
  simp only [Ed, map_add, add_mul]
  abel

theorem Ed_add_right (D : A →+ A) (a b c : A) :
    Ed D a (b + c) = Ed D a b + Ed D a c := by
  simp only [Ed, map_add, mul_add]
  abel

theorem thm41_core (α : A →+ A) (D : A →+ A)
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hsym : ∀ x y : A, Ed D x y = Ed D y x)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hnil : ∀ z : A, α z = -z → z * z = 0 → z = 0) :
    ∀ x y : A, Ed D x y = 0 := by
  have hskew : ∀ x y : A, α (Ed D x y) = -(Ed D x y) := by
    intro x y
    have h := hE x y
    rw [hsym y x] at h
    have key : α (Ed D x y) + Ed D x y = 0 := by rw [add_comm]; exact h
    exact eq_neg_iff_add_eq_zero.mpr key
  have hfix_fix : ∀ x y : A, α x = x → α y = y → α (x * y) = x * y := by
    intro x y hx hy; rw [hα, hx, hy]
  have hfix_skew : ∀ x y : A, α x = x → α y = -y → α (x * y) = -(x * y) := by
    intro x y hx hy; rw [hα, hx, hy, mul_neg]
  have hskew_fix : ∀ x y : A, α x = -x → α y = y → α (x * y) = -(x * y) := by
    intro x y hx hy; rw [hα, hx, hy, neg_mul]
  have hskew_skew : ∀ x y : A, α x = -x → α y = -y → α (x * y) = x * y := by
    intro x y hx hy; rw [hα, hx, hy, neg_mul_neg]
  have hDfix : ∀ x : A, α x = x → α (D x) = D x := by
    intro x hx; rw [← hDα, hx]
  have hDskew : ∀ x : A, α x = -x → α (D x) = -(D x) := by
    intro x hx; rw [← hDα, hx, map_neg]
  -- (1) both arguments in the same part
  have hsame : ∀ x y : A, (α x = x ∧ α y = y) ∨ (α x = -x ∧ α y = -y) → Ed D x y = 0 := by
    intro x y hxy
    have hfix : α (Ed D x y) = Ed D x y := by
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hxy' : α (x * y) = x * y := hfix_fix x y hx hy
        simp only [Ed, map_sub, hα, hx, hy, hDfix x hx, hDfix y hy, hDfix (x * y) hxy']
      · have hxy' : α (x * y) = x * y := hskew_skew x y hx hy
        simp only [Ed, map_sub, hα, hx, hy, hDskew x hx, hDskew y hy, hDfix (x * y) hxy',
          neg_mul_neg]
    have hEq : Ed D x y = -(Ed D x y) := hfix.symm.trans (hskew x y)
    have hzz : Ed D x y + Ed D x y = 0 := add_eq_zero_iff_eq_neg.mpr hEq
    exact h2 _ hzz
  -- (2) cross pairs: the paper's two applications of the cocycle identity
  have hcross : ∀ x y : A, α x = x → α y = -y → Ed D x y = 0 := by
    intro x y hx hy
    set z := Ed D x y with hzdef
    have hz : α z = -z := hskew x y
    have c1 := cocycle D z x y
    have hzx : α (z * x) = -(z * x) := hskew_fix z x hz hx
    have hxy' : α (x * y) = -(x * y) := hfix_skew x y hx hy
    have e1 : Ed D (z * x) y = 0 := hsame _ _ (Or.inr ⟨hzx, hy⟩)
    have e2 : Ed D z (x * y) = 0 := hsame _ _ (Or.inr ⟨hz, hxy'⟩)
    rw [e1, e2] at c1
    have h1 : z * z = Ed D z x * y := by
      have : z * z - Ed D z x * y = 0 := by simpa using c1
      exact sub_eq_zero.mp this
    have c2 := cocycle D x z y
    have hzy : α (z * y) = z * y := hskew_skew z y hz hy
    have hxz : α (x * z) = -(x * z) := hfix_skew x z hx hz
    have e3 : Ed D z y = 0 := hsame _ _ (Or.inr ⟨hz, hy⟩)
    have e4 : Ed D (x * z) y = 0 := hsame _ _ (Or.inr ⟨hxz, hy⟩)
    have e5 : Ed D x (z * y) = 0 := hsame _ _ (Or.inl ⟨hx, hzy⟩)
    rw [e3, e4, e5] at c2
    have h2' : Ed D x z * y = 0 := by
      have hneg : -(Ed D x z * y) = 0 := by simpa using c2
      simpa using neg_eq_zero.mp hneg
    have hzz : z * z = 0 := by rw [h1, hsym z x, h2']
    exact hnil z hz hzz
  -- (3) bilinearity and the decomposition
  intro x y
  obtain ⟨xp, xs, hxp, hxs, hxeq⟩ := hdec x
  obtain ⟨yp, ys, hyp, hys, hyeq⟩ := hdec y
  rw [hxeq, hyeq, Ed_add_left, Ed_add_right, Ed_add_right]
  rw [hsame xp yp (Or.inl ⟨hxp, hyp⟩), hcross xp ys hxp hys,
      hsame xs ys (Or.inr ⟨hxs, hys⟩), hsym xs yp, hcross yp xs hyp hxs]
  abel


/-! ## Remark 2.4: the four-entry dictionary, with the hypotheses it really needs -/

variable {A : Type*} [Ring A]

/-- `σ = id`: the product is `2xy`; the `σ`-Leibniz rule is `2D(xy) = 2(D(x)y + xD(y))`,
so it is the Leibniz rule for the original product as soon as `2` is cancellable.
(The paper: "if char K ≠ 2 we divide by 2 and get BSDer_id(A) = Der(A)".) -/
theorem bsd_id_iff_der (D : A →+ A) (h2 : ∀ a : A, a + a = 0 → a = 0) :
    (∀ x y : A, D (x * y + x * y) = (D x * y + D x * y) + (x * D y + x * D y))
      ↔ (∀ x y : A, D (x * y) = D x * y + x * D y) := by
  constructor
  · intro h x y
    have hxy := h x y
    rw [map_add] at hxy
    -- hxy : D (x*y) + D (x*y) = (D x * y + D x * y) + (x * D y + x * D y)
    have hc : (D (x * y) - (D x * y + x * D y)) + (D (x * y) - (D x * y + x * D y)) = 0 := by
      have h0 : (D (x * y) - (D x * y + x * D y)) + (D (x * y) - (D x * y + x * D y))
          = (D (x * y) + D (x * y)) - ((D x * y + D x * y) + (x * D y + x * D y)) := by
        abel
      rw [h0, hxy]; abel
    exact sub_eq_zero.mp (h2 _ hc)
  · intro h x y
    rw [map_add, h x y]; abel

/-- `σ = id` in characteristic 2: the product is `2xy = 0`, so every additive map satisfies the
rule — but the identity map of `ZMod 2` is not a derivation, so `BSDer_id ⊋ Der`
(the paper: "If char K = 2 … this is larger than Der(A)"). -/
theorem char_two_bsd_id_all (D : A →+ A) (h2 : ∀ a : A, a + a = 0) (x y : A) :
    D (x * y + x * y) = (D x * y + D x * y) + (x * D y + x * D y) := by
  have h : x * y + x * y = 0 := h2 _
  have h' : D x * y + D x * y = 0 := h2 _
  have h'' : x * D y + x * D y = 0 := h2 _
  rw [h, h', h'', map_zero, add_zero]

/-- The witness for the strict inclusion in characteristic 2: the identity map of `ZMod 2`
is a `σ_id`-BSD (product zero) but not a derivation, since `1 * 1 = 1` while `1 * 1 + 1 * 1 = 0`. -/
theorem char_two_strict :
    ¬ (∀ x y : ZMod 2, (id x) * y + x * (id y) = x * y) := by
  intro h
  have := h 1 1
  simp at this

/-- `σ = τ`: the product is `xy + yx`, so the `σ`-Leibniz rule *is* the Jordan-derivation
condition (the paper: "BSDer_τ(A) = JDer(A) in every characteristic").  Definitional. -/
theorem bsd_tau_is_jordan (D : A →+ A) :
    (∀ x y : A, D (x * y + y * x) = (D x * y + y * D x) + (x * D y + D y * x))
      ↔ (∀ x y : A, D (x * y + y * x) = (D x * y + y * D x) + (x * D y + D y * x)) :=
  Iff.rfl

/-- `σ = -id`: the product is `xy - xy = 0`, so every additive map is a BSD
(the paper: "BSDer_{-id}(A) = End_K(A)"). -/
theorem bsd_neg_id_all (D : A →+ A) (x y : A) :
    D (x * y - x * y) = (D x * y - D x * y) + (x * D y - x * D y) := by
  simp

/-- `σ = -τ`: the product is `xy - yx = [x,y]`, so the `σ`-Leibniz rule *is* the
Lie-derivation condition.  Definitional. -/
theorem bsd_neg_tau_is_lie (D : A →+ A) :
    (∀ x y : A, D (x * y - y * x) = (D x * y - y * D x) + (x * D y - D y * x))
      ↔ (∀ x y : A, D (x * y - y * x) = (D x * y - y * D x) + (x * D y - D y * x)) :=
  Iff.rfl


variable {K : Type*} [CommRing K] {B : Type*} [Ring B] [Algebra K B]

/-- `σ_α(x⊗y) = α(y)⊗α(x)`, i.e. `σ_α = (α⊗α) ∘ τ`. -/
noncomputable def sigmaAlpha (α : B →ₐ[K] B) : B ⊗[K] B →ₗ[K] B ⊗[K] B :=
  (TensorProduct.map α α).comp (TensorProduct.comm K B B).toLinearMap

@[simp] theorem sigmaAlpha_tmul (α : B →ₐ[K] B) (x y : B) :
    sigmaAlpha α (x ⊗ₜ[K] y) = α y ⊗ₜ[K] α x := by
  simp [sigmaAlpha]

/-- `σ_α` is an involution of `A ⊗ A` when `α² = id` (paper, Section 3). -/
theorem sigmaAlpha_involution (α : B →ₐ[K] B) (hα : ∀ x, α (α x) = x) (u : B ⊗[K] B) :
    sigmaAlpha α (sigmaAlpha α u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp [map_add, hu, hv]
  | tmul x y => simp [hα]


/-- The converse of `sigmaAlpha_involution`: if `σ_α` is an involution of `A ⊗ A` then
`α² = id`.  This is the step the paper states without proof ("if α²⊗α² = id, then α² = λ id
with λ² = 1, and α²(1) = 1 gives λ = 1"); the proof is to evaluate at `x ⊗ 1` and multiply. -/
theorem sigmaAlpha_involution_converse (α : B →ₐ[K] B)
    (h : ∀ u : B ⊗[K] B, sigmaAlpha α (sigmaAlpha α u) = u) : ∀ x : B, α (α x) = x := by
  intro x
  have h1 := h (x ⊗ₜ[K] (1 : B))
  simp only [sigmaAlpha_tmul, map_one] at h1
  have h2 := congrArg (LinearMap.mul' K B) h1
  simpa [LinearMap.mul'_apply] using h2

end BSDGeneral

#print axioms BSDGeneral.residual_automorphism
#print axioms BSDGeneral.bsd_iff_automorphism
#print axioms BSDGeneral.derivation_iff_commutes
#print axioms BSDGeneral.cocycle
#print axioms BSDGeneral.residual_antiautomorphism
#print axioms BSDGeneral.bsd_iff_antiautomorphism
#print axioms BSDGeneral.bsd_id_iff_der
#print axioms BSDGeneral.char_two_bsd_id_all
#print axioms BSDGeneral.char_two_strict
#print axioms BSDGeneral.sigmaAlpha_involution
#print axioms BSDGeneral.sigmaAlpha_involution_converse
#print axioms BSDGeneral.thm41_core
