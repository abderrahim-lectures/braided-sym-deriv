/-
# v73 findings F1 and F2, formalized

**F1.**  Remark 4.6 prints the dimension statements at the quaternions as
`dim BSDer_{σ_α}(ℍ)^α = dim Der(ℍ)^α = 1` and `dim BSDer_{σ_α}(ℍ) = 1 < 3 = dim Der(ℍ)`.
Those values hold for the conjugations by pure imaginary units, not for
`α = id`, where all three dimensions are `3` (Theorem 3.4); v73 says so in the
text.  This file proves the conjugation case for the model conjugation, the one
by `i`:  with `α x = -(i x i)` and `x·y = xy + α(y)α(x)`, a linear `D` that
commutes with `α` and satisfies the twisted Leibniz rule is a scalar multiple of
the inner derivation `ad_i(x) = i x - x i`, and `ad_i` itself is such a `D` and
is nonzero (`class_is_line`, `adI_ne_zero`).  So the class is exactly the line
spanned by `ad_i`, which is the printed dimension `1`.  The passage to a general
pure imaginary unit `q'` is the conjugacy identity below: for any `q'` with
`q' * q' = -1` the element `u = 1 - q' i` satisfies `u * i = q' * u`, so `q'` is
conjugate to `i` by `u`, and conjugation transports the class.

**F2.**  The paper defines `reduced` for commutative algebras and then uses it
for algebras that are not commutative (Remark 4.6).  v73 defines it for any
algebra.  The mathematical content of the widening is `reduced_imp_semiprime`
below: a reduced ring, commutative or not, is semiprime in Bresar's sense —
which is the implication the proof of Remark 4.6's reduction uses.

Nothing here uses `sorry` or `native_decide`.
-/
import Mathlib
import Background.JordanHerstein

namespace QuaternionConjug

open Quaternion

abbrev H := Quaternion ℝ

def qi : H := ⟨0, 1, 0, 0⟩
def qj : H := ⟨0, 0, 1, 0⟩
def qk : H := ⟨0, 0, 0, 1⟩

@[simp] theorem qi_qi : qi * qi = -1 := by ext <;> simp [qi]
@[simp] theorem qi_qj : qi * qj = qk := by ext <;> simp [qi, qj, qk]
@[simp] theorem qj_qi : qj * qi = -qk := by ext <;> simp [qi, qj, qk]
@[simp] theorem qj_qj : qj * qj = -1 := by ext <;> simp [qj]
@[simp] theorem qk_qk : qk * qk = -1 := by ext <;> simp [qk]
@[simp] theorem qk_qi : qk * qi = qj := by ext <;> simp [qi, qj, qk]
@[simp] theorem qi_qk : qi * qk = -qj := by ext <;> simp [qi, qj, qk]
@[simp] theorem qj_qk : qj * qk = qi := by ext <;> simp [qi, qj, qk]
@[simp] theorem qk_qj : qk * qj = -qi := by ext <;> simp [qi, qj, qk]

def conjI (x : H) : H := -(qi * x * qi)

@[simp] theorem conjI_mk (a b c d : ℝ) : conjI ⟨a,b,c,d⟩ = ⟨a, b, -c, -d⟩ := by
  ext <;> simp [conjI, qi]

@[simp] theorem conjI_one : conjI 1 = 1 := by ext <;> simp [conjI, qi]
@[simp] theorem conjI_qi : conjI qi = qi := by ext <;> simp [conjI, qi]
@[simp] theorem conjI_qj : conjI qj = -qj := by ext <;> simp [conjI, qi, qj]
@[simp] theorem conjI_qk : conjI qk = -qk := by ext <;> simp [conjI, qi, qk]

theorem conjI_invol (x : H) : conjI (conjI x) = x := by
  simp only [conjI]
  have h1 : -(qi * (-(qi * x * qi)) * qi) = qi * (qi * x * qi) * qi := by noncomm_ring
  rw [h1]
  have h2 : qi * (qi * x * qi) * qi = (qi * qi) * x * (qi * qi) := by noncomm_ring
  rw [h2, qi_qi]
  noncomm_ring

theorem conjI_mul (x y : H) : conjI (x * y) = conjI x * conjI y := by
  simp only [conjI]
  have h : (qi * x * qi) * (qi * y * qi) = -(qi * (x * y) * qi) := by
    have h1 : qi * x * qi * (qi * y * qi) = qi * x * (qi * qi) * y * qi := by noncomm_ring
    rw [h1, qi_qi]; noncomm_ring
  rw [neg_mul_neg, h]

def prod (x y : H) : H := x * y + conjI y * conjI x

theorem prod_one_left (x : H) : prod 1 x = x + conjI x := by simp [prod]
theorem prod_one_right (x : H) : prod x 1 = x + conjI x := by simp [prod]
theorem prod_qi_qi : prod qi qi = -2 := by simp [prod]; norm_num
theorem prod_qj_qj : prod qj qj = -2 := by simp [prod]; norm_num
theorem prod_qk_qk : prod qk qk = -2 := by simp [prod]; norm_num
theorem prod_qj_qk : prod qj qk = 0 := by simp [prod]
theorem prod_qk_qj : prod qk qj = 0 := by simp [prod]
theorem prod_qi_qj : prod qi qj = qk + qk := by simp [prod]
theorem prod_qi_qk : prod qi qk = -(qj + qj) := by simp [prod]




variable (D : H →ₗ[ℝ] H)
variable (hDα : ∀ x, D (conjI x) = conjI (D x))
variable (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y))

-- conjI fixes a = D 1 and b = D qi
include hDα in
theorem fix_one : conjI (D 1) = D 1 := by rw [← hDα, conjI_one]
include hDα in
theorem fix_qi : conjI (D qi) = D qi := by rw [← hDα, conjI_qi]
include hDα in
theorem skew_qj : conjI (D qj) = -(D qj) := by rw [← hDα, conjI_qj, map_neg]
include hDα in
theorem skew_qk : conjI (D qk) = -(D qk) := by rw [← hDα, conjI_qk, map_neg]

include hD in
theorem a_zero : D 1 = 0 := by
  have h := hD 1 1
  rw [prod_one_left, prod_one_right] at h
  simp only [prod, conjI_one] at h
  -- h : D (1 + 1) = (D 1 + conjI (D 1)) + (D 1 + conjI (D 1))
  rw [map_add] at h
  have key : conjI (D 1) + conjI (D 1) = 0 := by
    have h' := congrArg (fun z => z - (D 1 + D 1)) h
    have : (0:H) = conjI (D 1) + conjI (D 1) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    exact this.symm
  have hz : conjI (D 1) = 0 := by
    have h2 : (2:ℝ) • conjI (D 1) = 0 := by rw [two_smul ℝ]; exact key
    simpa using h2
  have hinv : D 1 = conjI (conjI (D 1)) := (conjI_invol (D 1)).symm
  rw [hinv, hz]
  simp [conjI]



theorem mk_eta (x : H) : (⟨x.re, x.imI, x.imJ, x.imK⟩ : H) = x := by ext <;> simp

-- generic: if conjI b = b then b = re + imI*i
theorem fixed_form (b : H) (h : conjI b = b) : b = ⟨b.re, b.imI, 0, 0⟩ := by
  have hb : b = ⟨b.re, b.imI, b.imJ, b.imK⟩ := (mk_eta b).symm
  rw [hb] at h
  simp only [conjI_mk] at h
  have hJ : b.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h
    simp at this; linarith
  have hK : b.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h
    simp at this; linarith
  rw [hb, hJ, hK]

-- generic: if conjI b = -b then b = imJ*j + imK*k
theorem skew_form (b : H) (h : conjI b = -b) : b = ⟨0, 0, b.imJ, b.imK⟩ := by
  have hb : b = ⟨b.re, b.imI, b.imJ, b.imK⟩ := (mk_eta b).symm
  rw [hb] at h
  simp only [conjI_mk, QuaternionAlgebra.neg_mk] at h
  have hR : b.re = 0 := by
    have := congrArg QuaternionAlgebra.re h; simp at this; linarith
  have hI : b.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h; simp at this; linarith
  rw [hb, hR, hI]

def adI : H →ₗ[ℝ] H where
  toFun x := qi * x - x * qi
  map_add' x y := by simp only [mul_add, add_mul, sub_eq_add_neg]; abel
  map_smul' c x := by simp only [mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply]


theorem fix_one' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x)) :
    conjI (D 1) = D 1 := by rw [← hDα 1, conjI_one]

theorem fix_qi' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x)) :
    conjI (D qi) = D qi := by rw [← hDα qi, conjI_qi]

theorem skew_qj' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x)) :
    conjI (D qj) = -(D qj) := by rw [← hDα qj, conjI_qj, map_neg]

theorem skew_qk' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x)) :
    conjI (D qk) = -(D qk) := by rw [← hDα qk, conjI_qk, map_neg]

theorem a_zero' (D : H →ₗ[ℝ] H) (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    D 1 = 0 := by
  have h := hD 1 1
  rw [prod_one_left, prod_one_right] at h
  simp only [prod, conjI_one, mul_one, one_mul] at h
  rw [map_add] at h
  have key : conjI (D 1) + conjI (D 1) = 0 := by
    have h' := congrArg (fun z => z - (D 1 + D 1)) h
    have h2 : (0:H) = conjI (D 1) + conjI (D 1) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    exact h2.symm
  have hz : conjI (D 1) = 0 := by
    have h2 : (2:ℝ) • conjI (D 1) = 0 := by rw [two_smul ℝ]; exact key
    simpa using h2
  have hinv : D 1 = conjI (conjI (D 1)) := (conjI_invol (D 1)).symm
  rw [hinv, hz]
  simp [conjI]

theorem b_zero' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) : D qi = 0 := by
  have hfix : conjI (D qi) = D qi := fix_qi' D hDα
  have h := hD qi qi
  rw [prod_qi_qi] at h
  have h2 : D (-2 : H) = 0 := by
    have hh : (-2 : H) = -((1:H) + (1:H)) := by norm_num
    rw [hh, map_neg, map_add, a_zero' D hD]; simp
  rw [h2] at h
  have hexp : prod (D qi) qi + prod qi (D qi)
      = ((D qi) * qi + qi * (D qi)) + ((D qi) * qi + qi * (D qi)) := by
    simp only [prod, conjI_qi, hfix]
    abel
  rw [hexp] at h
  have hsum : (D qi) * qi + qi * (D qi) = 0 := by
    have h3 : (2:ℝ) • ((D qi) * qi + qi * (D qi)) = 0 := by
      rw [two_smul ℝ]; exact h.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  have hform : (D qi) = ⟨(D qi).re, (D qi).imI, 0, 0⟩ := fixed_form _ hfix
  rw [hform] at hsum
  rw [show ((⟨(D qi).re, (D qi).imI, 0, 0⟩ : H) * qi + qi * ⟨(D qi).re, (D qi).imI, 0, 0⟩)
        = ⟨-2 * (D qi).imI, 2 * (D qi).re, 0, 0⟩ from by ext <;> simp [qi] <;> ring] at hsum
  have hr : (D qi).re = 0 := by
    have := congrArg QuaternionAlgebra.imI hsum; simpa using this
  have hs : (D qi).imI = 0 := by
    have := congrArg QuaternionAlgebra.re hsum; simpa using this
  rw [hform, hr, hs]
  rfl



theorem c_form (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    ∃ t : ℝ, D qj = t • qk := by
  have hskew : conjI (D qj) = -(D qj) := skew_qj' D hDα
  have h := hD qj qj
  rw [prod_qj_qj] at h
  have h2 : D (-2 : H) = 0 := by
    have hh : (-2 : H) = -((1:H) + (1:H)) := by norm_num
    rw [hh, map_neg, map_add, a_zero' D hD]; simp
  rw [h2] at h
  have hexp : prod (D qj) qj + prod qj (D qj)
      = ((D qj) * qj + qj * (D qj)) + ((D qj) * qj + qj * (D qj)) := by
    simp only [prod, conjI_qj, hskew, neg_mul_neg]
    abel
  rw [hexp] at h
  have hsum : (D qj) * qj + qj * (D qj) = 0 := by
    have h3 : (2:ℝ) • ((D qj) * qj + qj * (D qj)) = 0 := by
      rw [two_smul ℝ]; exact h.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  have hform : (D qj) = ⟨0, 0, (D qj).imJ, (D qj).imK⟩ := skew_form _ hskew
  rw [hform] at hsum
  rw [show ((⟨0, 0, (D qj).imJ, (D qj).imK⟩ : H) * qj + qj * ⟨0, 0, (D qj).imJ, (D qj).imK⟩)
        = ⟨-2 * (D qj).imJ, 0, 0, 0⟩ from by ext <;> simp [qi, qj, qk] <;> ring] at hsum
  have hp : (D qj).imJ = 0 := by
    have := congrArg QuaternionAlgebra.re hsum; simpa using this
  refine ⟨(D qj).imK, ?_⟩
  rw [hform, hp]
  ext <;> simp [qk]

theorem d_form (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    ∃ s : ℝ, D qk = s • qj := by
  have hskew : conjI (D qk) = -(D qk) := skew_qk' D hDα
  have h := hD qk qk
  rw [prod_qk_qk] at h
  have h2 : D (-2 : H) = 0 := by
    have hh : (-2 : H) = -((1:H) + (1:H)) := by norm_num
    rw [hh, map_neg, map_add, a_zero' D hD]; simp
  rw [h2] at h
  have hexp : prod (D qk) qk + prod qk (D qk)
      = ((D qk) * qk + qk * (D qk)) + ((D qk) * qk + qk * (D qk)) := by
    simp only [prod, conjI_qk, hskew, neg_mul_neg]
    abel
  rw [hexp] at h
  have hsum : (D qk) * qk + qk * (D qk) = 0 := by
    have h3 : (2:ℝ) • ((D qk) * qk + qk * (D qk)) = 0 := by
      rw [two_smul ℝ]; exact h.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  have hform : (D qk) = ⟨0, 0, (D qk).imJ, (D qk).imK⟩ := skew_form _ hskew
  rw [hform] at hsum
  rw [show ((⟨0, 0, (D qk).imJ, (D qk).imK⟩ : H) * qk + qk * ⟨0, 0, (D qk).imJ, (D qk).imK⟩)
        = ⟨-2 * (D qk).imK, 0, 0, 0⟩ from by ext <;> simp [qi, qj, qk] <;> ring] at hsum
  have hq : (D qk).imK = 0 := by
    have := congrArg QuaternionAlgebra.re hsum; simpa using this
  refine ⟨(D qk).imJ, ?_⟩
  rw [hform, hq]
  ext <;> simp [qj]


theorem adI_one : adI (1:H) = 0 := by simp [adI]
theorem adI_qi : adI qi = 0 := by simp [adI]
theorem adI_qj : adI qj = qk + qk := by simp [adI, qi_qj, qj_qi]
theorem adI_qk : adI qk = -(qj + qj) := by simp [adI, qi_qk, qk_qi]; abel

theorem c_form' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    ∃ t : ℝ, D qj = ⟨0, 0, 0, t⟩ := by
  obtain ⟨t, ht⟩ := c_form D hDα hD
  exact ⟨t, by rw [ht]; ext <;> simp [qk]⟩

theorem d_form' (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    ∃ s : ℝ, D qk = ⟨0, 0, s, 0⟩ := by
  obtain ⟨s, hs⟩ := d_form D hDα hD
  exact ⟨s, by rw [hs]; ext <;> simp [qj]⟩

theorem ts_relation (D : H →ₗ[ℝ] H) (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y))
    {t s : ℝ} (ht : D qj = ⟨0,0,0,t⟩) (hs : D qk = ⟨0,0,s,0⟩) : s = -t := by
  have h := hD qj qk
  rw [prod_qj_qk, map_zero, ht, hs] at h
  have h1 : prod (⟨0,0,0,t⟩ : H) qk = ⟨-2*t, 0, 0, 0⟩ := by
    simp only [prod, conjI_qk, conjI_mk, neg_mul_neg]
    ext <;> simp [qi, qj, qk] <;> ring
  have h2 : prod qj (⟨0,0,s,0⟩ : H) = ⟨-2*s, 0, 0, 0⟩ := by
    simp only [prod, conjI_qj, conjI_mk, neg_mul_neg]
    ext <;> simp [qi, qj, qk] <;> ring
  rw [h1, h2] at h
  have := congrArg QuaternionAlgebra.re h
  simp at this
  linarith

theorem main (D : H →ₗ[ℝ] H) (hDα : ∀ x, D (conjI x) = conjI (D x))
    (hD : ∀ x y, D (prod x y) = prod (D x) y + prod x (D y)) :
    ∃ c : ℝ, D = c • adI := by
  obtain ⟨t, ht⟩ := c_form' D hDα hD
  obtain ⟨s, hs⟩ := d_form' D hDα hD
  have hst : s = -t := ts_relation D hD ht hs
  refine ⟨t/2, ?_⟩
  apply LinearMap.ext
  intro x
  have hx : x = x.re • (1:H) + x.imI • qi + x.imJ • qj + x.imK • qk := by
    rw [← mk_eta x]
    ext <;> simp [qi, qj, qk]
  have ha := a_zero' D hD
  have hb := b_zero' D hDα hD
  rw [hx, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, ha, hb, ht, hs,
      LinearMap.smul_apply]
  rw [hst]
  -- now both sides in coordinates
  simp only [smul_zero, zero_add]
  rw [show (t / 2) • adI (x.re • (1:H) + x.imI • qi + x.imJ • qj + x.imK • qk)
        = (t/2) • (x.imJ • (qk + qk) + x.imK • (-(qj + qj))) from by
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, adI_one, adI_qi,
        adI_qj, adI_qk]; simp]
  ext <;> simp [qi, qj, qk] <;> ring


theorem conjI_smul (c : ℝ) (x : H) : conjI (c • x) = c • conjI x := by
  ext <;> simp [conjI, qi]

theorem conjI_zero : conjI (0:H) = 0 := by simp [conjI]

theorem prod_smul_left (c : ℝ) (x y : H) : prod (c • x) y = c • prod x y := by
  simp only [prod, smul_add, smul_mul_assoc, mul_smul_comm, conjI_smul]

theorem prod_smul_right (c : ℝ) (x y : H) : prod x (c • y) = c • prod x y := by
  simp only [prod, smul_add, smul_mul_assoc, mul_smul_comm, conjI_smul]

theorem adI_deriv (x y : H) : adI (x * y) = adI x * y + x * adI y := by
  ext <;> simp [adI, qi] <;> ring

theorem adI_comm (x : H) : conjI (adI x) = adI (conjI x) := by
  ext <;> simp [adI, conjI, qi] <;> ring

theorem adI_mem (x y : H) : adI (prod x y) = prod (adI x) y + prod x (adI y) := by
  simp only [prod, map_add, adI_deriv, adI_comm]
  abel

theorem adI_ne_zero : (adI : H →ₗ[ℝ] H) ≠ 0 := by
  intro h
  have h' := congrArg (fun f => f qj) h
  simp only [LinearMap.zero_apply, adI_qj] at h'
  have hc := congrArg QuaternionAlgebra.imK h'
  simp [qk] at hc

/-- **The class is exactly the line spanned by `ad_i`** — the `α ≠ id` case of
Remark 4.6 for the conjugation by `i`. -/
theorem class_is_line (D : H →ₗ[ℝ] H) :
    ((∀ x, D (conjI x) = conjI (D x)) ∧ (∀ x y, D (prod x y) = prod (D x) y + prod x (D y)))
      ↔ ∃ c : ℝ, D = c • adI := by
  constructor
  · rintro ⟨hDα, hD⟩
    exact main D hDα hD
  · rintro ⟨c, rfl⟩
    constructor
    · intro x
      simp only [LinearMap.smul_apply, adI_comm, conjI_smul]
    · intro x y
      simp only [LinearMap.smul_apply, prod_smul_left, prod_smul_right, adI_mem, smul_add]



/-! ## The conjugacy identity: every pure imaginary unit is conjugate to `i`

The paper's justification of "any two of the latter are conjugate" (Remark 4.6).
For any `q'` with `q' * q' = -1`, the element `u = 1 - q' * i` satisfies
`u * i = q' * u`; it vanishes exactly when `q' = -i`, the case the paper
excludes because it gives the same conjugation as `i`. -/

theorem conj_conjugacy (q' : H) (hq : q' * q' = -1) :
    (1 - q' * qi) * qi = q' * (1 - q' * qi) := by
  have h : q' * (q' * qi) = -qi := by
    rw [← mul_assoc, hq, neg_mul, one_mul]
  have h2 : q' * qi * qi = -q' := by
    rw [mul_assoc, qi_qi, mul_neg, mul_one]
  rw [sub_mul, one_mul, mul_sub, mul_one, h, h2]
  abel

/-! ## F2: a reduced ring is semiprime -/

theorem reduced_imp_semiprime {R : Type*} [Ring R] [IsReduced R] :
    Background.JordanHerstein.SemiprimeRing R := by
  intro a ha
  exact IsReduced.eq_zero a ⟨2, by simpa [pow_two] using ha 1⟩

end QuaternionConjug
