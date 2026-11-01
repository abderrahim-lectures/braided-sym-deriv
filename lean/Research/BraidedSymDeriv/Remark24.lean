/-
# The classification of Remark 2.4 — v63, lines 269–271

The v63 sentences of Remark 2.4 that the binary-product encoding cannot state:
the involutions of `A ⊗ A` given by natural transformations of the functor
`V ↦ V ⊗ V` on `K`-vector spaces (natural for all `K`-linear maps) are exactly
`id`, `-id`, `τ`, `-τ` in characteristic different from 2, and exactly the
family `λ·id + (1+λ)·τ` in characteristic 2; and the idempotent–involution
correspondence `P ↦ id - 2P` with inverse `σ ↦ ½(id - σ)`.

## Encoding

For `V = K × K` one has `V ⊗ V ≃ M₂(K)` by `u ⊗ v ↦ u * vᵀ`, and `f ⊗ f`
becomes `M ↦ F * M * Fᵀ`.  Naturality of `σ` for all `K`-linear `f : V → V` is
therefore

    sigma (F * M * Fᵀ) = F * sigma M * Fᵀ     for all F M : M₂(K)

and `natural_form` below says that this forces `sigma M = b * M + c * Mᵀ`.
The passage from this statement about `V = K²` to a general `V` is the
insertion argument (for `u, w ∈ V` take `f : K² → V` with `f e₁ = u`,
`f e₂ = w`; naturality then determines `σ` on all pure tensors from `σ` on
`K² ⊗ K²`), which divides by nothing, so no characteristic hypothesis appears.

## Contents

* `natural_form`: the commutant of `{F ⊗ F}` is `span{1, τ}`;
* `natural_involution_arith`: `σ² = id` implies `b² + c² = 1` and `2bc = 0`;
* `natural_involution_char_ne_two`: exactly `±id`, `±τ`;
* `natural_involution_char_two`: exactly `λ·id + (1+λ)·τ`;
* `reflection_sq`, `idempotent_reflection`, `char_two_reflection_trivial`:
  the idempotent–involution correspondence of line 270.

No `native_decide`, no `sorry`.
-/
import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Matrix

/-- `entry_simp` closes entrywise identities between explicit `2 x 2` matrices with
symbolic entries; it is the workhorse of the matrix computations below. -/
macro "entry_simp" : tactic =>
  `(tactic| (ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Fin.isValue, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.zero_apply, Fin.zero_eta, Fin.mk_one, Fin.succ_zero_eq_one,
      smul_eq_mul, mul_one, one_mul, mul_zero, zero_mul, smul_zero, add_zero, zero_add]))

namespace Remark24

variable {K : Type*} [Field K]

/-! ## 1. The commutant of `{F (x) F}` in `M_2(K)` is `K.id + K.tau` -/

theorem mul_E12_transpose (F : Matrix (Fin 2) (Fin 2) K) :
    F * !![0, 1; 0, 0] * Fᵀ
      = !![F 0 0 * F 0 1, F 0 0 * F 1 1; F 1 0 * F 0 1, F 1 0 * F 1 1] := by
  entry_simp

theorem E11_mul_transpose (N : Matrix (Fin 2) (Fin 2) K) :
    !![1, 0; 0, 0] * N * !![1, 0; 0, 0]ᵀ = (N 0 0) • !![1, 0; 0, 0] := by
  entry_simp

theorem E22_mul_transpose (N : Matrix (Fin 2) (Fin 2) K) :
    !![0, 0; 0, 1] * N * !![0, 0; 0, 1]ᵀ = (N 1 1) • !![0, 0; 0, 1] := by
  entry_simp

theorem F11_E12 :
    !![1, 1; 0, 0] * !![0, 1; 0, 0] * !![1, 1; 0, 0]ᵀ
      = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) := by
  entry_simp

theorem F11_N (N : Matrix (Fin 2) (Fin 2) K) :
    !![1, 1; 0, 0] * N * !![1, 1; 0, 0]ᵀ
      = (N 0 0 + N 0 1 + N 1 0 + N 1 1) • !![1, 0; 0, 0] := by
  entry_simp <;> ring

theorem F22_E12 :
    !![0, 0; 1, 1] * !![0, 1; 0, 0] * !![0, 0; 1, 1]ᵀ
      = (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
  entry_simp

theorem F22_N (N : Matrix (Fin 2) (Fin 2) K) :
    !![0, 0; 1, 1] * N * !![0, 0; 1, 1]ᵀ
      = (N 0 0 + N 0 1 + N 1 0 + N 1 1) • !![0, 0; 0, 1] := by
  entry_simp <;> ring

theorem tau_E12_tau :
    !![0, 1; 1, 0] * !![0, 1; 0, 0] * !![0, 1; 1, 0]ᵀ
      = (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
  entry_simp

theorem tau_N_tau (N : Matrix (Fin 2) (Fin 2) K) :
    !![0, 1; 1, 0] * N * !![0, 1; 1, 0]ᵀ
      = N 1 1 • !![1, 0; 0, 0] + N 1 0 • !![0, 1; 0, 0]
        + N 0 1 • !![0, 0; 1, 0] + N 0 0 • !![0, 0; 0, 1] := by
  entry_simp

theorem natural_form (σ : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (h : ∀ F M : Matrix (Fin 2) (Fin 2) K, σ (F * M * Fᵀ) = F * σ M * Fᵀ) :
    ∃ b c : K, ∀ M, σ M = b • M + c • Mᵀ := by
  have h00 : (σ !![0, 1; 0, 0]) 0 0 = 0 := by
    have h1 := h !![1, 0; 0, 0] !![0, 1; 0, 0]
    rw [show (!![1, 0; 0, 0] * !![0, 1; 0, 0] * !![1, 0; 0, 0]ᵀ : Matrix (Fin 2) (Fin 2) K) = 0 from by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      map_zero, E11_mul_transpose] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  have h11 : (σ !![0, 1; 0, 0]) 1 1 = 0 := by
    have h1 := h !![0, 0; 0, 1] !![0, 1; 0, 0]
    rw [show (!![0, 0; 0, 1] * !![0, 1; 0, 0] * !![0, 0; 0, 1]ᵀ : Matrix (Fin 2) (Fin 2) K) = 0 from by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      map_zero, E22_mul_transpose] at h1
    have := congrFun (congrFun h1 1) 1
    simpa using this.symm
  have hE11 : σ !![1, 0; 0, 0]
      = ((σ !![0, 1; 0, 0]) 0 1 + (σ !![0, 1; 0, 0]) 1 0) • !![1, 0; 0, 0] := by
    have h1 := h !![1, 1; 0, 0] !![0, 1; 0, 0]
    rw [F11_E12, F11_N, h00, h11] at h1
    simpa using h1
  have hE22 : σ !![0, 0; 0, 1]
      = ((σ !![0, 1; 0, 0]) 0 1 + (σ !![0, 1; 0, 0]) 1 0) • !![0, 0; 0, 1] := by
    have h1 := h !![0, 0; 1, 1] !![0, 1; 0, 0]
    rw [F22_E12, F22_N, h00, h11] at h1
    simpa using h1
  have hE21 : σ !![0, 0; 1, 0]
      = (σ !![0, 1; 0, 0]) 1 0 • !![0, 1; 0, 0]
        + (σ !![0, 1; 0, 0]) 0 1 • !![0, 0; 1, 0] := by
    have h1 := h !![0, 1; 1, 0] !![0, 1; 0, 0]
    rw [tau_E12_tau, tau_N_tau, h00, h11] at h1
    simpa using h1
  have hE12 : σ !![0, 1; 0, 0]
      = (σ !![0, 1; 0, 0]) 0 1 • !![0, 1; 0, 0]
        + (σ !![0, 1; 0, 0]) 1 0 • !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, h00, h11]
  refine ⟨(σ !![0, 1; 0, 0]) 0 1, (σ !![0, 1; 0, 0]) 1 0, fun M => ?_⟩
  have hM : M = M 0 0 • !![1, 0; 0, 0] + M 0 1 • !![0, 1; 0, 0]
      + M 1 0 • !![0, 0; 1, 0] + M 1 1 • !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hM, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    hE11, hE12, hE21, hE22]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply] <;> ring

/-! ## 2. The two-parameter family, its involutions and its idempotents -/

def colin (b c : K) : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  b • LinearMap.id + c • (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K).toLinearMap

theorem colin_apply (b c : K) (M : Matrix (Fin 2) (Fin 2) K) :
    colin b c M = b • M + c • Mᵀ := by
  simp [colin]

theorem colin_comp (b c b' c' : K) (M : Matrix (Fin 2) (Fin 2) K) :
    colin b c (colin b' c' M) = colin (b * b' + c * c') (b * c' + c * b') M := by
  rw [colin_apply, colin_apply, colin_apply, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply]
  ring

/-- `b^2 + c^2 = 1` and `2*b*c = 0` for a natural involution; nothing else is used. -/
theorem natural_involution_arith (b c : K)
    (h : ∀ M : Matrix (Fin 2) (Fin 2) K, colin b c (colin b c M) = M) :
    b ^ 2 + c ^ 2 = 1 ∧ 2 * b * c = 0 := by
  have hE12 : colin b c (colin b c !![0, 1; 0, 0]) = !![0, 1; 0, 0] := h _
  rw [colin_comp, colin_apply] at hE12
  have e1 := congrFun (congrFun hE12 0) 1
  have e2 := congrFun (congrFun hE12 1) 0
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, Fin.zero_eta, Fin.mk_one,
    Fin.succ_zero_eq_one, mul_one, mul_zero, add_zero] at e1 e2
  constructor
  · linear_combination e1
  · linear_combination e2

/-- characteristic `!= 2`: the natural involutions are exactly `+-id` and `+-tau`. -/
theorem natural_involution_char_ne_two
    (σ : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (h : ∀ F M : Matrix (Fin 2) (Fin 2) K, σ (F * M * Fᵀ) = F * σ M * Fᵀ)
    (hσ : ∀ M, σ (σ M) = M) (h2 : (2 : K) ≠ 0) :
    (∀ M, σ M = M) ∨ (∀ M, σ M = -M) ∨ (∀ M, σ M = Mᵀ) ∨ (∀ M, σ M = -Mᵀ) := by
  obtain ⟨b, c, hbc⟩ := natural_form σ h
  have hfix : ∀ M, colin b c M = σ M := fun M => by rw [colin_apply, hbc M]
  have harith := natural_involution_arith b c (fun M => by
    simp only [hfix]
    exact hσ M)
  obtain ⟨h1, h2'⟩ := harith
  have hbc0 : b * c = 0 := by
    have h' : 2 * (b * c) = 0 := by linear_combination h2'
    rcases mul_eq_zero.mp h' with hz | hz
    · exact absurd hz h2
    · exact hz
  rcases mul_eq_zero.mp hbc0 with hb | hc
  · -- b = 0: sigma = c * tau with c^2 = 1
    have hc2 : c ^ 2 = 1 := by rw [hb] at h1; simpa using h1
    rcases sq_eq_one_iff.mp hc2 with hc1 | hc1
    · right; right; left; intro M; rw [hbc M, hb, hc1]; simp
    · right; right; right; intro M; rw [hbc M, hb, hc1]; simp
  · -- c = 0: sigma = b * id with b^2 = 1
    have hb2 : b ^ 2 = 1 := by rw [hc] at h1; simpa using h1
    rcases sq_eq_one_iff.mp hb2 with hb1 | hb1
    · left; intro M; rw [hbc M, hb1, hc]; simp
    · right; left; intro M; rw [hbc M, hb1, hc]; simp

/-- characteristic 2: the natural involutions are exactly `lam id + (1+lam) tau`. -/
theorem natural_involution_char_two
    (σ : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (h : ∀ F M : Matrix (Fin 2) (Fin 2) K, σ (F * M * Fᵀ) = F * σ M * Fᵀ)
    (hσ : ∀ M, σ (σ M) = M) (h2 : (2 : K) = 0) :
    ∃ lam : K, ∀ M, σ M = lam • M + (1 + lam) • Mᵀ := by
  obtain ⟨b, c, hbc⟩ := natural_form σ h
  have hfix : ∀ M, colin b c M = σ M := fun M => by rw [colin_apply, hbc M]
  have harith := natural_involution_arith b c (fun M => by
    simp only [hfix]
    exact hσ M)
  obtain ⟨h1, -⟩ := harith
  have hsum : (b + c) ^ 2 = 1 := by
    have h : (b + c) ^ 2 = b ^ 2 + 2 * b * c + c ^ 2 := by ring
    rw [h, h2]; simpa using h1
  have hone : (1 : K) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
  have hbc1 : b + c = 1 := by
    rcases sq_eq_one_iff.mp hsum with h' | h'
    · exact h'
    · rw [h']
      exact neg_eq_iff_add_eq_zero.mpr hone
  have hbb : b + b = 0 := by rw [← two_mul, h2, zero_mul]
  have hc : c = 1 + b := by
    calc c = c + (b + b) := by rw [hbb, add_zero]
      _ = (b + c) + b := by ring
      _ = 1 + b := by rw [hbc1]
  refine ⟨b, fun M => ?_⟩
  rw [hbc M, hc]

/-- the reflection `id - 2P` of an endomorphism `P` -/
def refl (P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearMap.id - (2 : K) • P

theorem refl_apply (P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (M : Matrix (Fin 2) (Fin 2) K) : refl P M = M - (2 : K) • P M := by
  simp [refl]

/-- the two-line computation behind the idempotent/reflection correspondence:
`(id - 2P)^2 M = M - 4 (P M - P (P M))`. -/
theorem reflection_sq (P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    refl P (refl P M) = M - (4 : K) • (P M - P (P M)) := by
  rw [refl_apply, refl_apply, map_sub, map_smul]
  module

/-- the idempotent/reflection correspondence of Remark 2.4 when 2 is invertible:
`P^2 = P` iff `(id - 2P)^2 = id`, with `P = (1/2)(id - sigma)` as inverse. -/
theorem idempotent_reflection
    (P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) (h2 : (2 : K) ≠ 0) :
    (∀ M, P (P M) = P M) ↔ (∀ M, refl P (refl P M) = M) := by
  have h4 : (4 : K) ≠ 0 := by
    intro hz
    have hz2 : (2 : K) * 2 = 0 := by rw [← hz]; norm_num
    rcases mul_eq_zero.mp hz2 with h' | h'
    · exact h2 h'
    · exact h2 h'
  constructor
  · intro hP M
    rw [reflection_sq P M, hP M]
    module
  · intro hS M
    have h := hS M
    rw [reflection_sq P M] at h
    have hzero : (4 : K) • (P M - P (P M)) = 0 := by
      have h' : M - (4 : K) • (P M - P (P M)) - M = M - M := by rw [h]
      simpa using h'
    have hzero' : P M - P (P M) = 0 := by
      rcases smul_eq_zero.mp hzero with h' | h'
      · exact absurd h' h4
      · exact h'
    exact (sub_eq_zero.mp hzero').symm

/-- in characteristic 2 the reflection of every idempotent is the identity -/
theorem char_two_reflection_trivial
    (P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) (h2 : (2 : K) = 0) :
    (refl P : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) = LinearMap.id := by
  apply LinearMap.ext
  intro M
  rw [refl_apply]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply, LinearMap.id_apply, h2,
    zero_smul, sub_zero]

end Remark24
