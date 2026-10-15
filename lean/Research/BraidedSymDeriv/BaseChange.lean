import Mathlib

open Finset

namespace BaseChange

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The linear map `D` with matrix `d`: `D v = fun k => ∑ i, d k i * v i`. -/
def applyD (d : Fin n → Fin n → R) (v : Fin n → R) : Fin n → R :=
  fun k => ∑ i, d k i * v i

/-- The product with structure constants `s k i j`, so that `x_i * x_j = ∑ k, s k i j * x_k`. -/
def mulS (s : Fin n → Fin n → Fin n → R) (u w : Fin n → R) : Fin n → R :=
  fun k => ∑ i, ∑ j, s k i j * (u i * w j)

/-- The basis vector `x_i`. -/
def e (i : Fin n) : Fin n → R := Pi.single i 1

theorem applyD_e (d : Fin n → Fin n → R) (i k : Fin n) :
    applyD d (e i) k = d k i := by
  unfold applyD e
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mulS_right (s : Fin n → Fin n → Fin n → R) (i k : Fin n) (w : Fin n → R) :
    mulS s (e i) w k = ∑ b, s k i b * w b := by
  unfold mulS e
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Pi.single_eq_same, one_mul]
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    rw [Pi.single_eq_of_ne ha, zero_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mulS_left (s : Fin n → Fin n → Fin n → R) (j k : Fin n) (u : Fin n → R) :
    mulS s u (e j) k = ∑ a, s k a j * u a := by
  unfold mulS e
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem mulS_e (s : Fin n → Fin n → Fin n → R) (i j k : Fin n) :
    mulS s (e i) (e j) k = s k i j := by
  rw [mulS_right, Finset.sum_eq_single j]
  · rw [e, Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [e, Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The formula for `Φ_ijk(d)` in the proof of Proposition 3.8 (base change): the `x_k`
coefficient of `D(x_i x_j) - D(x_i) x_j - x_i D(x_j)` in coordinates. -/
theorem phi_formula (d : Fin n → Fin n → R) (s : Fin n → Fin n → Fin n → R) (i j k : Fin n) :
    applyD d (mulS s (e i) (e j)) k
      - mulS s (applyD d (e i)) (e j) k
      - mulS s (e i) (applyD d (e j)) k
    = ∑ p, s p i j * d k p - ∑ p, s k p j * d p i - ∑ p, s k i p * d p j := by
  have h1 : applyD d (mulS s (e i) (e j)) k = ∑ p, s p i j * d k p := by
    unfold applyD
    apply Finset.sum_congr rfl
    intro p _
    rw [mulS_e, mul_comm]
  have h2 : mulS s (applyD d (e i)) (e j) k = ∑ p, s k p j * d p i := by
    rw [mulS_left]
    apply Finset.sum_congr rfl
    intro p _
    rw [applyD_e]
  have h3 : mulS s (e i) (applyD d (e j)) k = ∑ p, s k i p * d p j := by
    rw [mulS_right]
    apply Finset.sum_congr rfl
    intro p _
    rw [applyD_e]
  rw [h1, h2, h3]

end BaseChange

section KernelBaseChange

open TensorProduct

variable {K L V W : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

/-- The kernel of a base-changed linear map is the base change of the kernel
(the linear-algebra core of Proposition 3.8). Flatness of `L` over the field `K`
is found by instance search. -/
noncomputable def kerBaseChangeEquiv (Φ : V →ₗ[K] W) :
    (L ⊗[K] LinearMap.ker Φ) ≃ₗ[L]
      LinearMap.ker (AlgebraTensorModule.lTensor L L Φ) :=
  LinearMap.tensorKerEquiv L L Φ

/-- The dimension of the kernel does not change under a field extension. -/
theorem finrank_ker_baseChange [Module.Finite K V] (Φ : V →ₗ[K] W) :
    Module.finrank L (LinearMap.ker (AlgebraTensorModule.lTensor L L Φ))
      = Module.finrank K (LinearMap.ker Φ) := by
  have h := LinearEquiv.finrank_eq (kerBaseChangeEquiv (L := L) Φ)
  rw [← h]
  exact Module.finrank_baseChange

end KernelBaseChange

