import Mathlib
import Research.BraidedSymDeriv.References.Basic

/-!
# Involutions of rings (Herstein 1976)

The paper (§3, line 285) says: "An involutive anti-automorphism is an involution
of the ring `A` in the sense of Herstein, *Rings with Involution*, §1.2, that is,
a map `*` with `a** = a`, `(a + b)* = a* + b*` and `(ab)* = b*a*`."

This module formalizes exactly those three axioms as a structure and derives
what follows from them alone. Note what does **not** follow: `1* = 1` is not one
of Herstein's axioms — but in a unital ring it is a consequence of them
(`RefInvolution.RingInvolution.map_one`), because `1*` is a two-sided identity.

The paper's use of the notion is the construction `σ_α(x⊗y) = α(y)⊗α(x)` for an
involutive anti-automorphism, and the fact that `α² ⊗ α² = id` exactly when
`α² = id`. The transpose of a matrix algebra is the standard example, and it is
recorded here.

## Main results

* `RefInvolution.RingInvolution`: Herstein's three axioms.
* `RefInvolution.RingInvolution.map_zero`, `map_neg`, `map_sub`, `injective`.
* `RefInvolution.matrixTranspose`: the transpose is an involution of `Mₙ(K)`.
* `RefInvolution.mem_fixed_or_neg`: with `2` invertible the fixed and the
  negated parts span everything, `x = ½(x + x*) + ½(x − x*)`, the decomposition
  the paper uses after Theorem 4.1.

## References

* Herstein, I. N.: Rings with Involution. Chicago Lectures in Mathematics.
  University of Chicago Press, Chicago (1976), §1.2.
-/

namespace RefInvolution

/-- **Herstein 1976, §1.2**: an involution of a ring is a map with
`a** = a`, `(a + b)* = a* + b*` and `(ab)* = b*a*`. -/
structure RingInvolution (A : Type*) [Add A] [Mul A] where
  /-- The map `*`. -/
  toFun : A → A
  /-- Additivity. -/
  map_add' : ∀ x y : A, toFun (x + y) = toFun x + toFun y
  /-- Anti-multiplicativity. -/
  map_mul' : ∀ x y : A, toFun (x * y) = toFun y * toFun x
  /-- Involution. -/
  involutive' : ∀ x : A, toFun (toFun x) = x

namespace RingInvolution

variable {A : Type*} [Ring A] (s : RingInvolution A)

instance : CoeFun (RingInvolution A) (fun _ => A → A) := ⟨RingInvolution.toFun⟩

@[simp] theorem map_add (x y : A) : s (x + y) = s x + s y := s.map_add' x y
@[simp] theorem map_mul (x y : A) : s (x * y) = s y * s x := s.map_mul' x y
@[simp] theorem involutive (x : A) : s (s x) = x := s.involutive' x

theorem map_zero : s 0 = 0 := by
  have h : s 0 + s 0 = s 0 + 0 := by rw [← map_add, add_zero, add_zero]
  exact add_left_cancel h

theorem map_neg (x : A) : s (-x) = -s x := by
  have h : s (-x) + s x = 0 := by rw [← map_add, neg_add_cancel, map_zero]
  exact eq_neg_iff_add_eq_zero.mpr h

theorem map_sub (x y : A) : s (x - y) = s x - s y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, map_add, map_neg]

theorem injective : Function.Injective s := by
  intro x y h
  have := congrArg s h
  rwa [involutive, involutive] at this

/-- `1* = 1`. Herstein 1976, §1.2 does not assume this, but in a unital ring it
follows from the three axioms: `(1 · 1*)* = 1** · 1* = 1 · 1* = 1*` while
`(1 · 1*)* = 1** = 1`, so `1* = 1`. -/
theorem map_one : s 1 = (1 : A) := by
  have h : s (1 * s 1) = s (s 1) * s 1 := s.map_mul' 1 (s 1)
  rw [one_mul, involutive, one_mul] at h
  exact h.symm

/-- `(xⁿ)* = (x*)ⁿ` (Herstein 1976, §1.2). -/
theorem map_pow (x : A) (n : ℕ) : s (x ^ n) = s x ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using map_one (s := s)
  | succ k ih => rw [pow_succ, map_mul, ih, pow_succ']

end RingInvolution

/-- **The transpose** is an involution of a matrix ring in Herstein's sense:
`(M * N)ᵀ = Nᵀ * Mᵀ` and `(Mᵀ)ᵀ = M`. -/
def matrixTranspose (n : Type*) [Fintype n] [DecidableEq n] (K : Type*) [CommRing K] :
    RingInvolution (Matrix n n K) where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_mul' := Matrix.transpose_mul
  involutive' := Matrix.transpose_transpose

/-- **The symmetric/skew decomposition** used in the proof of Theorem 4.1: over a
`ℚ`-algebra, `x = ½(x + x*) + ½(x − x*)`. -/
theorem eq_half_symm_add_half_skew {A : Type*} [Ring A] [Algebra ℚ A]
    (s : RingInvolution A) (x : A) :
    x = (2 : ℚ)⁻¹ • (x + s x) + (2 : ℚ)⁻¹ • (x - s x) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have h : (x + s x) + (x - s x) = (2 : ℚ) • x := by
    rw [two_smul]
    abel
  rw [← smul_add, h, smul_smul, inv_mul_cancel₀ h2, one_smul]

end RefInvolution
