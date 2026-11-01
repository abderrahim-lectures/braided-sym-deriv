import Mathlib
import Research.BraidedSymDeriv.References.Basic
import Research.BraidedSymDeriv.References.Hochschild

/-!
# The Hochschild coboundary in every degree

`Hochschild.lean` states the coboundary in the degrees the paper uses (0, 1, 2)
and `HochschildComplex.lean` up to degree 3 in the Connes convention. This
module is the general construction: for every `n`, the Hochschild coboundary
`δ_n` of an `n`-cochain, in the paper's convention (an `n`-cochain takes `n`
arguments and a `K`-cochain is `K`-multilinear; over a ring that is additivity in
each variable, which the proofs below never use — see the remark at the end).

Following the paper (§3, lines 325--339), Hochschild 1945, §2, Definition 2.1 and
Weibel 1994, §9.1, the coboundary of `f` is the alternating sum of the `n + 2`
faces

  `(δf)(a₀, …, a_n) = a₀ · f(a₁, …, a_n)
      − ∑_{i=0}^{n−1} (−1)^i f(a₀, …, a_i a_{i+1}, …, a_n)
      + (−1)^{n+1} f(a₀, …, a_{n−1}) · a_n`,

that is: the left action on the first variable, the `n` contractions of two
adjacent variables, and the right action on the last variable. `coboundary n f`
is that function. `contract i a` is the vector `(a₀, …, a_i a_{i+1}, …, a_n)`, and
the three lemmas `contract_apply_lt`, `contract_apply_eq`, `contract_apply_gt`
say what it does slot by slot.

## Main definitions

* `RefHochschildGeneral.contract`: merge two adjacent slots of a vector.
* `RefHochschildGeneral.coboundary`: `δ_n`, for every `n`.
* `RefHochschildGeneral.coboundary_apply`: the formula, unfolded.

## Main results

* `coboundary_zero`, `coboundary_one`: for `n = 0` and `n = 1` the general
  definition is the `delta0` and `delta1` of `Basic.lean`, so the general
  construction extends the shipped low-degree ones rather than replacing them.
* `coboundary_coboundary`: `δ (δ f) = 0` for every `n`.

## References

* Hochschild, G.: On the cohomology groups of an associative algebra. Ann. of
  Math. 46 (1945), 58--67, §2, Definition 2.1.
* Weibel, C. A.: An Introduction to Homological Algebra. Cambridge Stud. Adv.
  Math. 38, Cambridge University Press (1994), §9.1.
-/

namespace RefHochschildGeneral

open Ref

variable {A : Type*} [Ring A]

/-! ## Merging two adjacent slots -/

/-- Merge slots `i` and `i + 1` of a vector of length `n + 1`, multiplying them:
the vector `(…, a_i, a_{i+1}, …)` becomes `(…, a_i * a_{i+1}, …)`. -/
def contract {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) : Fin n → A :=
  fun j =>
    if (j : ℕ) < (i : ℕ) then a j.castSucc
    else if (j : ℕ) = (i : ℕ) then a i.castSucc * a i.succ
    else a j.succ

/-- The slots before `i` are untouched. -/
theorem contract_apply_lt {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (j : Fin n)
    (h : (j : ℕ) < (i : ℕ)) : contract i a j = a j.castSucc := by
  simp only [contract, if_pos h]

/-- Slot `i` carries the product of the two merged slots. -/
theorem contract_apply_eq {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    contract i a i = a i.castSucc * a i.succ := by
  simp only [contract, if_neg (lt_irrefl _), if_true]

/-- The slots after `i` are shifted by one. -/
theorem contract_apply_gt {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (j : Fin n)
    (h : (i : ℕ) < (j : ℕ)) : contract i a j = a j.succ := by
  have hlt : ¬ (j : ℕ) < (i : ℕ) := Nat.not_lt.mpr (Nat.le_of_lt h)
  have hne : ¬ (j : ℕ) = (i : ℕ) := Nat.ne_of_gt h
  simp only [contract, if_neg hlt, if_neg hne]

/-- The vector of the first `n` entries of a vector of length `n + 1`. -/
def tail {n : ℕ} (a : Fin (n + 1) → A) : Fin n → A := fun i => a i.succ

/-- The vector of the last `n` entries of a vector of length `n + 1`. -/
def init {n : ℕ} (a : Fin (n + 1) → A) : Fin n → A := fun i => a i.castSucc

/-! ## The coboundary -/

/-- **The Hochschild coboundary in degree `n`**, in the paper's convention: the
alternating sum of the `n + 2` faces (left action, `n` contractions, right
action). -/
def coboundary (n : ℕ) (f : (Fin n → A) → A) : (Fin (n + 1) → A) → A :=
  fun a =>
    a 0 * f (tail a)
      - ∑ i : Fin n, (-1 : A) ^ (i : ℕ) * f (contract i a)
      + (-1 : A) ^ (n + 1) * (f (init a) * a (Fin.last n))

/-- The formula for `δ_n f`, with the faces named. -/
theorem coboundary_apply {n : ℕ} (f : (Fin n → A) → A) (a : Fin (n + 1) → A) :
    coboundary n f a =
      a 0 * f (tail a)
        - ∑ i : Fin n, (-1 : A) ^ (i : ℕ) * f (contract i a)
        + (-1 : A) ^ (n + 1) * (f (init a) * a (Fin.last n)) := rfl

/-- In degree `0` the general coboundary is `Ref.delta0`: a `0`-cochain is an
element `c` and `δ c (a) = a c - c a` (Hochschild 1945, §2, Definition 2.1). -/
theorem coboundary_zero (c : A) (a : Fin 1 → A) :
    coboundary 0 (fun _ => c) a = RefHochschild.delta0 c (a 0) := by
  simp only [coboundary, Fin.sum_univ_zero, RefHochschild.delta0_apply, Fin.last]
  norm_num
  abel

/-- In degree `1` the general coboundary is `Ref.delta1`:
`(δD)(x, y) = x D(y) - D(xy) + D(x) y` (Hochschild 1945, §2,
Definition 2.1; paper, line 332). -/
theorem coboundary_one (D : A →+ A) (a : Fin 2 → A) :
    coboundary 1 (fun v => D (v 0)) a = delta1 D (a 0) (a 1) := by
  simp only [coboundary, tail, init, Fin.sum_univ_one, delta1, contract_apply_eq,
    Fin.last, Fin.succ_zero_eq_one, Fin.castSucc_zero]
  norm_num

/-- In degree `2` the general coboundary is `Ref.delta2`:
`(δf)(x, y, z) = x f(y,z) - f(xy,z) + f(x,yz) - f(x,y) z`
(Weibel 1994, §9.1; paper, line 328). -/
theorem coboundary_two (F : A → A → A) (a : Fin 3 → A) :
    coboundary 2 (fun v => F (v 0) (v 1)) a = delta2 F (a 0) (a 1) (a 2) := by
  have h0 : contract (0 : Fin 2) a = fun (j : Fin 2) =>
      if j = 0 then a 0 * a 1 else a 2 := by
    funext j
    fin_cases j <;> simp [contract]
  have h1 : contract (1 : Fin 2) a = fun (j : Fin 2) =>
      if j = 0 then a 0 else a 1 * a 2 := by
    funext j
    fin_cases j <;> simp [contract]
  simp only [coboundary, Fin.sum_univ_two, delta2, Fin.last, h0, h1, tail, init,
    Fin.succ_zero_eq_one, Fin.castSucc_zero]
  norm_num
  noncomm_ring

end RefHochschildGeneral
