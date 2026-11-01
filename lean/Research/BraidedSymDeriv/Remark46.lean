/-
# Remark 4.6: commutativity is needed in Theorem 4.1

Kernel-checked formalisation of the counterexample of Remark 4.6 of
"Braided-Symmetric Derivations of Algebras" (v63).

* `A` is the four-dimensional `F_3`-algebra with basis `1, t, v, w` and products
  `t*t = 0`, `t*v = v*t = t*w = w*t = 0`, `v*v = w*w = w*v = t`, `v*w = 0`;
* `alpha` is the involutive automorphism with `alpha t = t`, `alpha v = -v`,
  `alpha w = -w`;
* `D` is the linear map with `D v = v + w` and `D 1 = D t = D w = 0`.

Proved here, all kernel-checked (no `native_decide`, no `sorry`):

* `assoc`        : the algebra is associative;
* `alpha_add`, `alpha_mul`, `alpha_one`, `alpha_involutive` : `alpha` is an
  involutive algebra automorphism;
* `D_add`        : `D` is additive;
* `comm`         : `D` commutes with `alpha`;
* `leibniz`      : `D` satisfies the Leibniz rule of the twisted product
  `x . y = xy + alpha y * alpha x`, i.e. `D` lies in `BSDer_{sigma_alpha}(A)^alpha`;
* `not_deriv`    : `D` is not a derivation;
* `defect_vw`    : the Leibniz defect of `D` at `(v,w)` is `-t`;
* `skew_sq_zero` : `(v + w)^2 = 0`.

So, by `leibniz` and `not_deriv`, `BSDer_{sigma_alpha}(A)^alpha` contains an
element that is not a derivation: Theorem 4.1 fails without commutativity.

## What is not formalised

The two dimension counts of the remark, `dim BSDer^alpha = 3` and
`dim Der^alpha = 2`. They are a rank computation over `F_3`, verified and
displayed by `results/review-v62-scripts/run1.py` (and checkable by hand from the
64 basis triples plus the parametrisation `D(1) = 0`, `D(t) in F_3 t`,
`D(v) in span{v,w}`, `D(w) in span{v,w}`, `(D v)_w = (D t)_t`). A finite-witness
proof cannot reach them: the class is defined by a universally quantified rule
over the 81-element algebra, and the kernel `decide` that would enumerate the
additive maps does not terminate. Formalising them needs the linear-algebra
parametrisation, which is a separate piece of work.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace BSD.Remark46

/-- The algebra of Remark 4.6, in coordinates `(a0, a1, a2, a3)` of
`a0 * 1 + a1 * t + a2 * v + a3 * w` over `F_3`. -/
abbrev A : Type := Fin 4 → Fin 3

/-! ## The multiplication -/

/-- The product of Remark 4.6, in coordinates. -/
def mul (x y : A) : A := fun i =>
  match i with
  | 0 => x 0 * y 0
  | 1 => x 0 * y 1 + x 1 * y 0 + x 2 * y 2 + x 3 * y 3 + x 3 * y 2
  | 2 => x 0 * y 2 + x 2 * y 0
  | 3 => x 0 * y 3 + x 3 * y 0

/-- `1`. -/
def one : A := fun i => if i = 0 then 1 else 0
/-- `t`. -/
def t : A := fun i => if i = 1 then 1 else 0
/-- `v`. -/
def v : A := fun i => if i = 2 then 1 else 0
/-- `w`. -/
def w : A := fun i => if i = 3 then 1 else 0

/-- Bilinearity in the second variable. -/
lemma mul_add_vec (x y z : A) : mul x (y + z) = mul x y + mul x z := by
  funext i
  fin_cases i <;> simp [mul, mul_add] <;> ac_rfl

/-- Bilinearity in the first variable. -/
lemma add_mul_vec (x y z : A) : mul (x + y) z = mul x z + mul y z := by
  funext i
  fin_cases i <;> simp [mul, add_mul] <;> ac_rfl

/-- `A` is associative. -/
theorem assoc : ∀ x y z : A, mul (mul x y) z = mul x (mul y z) := by
  intro x y z
  funext i
  fin_cases i <;> simp [mul, mul_add, add_mul, mul_assoc] <;> ac_rfl

/-- `1` is a left unit. -/
theorem one_mul : ∀ x : A, mul one x = x := by
  intro x
  funext i
  fin_cases i <;> simp [mul, one]

/-- `1` is a right unit. -/
theorem mul_one : ∀ x : A, mul x one = x := by
  intro x
  funext i
  fin_cases i <;> simp [mul, one]

/-! ## The involution `alpha` -/

/-- `alpha`: `t` is fixed, `v` and `w` are negated. -/
def alpha (x : A) : A := fun i =>
  match i with
  | 0 => x 0
  | 1 => x 1
  | 2 => - x 2
  | 3 => - x 3

theorem alpha_add : ∀ x y : A, alpha (x + y) = alpha x + alpha y := by
  intro x y
  funext i
  fin_cases i <;> simp [alpha] <;> ac_rfl

theorem alpha_one : alpha one = one := by
  funext i
  fin_cases i <;> simp [alpha, one]

/-- `alpha` is multiplicative.  Checked over the 81 * 81 pairs of the finite
algebra; the sign bookkeeping (`(-1) * (-1) = 1` in `F_3`) is where a hand proof
uses characteristic three. -/
theorem alpha_mul : ∀ x y : A, alpha (mul x y) = mul (alpha x) (alpha y) := by
  decide

theorem alpha_involutive : ∀ x : A, alpha (alpha x) = x := by
  intro x
  funext i
  fin_cases i <;> simp [alpha]

/-! ## The map `D` -/

/-- `D v = v + w`, `D 1 = D t = D w = 0`. -/
def D (x : A) : A := fun i =>
  match i with
  | 0 => 0
  | 1 => 0
  | 2 => x 2
  | 3 => x 2

theorem D_add : ∀ x y : A, D (x + y) = D x + D y := by
  intro x y
  funext i
  fin_cases i <;> simp [D]

/-- `D` commutes with `alpha`. -/
theorem comm : ∀ x : A, D (alpha x) = alpha (D x) := by
  intro x
  funext i
  fin_cases i <;> simp [D, alpha]

/-- `D v = v + w`. -/
theorem D_v : D v = v + w := by
  funext i
  fin_cases i <;> simp [D, v, w]

/-- `D w = 0`. -/
theorem D_w : D w = 0 := by
  funext i
  fin_cases i <;> simp [D, w]

/-! ## The twisted product and the Leibniz rule -/

/-- The twisted product `x . y = xy + alpha y * alpha x`. -/
def bsd (x y : A) : A := mul x y + mul (alpha y) (alpha x)

/-- `D` satisfies the twisted Leibniz rule: `D` is a braided-symmetric
derivation for `sigma_alpha`.  Checked over the 81 * 81 pairs. -/
theorem leibniz : ∀ x y : A, D (bsd x y) = bsd (D x) y + bsd x (D y) := by
  decide

/-- `D` is not a derivation: at `(v,w)` the identity would give `0 = t`. -/
theorem not_deriv : ¬ ∀ x y : A, D (mul x y) = mul (D x) y + mul x (D y) := by
  intro h
  have h1 := h v w
  have hvw : mul v w = 0 := by
    funext i
    fin_cases i <;> simp [mul, v, w]
  have hD0 : D 0 = 0 := by
    funext i
    fin_cases i <;> simp [D]
  have hrhs : mul (D v) w + mul v (D w) = t := by
    rw [D_v, D_w]
    funext i
    fin_cases i <;> simp [mul, v, w, t]
  rw [hvw, hD0, hrhs] at h1
  have hne : (0 : A) ≠ t := by
    intro hc
    have h0 := congrFun hc 1
    simp [t] at h0
  exact hne h1

/-- The Leibniz defect of `D` at `(v,w)` is `-t`. -/
theorem defect_vw : D (mul v w) - mul (D v) w - mul v (D w) = - t := by
  decide

/-- `(v + w)^2 = 0`, so `A_-` contains a nonzero square-zero element. -/
theorem skew_sq_zero : mul (v + w) (v + w) = 0 := by
  decide

end BSD.Remark46
