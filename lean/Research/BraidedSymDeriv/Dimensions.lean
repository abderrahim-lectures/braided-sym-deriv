/-
# The two dimension counts of Remark 4.6, as finrank statements

`dim BSDer^α = 3` and `dim Der^α = 2` for the four-dimensional `F₃`-algebra of
Remark 4.6 (basis `1, t, v, w` with `t² = 0`, `v² = w² = wv = t`, `vw = 0`,
`α` fixing `1, t` and negating `v, w`).  `Remark46.lean` proves the remark's
finite facts over `Fin 3` coefficients (its kernel `decide`s need the concrete
`Fin` arithmetic); here the same coordinate formulas are used over `ZMod 3`,
whose field structure supports the linear algebra the finrank statements need.

The bases (computed by the review's exact solver, verified here by membership
and spanning):  `Der^α` is spanned by

* `B₁ = (1 ↦ 0, t ↦ 2t, v ↦ v, w ↦ w)`,
* `B₂ = (1 ↦ 0, t ↦ t,  v ↦ w, w ↦ 2v + w)`;

`BSDer^α` is spanned by

* `T = (1 ↦ 0, t ↦ t, v ↦ w,  w ↦ 2w)`,
* `U₁ = (1 ↦ 0, t ↦ 0, v ↦ v + w, w ↦ 0)`,
* `U₂ = (1 ↦ 0, t ↦ 0, v ↦ 0,     w ↦ v + w)`.

The paper's own `D` (`D v = v + w`, all else `0`) is `U₁`: it lies in
`BSDer^α` and is a Jordan derivation, but not a derivation — so it is also the
witness that Corollary 3.5 needs semiprimeness (the algebra is not semiprime:
`t ≠ 0` and `t * (1) * t = t² = 0`).
-/
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Remark46Dim

abbrev K := ZMod 3
abbrev A := Fin 4 → K

/-! ## The algebra -/

/-- The multiplication of Remark 4.6, in coordinates `(a₀, a₁, a₂, a₃)` of
`a₀ · 1 + a₁ · t + a₂ · v + a₃ · w` — the same table as `Remark46.lean`. -/
def mul (x y : A) : A := fun i =>
  match i with
  | 0 => x 0 * y 0
  | 1 => x 0 * y 1 + x 1 * y 0 + x 2 * y 2 + x 3 * y 3 + x 3 * y 2
  | 2 => x 0 * y 2 + x 2 * y 0
  | 3 => x 0 * y 3 + x 3 * y 0

/-- The involution `α`: fixes `1, t`, negates `v, w`. -/
def alphaLin : A →ₗ[K] A where
  toFun x := fun i => match i with
    | 0 => x 0
    | 1 => x 1
    | 2 => -x 2
    | 3 => -x 3
  map_add' x y := by funext i; fin_cases i <;> simp [Pi.add_apply] <;> abel
  map_smul' a x := by funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

/-- The twisted product `x ·_σ y = xy + α(y)α(x)`. -/
def bsd (x y : A) : A := mul x y + mul (alphaLin y) (alphaLin x)

/-- The Jordan product `x ∘ y = xy + yx`. -/
def jordan (x y : A) : A := mul x y + mul y x

/-! ## Bilinearity -/

theorem mul_add (x y z : A) : mul (x + y) z = mul x z + mul y z := by
  funext k; fin_cases k <;> simp [mul, Pi.add_apply] <;> ring

theorem add_mul (x y z : A) : mul x (y + z) = mul x y + mul x z := by
  funext k; fin_cases k <;> simp [mul, Pi.add_apply] <;> ring

theorem mul_smul (c : K) (x y : A) : mul (c • x) y = c • mul x y := by
  funext k; fin_cases k <;> simp [mul, Pi.smul_apply, smul_eq_mul] <;> ring

theorem smul_mul (c : K) (x y : A) : mul x (c • y) = c • mul x y := by
  funext k; fin_cases k <;> simp [mul, Pi.smul_apply, smul_eq_mul] <;> ring

theorem bsd_add_l (x y z : A) : bsd (x + y) z = bsd x z + bsd y z := by
  simp only [bsd, mul_add, alphaLin.map_add, add_mul]
  abel

theorem bsd_add_r (x y z : A) : bsd x (y + z) = bsd x y + bsd x z := by
  simp only [bsd, add_mul, alphaLin.map_add, mul_add]
  abel

theorem bsd_smul_l (c : K) (x y : A) : bsd (c • x) y = c • bsd x y := by
  simp only [bsd, mul_smul, alphaLin.map_smul, smul_mul, smul_add]

theorem bsd_smul_r (c : K) (x y : A) : bsd x (c • y) = c • bsd x y := by
  simp only [bsd, smul_mul, alphaLin.map_smul, mul_smul, smul_add]

theorem jordan_add_l (x y z : A) : jordan (x + y) z = jordan x z + jordan y z := by
  simp only [jordan, mul_add, add_mul]
  abel

theorem jordan_add_r (x y z : A) : jordan x (y + z) = jordan x y + jordan x z := by
  simp only [jordan, add_mul, mul_add]
  abel

theorem jordan_smul_l (c : K) (x y : A) : jordan (c • x) y = c • jordan x y := by
  simp only [jordan, mul_smul, smul_mul, smul_add]

theorem jordan_smul_r (c : K) (x y : A) : jordan x (c • y) = c • jordan x y := by
  simp only [jordan, smul_mul, mul_smul, smul_add]

/-! ## The basis and the coordinate decomposition -/

/-- The basis vector `e i` (with `e 0 = 1`, `e 1 = t`, `e 2 = v`, `e 3 = w`). -/
def e (i : Fin 4) : A := fun k => if k = i then 1 else 0

theorem one_mul_vec (x : A) : mul (e 0) x = x := by
  funext k; fin_cases k <;> simp [mul, e]

theorem mul_one_vec (x : A) : mul x (e 0) = x := by
  funext k; fin_cases k <;> simp [mul, e]

theorem mul_zero_vec (x : A) : mul 0 x = 0 := by funext k; fin_cases k <;> simp [mul]

theorem zero_mul_vec (x : A) : mul x 0 = 0 := by funext k; fin_cases k <;> simp [mul]

/-- Every element is the sum of its coordinates times the basis. -/
theorem sum_eq (x : A) :
    x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3 = x := by
  funext k
  fin_cases k <;> simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem alphaLin_e0 : alphaLin (e 0) = e 0 := by
  funext k; fin_cases k <;> simp [alphaLin, e]

theorem alphaLin_e1 : alphaLin (e 1) = e 1 := by
  funext k; fin_cases k <;> simp [alphaLin, e]

theorem alphaLin_e2 : alphaLin (e 2) = -(e 2) := by
  funext k; fin_cases k <;> simp [alphaLin, e]

theorem alphaLin_e3 : alphaLin (e 3) = -(e 3) := by
  funext k; fin_cases k <;> simp [alphaLin, e]

theorem alphaLin_apply_0 (x : A) : alphaLin x 0 = x 0 := rfl
theorem alphaLin_apply_1 (x : A) : alphaLin x 1 = x 1 := rfl
theorem alphaLin_apply_2 (x : A) : alphaLin x 2 = -x 2 := rfl
theorem alphaLin_apply_3 (x : A) : alphaLin x 3 = -x 3 := rfl

/-! ## The map space and the three classes -/

/-- `D` is a derivation commuting with `α` (the paper's `Der(A)^α`). -/
def Derα (D : A →ₗ[K] A) : Prop :=
  (∀ x y, D (mul x y) = mul (D x) y + mul x (D y)) ∧ ∀ x, D (alphaLin x) = alphaLin (D x)

/-- `D` is a braided-symmetric derivation for `σ_α`, commuting with `α`. -/
def BSDerα (D : A →ₗ[K] A) : Prop :=
  (∀ x y, D (bsd x y) = bsd (D x) y + bsd x (D y)) ∧ ∀ x, D (alphaLin x) = alphaLin (D x)

/-- `D` is a Jordan derivation commuting with `α`. -/
def JDerα (D : A →ₗ[K] A) : Prop :=
  (∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y)) ∧ ∀ x, D (alphaLin x) = alphaLin (D x)

/-- A linear map from an explicit table of rows: `(linMap c) x = fun k => Σ i, c i k * x i`,
so `c i` is the image of the `i`-th basis vector. -/
def linMap (c : Fin 4 → Fin 4 → K) : A →ₗ[K] A where
  toFun x := fun k => ∑ i, c i k * x i
  map_add' x y := by
    funext k
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' a x := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [RingHom.id_apply]; ring

theorem linMap_apply (c : Fin 4 → Fin 4 → K) (x : A) (k : Fin 4) :
    linMap c x k = ∑ i, c i k * x i := rfl

theorem linMap_e (c : Fin 4 → Fin 4 → K) (i k : Fin 4) :
    linMap c (e i) k = c i k := by
  simp [linMap_apply, e, Finset.sum_ite_eq']

/-! ## The submodules of the three classes -/

theorem derα_zero : Derα 0 :=
  ⟨fun x y => by simp [mul_zero_vec, zero_mul_vec], fun x => by simp⟩

theorem derα_add {D E : A →ₗ[K] A} (hD : Derα D) (hE : Derα E) : Derα (D + E) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply]
    rw [hD.1, hE.1, mul_add, add_mul]
    abel
  · intro x
    simp only [LinearMap.add_apply]
    rw [hD.2, hE.2, map_add]

theorem derα_smul (c : K) {D : A →ₗ[K] A} (hD : Derα D) : Derα (c • D) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.smul_apply]
    rw [hD.1, smul_add, mul_smul, smul_mul]
  · intro x
    simp only [LinearMap.smul_apply]
    rw [hD.2, alphaLin.map_smul]

theorem bsderα_zero : BSDerα 0 :=
  ⟨fun x y => by simp [bsd, mul_zero_vec, zero_mul_vec], fun x => by simp⟩

theorem bsderα_add {D E : A →ₗ[K] A} (hD : BSDerα D) (hE : BSDerα E) : BSDerα (D + E) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply]
    rw [hD.1, hE.1, bsd_add_l, bsd_add_r]
    abel
  · intro x
    simp only [LinearMap.add_apply]
    rw [hD.2, hE.2, map_add]

theorem bsderα_smul (c : K) {D : A →ₗ[K] A} (hD : BSDerα D) : BSDerα (c • D) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.smul_apply]
    rw [hD.1, smul_add, bsd_smul_l, bsd_smul_r]
  · intro x
    simp only [LinearMap.smul_apply]
    rw [hD.2, alphaLin.map_smul]

theorem jderα_zero : JDerα 0 :=
  ⟨fun x y => by simp [jordan, mul_zero_vec, zero_mul_vec], fun x => by simp⟩

theorem jderα_add {D E : A →ₗ[K] A} (hD : JDerα D) (hE : JDerα E) : JDerα (D + E) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply]
    rw [hD.1, hE.1, jordan_add_l, jordan_add_r]
    abel
  · intro x
    simp only [LinearMap.add_apply]
    rw [hD.2, hE.2, map_add]

theorem jderα_smul (c : K) {D : A →ₗ[K] A} (hD : JDerα D) : JDerα (c • D) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.smul_apply]
    rw [hD.1, smul_add, jordan_smul_l, jordan_smul_r]
  · intro x
    simp only [LinearMap.smul_apply]
    rw [hD.2, alphaLin.map_smul]

def DerαSub : Submodule K (A →ₗ[K] A) where
  carrier := {D | Derα D}
  zero_mem' := derα_zero
  add_mem' hD hE := derα_add hD hE
  smul_mem' c _ hD := derα_smul c hD

def BSDerαSub : Submodule K (A →ₗ[K] A) where
  carrier := {D | BSDerα D}
  zero_mem' := bsderα_zero
  add_mem' hD hE := bsderα_add hD hE
  smul_mem' c _ hD := bsderα_smul c hD

def JDerαSub : Submodule K (A →ₗ[K] A) where
  carrier := {D | JDerα D}
  zero_mem' := jderα_zero
  add_mem' hD hE := jderα_add hD hE
  smul_mem' c _ hD := jderα_smul c hD

/-! ## The basis maps -/

/-- `Der^α` generator: `t ↦ 2t`, `v ↦ v`, `w ↦ w`. -/
def B₁ : A →ₗ[K] A :=
  linMap ![![0, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- `Der^α` generator: `t ↦ t`, `v ↦ w`, `w ↦ 2v + w`. -/
def B₂ : A →ₗ[K] A :=
  linMap ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![0, 0, 2, 1]]

/-- `BSDer^α` generator: `t ↦ t`, `v ↦ w`, `w ↦ 2w`. -/
def T : A →ₗ[K] A :=
  linMap ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2]]

/-- `BSDer^α` generator: `v ↦ v + w` (the paper's `D`). -/
def U₁ : A →ₗ[K] A :=
  linMap ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0]]

/-- `BSDer^α` generator: `w ↦ v + w`. -/
def U₂ : A →ₗ[K] A :=
  linMap ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1]]

/-! ## Two bilinear extension lemmas -/

/-- Two bilinear maps that agree on the sixteen basis pairs agree everywhere. -/
theorem bilinear_eq_of_basis {G H : A → A → A}
    (hGa : ∀ a b c, G (a + b) c = G a c + G b c) (hGk : ∀ (k : K) a b, G (k • a) b = k • G a b)
    (hGr : ∀ a b c, G a (b + c) = G a b + G a c) (hGk2 : ∀ (k : K) a b, G a (k • b) = k • G a b)
    (hHa : ∀ a b c, H (a + b) c = H a c + H b c) (hHk : ∀ (k : K) a b, H (k • a) b = k • H a b)
    (hHr : ∀ a b c, H a (b + c) = H a b + H a c) (hHk2 : ∀ (k : K) a b, H a (k • b) = k • H a b)
    (hb : ∀ i j, G (e i) (e j) = H (e i) (e j)) : ∀ a b, G a b = H a b := by
  intro a b
  conv_lhs => rw [← sum_eq a, ← sum_eq b]
  conv_rhs => rw [← sum_eq a, ← sum_eq b]
  simp only [hGa, hGk, hGr, hGk2, hHa, hHk, hHr, hHk2, hb]

/-- A linear map satisfying the `P`-Leibniz rule on the sixteen basis pairs
satisfies it on all pairs, for any bilinear `P`. -/
theorem leibniz_of_basis {D : A →ₗ[K] A} {P : A → A → A}
    (hPl : ∀ a b c, P (a + b) c = P a c + P b c) (hPk : ∀ (k : K) a b, P (k • a) b = k • P a b)
    (hPr : ∀ a b c, P a (b + c) = P a b + P a c) (hPk2 : ∀ (k : K) a b, P a (k • b) = k • P a b)
    (h : ∀ i j, D (P (e i) (e j)) = P (D (e i)) (e j) + P (e i) (D (e j))) :
    ∀ x y, D (P x y) = P (D x) y + P x (D y) := by
  refine bilinear_eq_of_basis ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro a b c; simp only [map_add, hPl] <;> abel
  · intro k a b; simp only [map_smul, hPk] <;> abel
  · intro a b c; simp only [map_add, hPr] <;> abel
  · intro k a b; simp only [map_smul, hPk2] <;> abel
  · intro a b c; simp only [map_add, hPl] <;> abel
  · intro k a b; simp only [map_smul, hPk, smul_add]
  · intro a b c; simp only [map_add, hPr] <;> abel
  · intro k a b; simp only [map_smul, hPk2, smul_add]

/-- A linear map commuting with `α` on the basis commutes with it everywhere. -/
theorem comm_of_basis {D : A →ₗ[K] A}
    (h : ∀ i, D (alphaLin (e i)) = alphaLin (D (e i))) : ∀ x, D (alphaLin x) = alphaLin (D x) := by
  intro x
  conv_lhs => rw [← sum_eq x]
  conv_rhs => rw [← sum_eq x]
  simp only [map_add, map_smul, h]

/-! ## Membership of the generators -/

theorem B₁_der : Derα B₁ := by
  refine ⟨leibniz_of_basis mul_add mul_smul add_mul smul_mul (fun i j => ?_),
          comm_of_basis (fun i => ?_)⟩
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;> decide
  · fin_cases i <;> ext k <;> fin_cases k <;> decide

theorem B₂_der : Derα B₂ := by
  refine ⟨leibniz_of_basis mul_add mul_smul add_mul smul_mul (fun i j => ?_),
          comm_of_basis (fun i => ?_)⟩
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;> decide
  · fin_cases i <;> ext k <;> fin_cases k <;> decide

theorem T_bsder : BSDerα T := by
  refine ⟨leibniz_of_basis bsd_add_l bsd_smul_l bsd_add_r bsd_smul_r (fun i j => ?_),
          comm_of_basis (fun i => ?_)⟩
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;> decide
  · fin_cases i <;> ext k <;> fin_cases k <;> decide

theorem U₁_bsder : BSDerα U₁ := by
  refine ⟨leibniz_of_basis bsd_add_l bsd_smul_l bsd_add_r bsd_smul_r (fun i j => ?_),
          comm_of_basis (fun i => ?_)⟩
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;> decide
  · fin_cases i <;> ext k <;> fin_cases k <;> decide

theorem U₂_bsder : BSDerα U₂ := by
  refine ⟨leibniz_of_basis bsd_add_l bsd_smul_l bsd_add_r bsd_smul_r (fun i j => ?_),
          comm_of_basis (fun i => ?_)⟩
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;> decide
  · fin_cases i <;> ext k <;> fin_cases k <;> decide

/-! ## Spanning: the two dimension counts -/

/-! ## Closed products on the needed basis pairs -/

private lemma mul_e00 : mul (e 0) (e 0) = e 0 := one_mul_vec (e 0)
private lemma mul_e12 : mul (e 1) (e 2) = 0 := by funext k; fin_cases k <;> decide
private lemma mul_e22 : mul (e 2) (e 2) = e 1 := by funext k; fin_cases k <;> decide
private lemma mul_e23 : mul (e 2) (e 3) = 0 := by funext k; fin_cases k <;> decide
private lemma mul_e32 : mul (e 3) (e 2) = e 1 := by funext k; fin_cases k <;> decide

private lemma neg_eq_two_mul (x : K) : -x = 2 * x := by
  have h2 : (2 : K) = -1 := by decide
  rw [h2, neg_one_mul]

/-- In `ZMod 3`, `x = -x` forces `x = 0`. -/
private lemma eq_zero_of_eq_neg (x : K) (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := by nth_rewrite 2 [h]; exact add_neg_cancel x
  have h3 : (2 : K) * x = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp h3).resolve_left (by decide)

/-! ## Row values of the generators -/

theorem B₁_e0 : B₁ (e 0) = 0 := by funext k; fin_cases k <;> decide
theorem B₁_e1 : B₁ (e 1) = 2 • e 1 := by funext k; fin_cases k <;> decide
theorem B₁_e2 : B₁ (e 2) = e 2 := by funext k; fin_cases k <;> decide
theorem B₁_e3 : B₁ (e 3) = e 3 := by funext k; fin_cases k <;> decide
theorem B₂_e0 : B₂ (e 0) = 0 := by funext k; fin_cases k <;> decide
theorem B₂_e1 : B₂ (e 1) = e 1 := by funext k; fin_cases k <;> decide
theorem B₂_e2 : B₂ (e 2) = e 3 := by funext k; fin_cases k <;> decide
theorem B₂_e3 : B₂ (e 3) = 2 • e 2 + e 3 := by funext k; fin_cases k <;> decide

/-! ## The combination, evaluated on the basis -/

theorem comb_e0 (a b : K) : (a • B₁ + b • B₂) (e 0) = 0 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, B₁_e0, B₂_e0]
  simp

theorem comb_e1 (a b : K) : (a • B₁ + b • B₂) (e 1) = (2 * a + b) • e 1 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, B₁_e1, B₂_e1]
  funext k
  fin_cases k <;> simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem comb_e2 (a b : K) : (a • B₁ + b • B₂) (e 2) = a • e 2 + b • e 3 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, B₁_e2, B₂_e2]

theorem comb_e3 (a b : K) : (a • B₁ + b • B₂) (e 3) = b • (2 • e 2) + (a + b) • e 3 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, B₁_e3, B₂_e3, smul_add]
  funext k
  fin_cases k <;> simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem comb_e1_0 (a b : K) : (a • B₁ + b • B₂) (e 1) 0 = 0 := by
  rw [comb_e1]; simp [e, Pi.smul_apply, smul_eq_mul]

theorem comb_e1_1 (a b : K) : (a • B₁ + b • B₂) (e 1) 1 = 2 * a + b := by
  rw [comb_e1]; simp [e, Pi.smul_apply, smul_eq_mul]; ring

theorem comb_e1_2 (a b : K) : (a • B₁ + b • B₂) (e 1) 2 = 0 := by
  rw [comb_e1]; simp [e, Pi.smul_apply, smul_eq_mul]

theorem comb_e1_3 (a b : K) : (a • B₁ + b • B₂) (e 1) 3 = 0 := by
  rw [comb_e1]; simp [e, Pi.smul_apply, smul_eq_mul]

theorem comb_e2_2 (a b : K) : (a • B₁ + b • B₂) (e 2) 2 = a := by
  rw [comb_e2]; simp [e, Pi.smul_apply, smul_eq_mul]

theorem comb_e2_3 (a b : K) : (a • B₁ + b • B₂) (e 2) 3 = b := by
  rw [comb_e2]; simp [e, Pi.smul_apply, smul_eq_mul]

theorem comb_e3_2 (a b : K) : (a • B₁ + b • B₂) (e 3) 2 = 2 * b := by
  rw [comb_e3]; simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem comb_e3_3 (a b : K) : (a • B₁ + b • B₂) (e 3) 3 = a + b := by
  rw [comb_e3]; simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## Spanning: `Der^α` is exactly `span {B₁, B₂}` -/

/-- `Der^α` is exactly `span {B₁, B₂}`. -/
theorem derα_eq_span :
    (DerαSub : Set (A →ₗ[K] A)) = (Submodule.span K ({B₁, B₂} : Set (A →ₗ[K] A)) : Set _) := by
  refine Set.Subset.antisymm (fun D hD => ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨hleib, hcomm⟩ := hD
    -- The unit: `D 1 = 0`.
    have hD0 : D (e 0) = 0 := by
      have h1 : D (e 0) = D (e 0) + D (e 0) := by
        simpa [mul_e00, one_mul_vec, mul_one_vec] using hleib (e 0) (e 0)
      funext k
      simp only [Pi.zero_apply]
      have h1k : (D (e 0)) k = (D (e 0)) k + (D (e 0)) k := by simpa using congrFun h1 k
      exact (add_left_cancel (show (D (e 0)) k + 0 = (D (e 0)) k + (D (e 0)) k by
        simpa using h1k)).symm
    have hα1 : alphaLin (e 1) = e 1 := alphaLin_e1
    have hα2 : alphaLin (e 2) = -(e 2) := alphaLin_e2
    have hα3 : alphaLin (e 3) = -(e 3) := alphaLin_e3
    -- `D t` has zero `1`, `v`, `w` coordinates.
    have c0 : (D (e 1)) 0 = 0 := by
      have h := hleib (e 1) (e 2)
      rw [mul_e12, map_zero] at h
      have h2 := congrFun h 2
      simp (config := { decide := true }) only [mul, e, Pi.add_apply, Pi.zero_apply,
        ite_true, ite_false] at h2
      simp at h2
      exact h2.symm
    have c2 : (D (e 1)) 2 = 0 := by
      have h := hcomm (e 1)
      rw [hα1] at h
      have h2 := congrFun h 2
      simp only [alphaLin_apply_2] at h2
      exact eq_zero_of_eq_neg _ h2
    have c3 : (D (e 1)) 3 = 0 := by
      have h := hcomm (e 1)
      rw [hα1] at h
      have h3 := congrFun h 3
      simp only [alphaLin_apply_3] at h3
      exact eq_zero_of_eq_neg _ h3
    -- `D v` and `D w` have zero `1`, `t` coordinates.
    have v0 : (D (e 2)) 0 = 0 := by
      have h := hcomm (e 2)
      rw [hα2, map_neg] at h
      have h2 := congrFun h 0
      simp only [Pi.neg_apply, alphaLin_apply_0] at h2
      exact eq_zero_of_eq_neg _ h2.symm
    have v1 : (D (e 2)) 1 = 0 := by
      have h := hcomm (e 2)
      rw [hα2, map_neg] at h
      have h2 := congrFun h 1
      simp only [Pi.neg_apply, alphaLin_apply_1] at h2
      exact eq_zero_of_eq_neg _ h2.symm
    have w0 : (D (e 3)) 0 = 0 := by
      have h := hcomm (e 3)
      rw [hα3, map_neg] at h
      have h2 := congrFun h 0
      simp only [Pi.neg_apply, alphaLin_apply_0] at h2
      exact eq_zero_of_eq_neg _ h2.symm
    have w1 : (D (e 3)) 1 = 0 := by
      have h := hcomm (e 3)
      rw [hα3, map_neg] at h
      have h2 := congrFun h 1
      simp only [Pi.neg_apply, alphaLin_apply_1] at h2
      exact eq_zero_of_eq_neg _ h2.symm
    -- The three linear relations on the remaining coordinates.
    have E1 : (D (e 1)) 1 = 2 * (D (e 2)) 2 + (D (e 2)) 3 := by
      have h := hleib (e 2) (e 2)
      rw [mul_e22] at h
      have h2 := congrFun h 1
      simp (config := { decide := true }) only [mul, e, Pi.add_apply, ite_true, ite_false] at h2
      simp at h2
      linear_combination h2
    have E2 : (D (e 3)) 2 = -(D (e 2)) 3 := by
      have h := hleib (e 2) (e 3)
      rw [mul_e23, map_zero] at h
      have h2 := congrFun h 1
      simp (config := { decide := true }) only [mul, e, Pi.add_apply, Pi.zero_apply,
        ite_true, ite_false] at h2
      simp at h2
      linear_combination (-1) * h2
    have E3 : (D (e 3)) 3 = (D (e 2)) 2 + (D (e 2)) 3 := by
      have h := hleib (e 3) (e 2)
      rw [mul_e32] at h
      have h2 := congrFun h 1
      simp (config := { decide := true }) only [mul, e, Pi.add_apply, ite_true, ite_false] at h2
      simp at h2
      rw [E1, E2] at h2
      linear_combination (-1) * h2
    -- The combination: coefficients read off `D v`.
    have hb0 : D (e 0) = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 0) := by
      rw [hD0, comb_e0]
    have hb1 : D (e 1) = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 1) := by
      rw [comb_e1]
      funext k
      fin_cases k
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact c0
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
        try rw [E1]; try ring
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact c2
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact c3
    have hb2 : D (e 2) = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 2) := by
      rw [comb_e2]
      funext k
      fin_cases k
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact v0
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact v1
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; try ring
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; try ring
    have hb3 : D (e 3) = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 3) := by
      rw [comb_e3]
      funext k
      fin_cases k
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact w0
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]; exact w1
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
        try rw [E2, neg_eq_two_mul]; try ring
      · simp (config := { decide := true }) only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
        try rw [E3]; try ring
    have hcomb : D = (D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂ := by
      ext x
      have hx : x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3 = x := sum_eq x
      calc D x = D (x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3) := by rw [hx]
        _ = x 0 • D (e 0) + x 1 • D (e 1) + x 2 • D (e 2) + x 3 • D (e 3) := by
              simp only [map_add, map_smul]
        _ = x 0 • ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 0)
              + x 1 • ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 1)
              + x 2 • ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 2)
              + x 3 • ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (e 3) := by
              rw [hb0, hb1, hb2, hb3]
        _ = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) (x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3) := by
              simp only [map_add, map_smul]
        _ = ((D (e 2)) 2 • B₁ + (D (e 2)) 3 • B₂) x := by rw [hx]
    rw [hcomb]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (by simp))
      (Submodule.smul_mem _ _ (by simp))
  · intro D hD
    rcases hD with rfl | rfl
    · exact B₁_der
    · exact B₂_der

end Remark46Dim
