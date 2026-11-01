/-
# Example 4.5(b): the dual numbers `K[ε]/(ε²)`, `char K ≠ 2` versus `char K = 2`

The second half of Example 4.5 of the paper: on `A = K[ε]/(ε²)` with
`α(ε) = -ε`, the map `D(a + bε) = bε` is a derivation, an `α`-derivation and
commutes with `α`, so it lies in both `Der_α(A)` and `BSDer_{σ_α}(A)^α`.  When
`char K ≠ 2` the derivations, the `α`-derivations and the `α`-commuting
braided-symmetric derivations are all the one-dimensional space spanned by
`ε ↦ ε`, so the two classes coincide; when `char K = 2` the involution `α` is
the identity and the twisted product `x ·_σ y = xy + α(x)α(y)` vanishes, so
`BSDer_{σ_α}(A)` is all of `End_K(A)` (four-dimensional), while
`Der_α(A) = Der(A)` is two-dimensional.

The algebra is the product type `K × K` with `(a, b) * (c, d) = (ac, ad + bc)`;
multiplication is commutative and `ε² = 0`.  Everything is a coordinate
computation, and the two characteristic regimes are the hypotheses
`(2 : K) ≠ 0` respectively `(2 : K) = 0`.

This closes the last numbered result of the paper with no Lean counterpart
(`RESULTS.md`).
-/
import Mathlib

namespace Ex45b

variable {K : Type*} [Field K]

/-- `K[ε]/(ε²)`, in coordinates `a + bε ↦ (a, b)`. -/
abbrev A (K : Type*) : Type _ := K × K

/-- The product of the dual numbers. -/
def mul (x y : A K) : A K := (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

@[simp] theorem mul_fst (x y : A K) : (mul x y).1 = x.1 * y.1 := rfl

@[simp] theorem mul_snd (x y : A K) : (mul x y).2 = x.1 * y.2 + x.2 * y.1 := rfl

@[simp] theorem mul_zero_left (y : A K) : mul 0 y = 0 := by ext <;> simp [mul]

@[simp] theorem mul_zero_right (x : A K) : mul x 0 = 0 := by ext <;> simp [mul]

theorem mul_comm' (x y : A K) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

theorem mul_add_l (x y z : A K) : mul (x + y) z = mul x z + mul y z := by
  ext <;> simp [mul, add_mul] <;> ring

theorem mul_add_r (x y z : A K) : mul x (y + z) = mul x y + mul x z := by
  ext <;> simp [mul, add_mul] <;> ring

theorem mul_smul_l (c : K) (x y : A K) : mul (c • x) y = c • mul x y := by
  ext <;> simp [mul, mul_add] <;> ring

theorem mul_smul_r (c : K) (x y : A K) : mul x (c • y) = c • mul x y := by
  ext <;> simp [mul, mul_add] <;> ring

/-- The involution `α(a + bε) = a - bε`. -/
def alphaLin : A K →ₗ[K] A K where
  toFun x := (x.1, -x.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem alphaLin_fst (x : A K) : (alphaLin x).1 = x.1 := rfl

@[simp] theorem alphaLin_snd (x : A K) : (alphaLin x).2 = -x.2 := rfl

theorem alphaLin_one : alphaLin (1, 0) = ((1, 0) : A K) := by ext <;> simp

theorem alphaLin_eps : alphaLin (0, 1) = ((0, -1) : A K) := by ext <;> simp

theorem alphaLin_invol (x : A K) : alphaLin (alphaLin x) = x := by ext <;> simp

/-- `α` is an algebra map: `α(xy) = α(x)α(y)`. -/
theorem alphaLin_mul (x y : A K) : alphaLin (mul x y) = mul (alphaLin x) (alphaLin y) := by
  ext <;> simp [mul] <;> ring

/-- The twisted product `x ·_σ y = xy + α(x)α(y)` of `σ_α`. -/
def tw (x y : A K) : A K := mul x y + mul (alphaLin x) (alphaLin y)

/-- On the dual numbers the twisted product only keeps the scalar part. -/
theorem tw_eq (x y : A K) : tw x y = (2 * (x.1 * y.1), 0) := by
  ext
  · simp [tw, mul]; ring
  · simp [tw, mul]; ring

theorem tw_add_l (x y z : A K) : tw (x + y) z = tw x z + tw y z := by
  simp only [tw, alphaLin.map_add, mul_add_l, add_add_add_comm]

theorem tw_add_r (x y z : A K) : tw x (y + z) = tw x y + tw x z := by
  simp only [tw, alphaLin.map_add, mul_add_r, add_add_add_comm]

theorem tw_smul_l (c : K) (x y : A K) : tw (c • x) y = c • tw x y := by
  simp only [tw, alphaLin.map_smul, mul_smul_l, smul_add]

theorem tw_smul_r (c : K) (x y : A K) : tw x (c • y) = c • tw x y := by
  simp only [tw, alphaLin.map_smul, mul_smul_r, smul_add]

theorem tw_comm (x y : A K) : tw x y = tw y x := by
  ext <;> simp [tw, mul] <;> ring

/-- In characteristic two the twisted product vanishes identically. -/
theorem tw_eq_zero (h2 : (2 : K) = 0) (x y : A K) : tw x y = 0 := by
  rw [tw_eq, h2, zero_mul]
  rfl

/-! ## The three derivation classes -/

/-- Derivations of the dual numbers. -/
def Der (K : Type*) [Field K] (D : A K →ₗ[K] A K) : Prop :=
  ∀ x y, D (mul x y) = mul (D x) y + mul x (D y)

/-- `α`-derivations: `D(xy) = D(x)α(y) + α(x)D(y)`. -/
def ADer (K : Type*) [Field K] (D : A K →ₗ[K] A K) : Prop :=
  ∀ x y, D (mul x y) = mul (D x) (alphaLin y) + mul (alphaLin x) (D y)

/-- Braided-symmetric derivations for `σ_α`. -/
def BSDer (K : Type*) [Field K] (D : A K →ₗ[K] A K) : Prop :=
  ∀ x y, D (tw x y) = tw (D x) y + tw x (D y)

/-- Braided-symmetric derivations for `σ_α` that commute with `α`. -/
def BSDerα (K : Type*) [Field K] (D : A K →ₗ[K] A K) : Prop :=
  BSDer K D ∧ ∀ x, D (alphaLin x) = alphaLin (D x)

theorem der_zero : Der K (0 : A K →ₗ[K] A K) := fun x y => by simp

theorem der_add {D E : A K →ₗ[K] A K} (hD : Der K D) (hE : Der K E) : Der K (D + E) := by
  intro x y
  simp only [LinearMap.add_apply, hD x y, hE x y, mul_add_l, mul_add_r]
  abel

theorem der_smul (c : K) {D : A K →ₗ[K] A K} (hD : Der K D) : Der K (c • D) := by
  intro x y
  simp only [LinearMap.smul_apply, hD x y, mul_smul_l, mul_smul_r, smul_add]

theorem ader_zero : ADer K (0 : A K →ₗ[K] A K) := fun x y => by simp

theorem ader_add {D E : A K →ₗ[K] A K} (hD : ADer K D) (hE : ADer K E) : ADer K (D + E) := by
  intro x y
  simp only [LinearMap.add_apply, hD x y, hE x y, mul_add_l, mul_add_r]
  abel

theorem ader_smul (c : K) {D : A K →ₗ[K] A K} (hD : ADer K D) : ADer K (c • D) := by
  intro x y
  simp only [LinearMap.smul_apply, hD x y, mul_smul_l, mul_smul_r, smul_add]

theorem bsder_zero : BSDer K (0 : A K →ₗ[K] A K) := fun x y => by simp [tw]

theorem bsder_add {D E : A K →ₗ[K] A K} (hD : BSDer K D) (hE : BSDer K E) : BSDer K (D + E) := by
  intro x y
  simp only [LinearMap.add_apply, hD x y, hE x y, tw_add_l, tw_add_r]
  abel

theorem bsder_smul (c : K) {D : A K →ₗ[K] A K} (hD : BSDer K D) : BSDer K (c • D) := by
  intro x y
  simp only [LinearMap.smul_apply, hD x y, tw_smul_l, tw_smul_r, smul_add]

/-- The derivations, as a subspace of `End_K(A)`. -/
def DerSub (K : Type*) [Field K] : Submodule K (A K →ₗ[K] A K) where
  carrier := {D : A K →ₗ[K] A K | Der K D}
  zero_mem' := der_zero
  add_mem' hD hE := der_add hD hE
  smul_mem' c _ hD := der_smul c hD

/-- The `α`-derivations, as a subspace of `End_K(A)`. -/
def ADerSub (K : Type*) [Field K] : Submodule K (A K →ₗ[K] A K) where
  carrier := {D : A K →ₗ[K] A K | ADer K D}
  zero_mem' := ader_zero
  add_mem' hD hE := ader_add hD hE
  smul_mem' c _ hD := ader_smul c hD

/-- The braided-symmetric derivations, as a subspace of `End_K(A)`. -/
def BSDerSub (K : Type*) [Field K] : Submodule K (A K →ₗ[K] A K) where
  carrier := {D : A K →ₗ[K] A K | BSDer K D}
  zero_mem' := bsder_zero
  add_mem' hD hE := bsder_add hD hE
  smul_mem' c _ hD := bsder_smul c hD

/-- The `α`-commuting braided-symmetric derivations. -/
def BSDerαSub (K : Type*) [Field K] : Submodule K (A K →ₗ[K] A K) where
  carrier := {D : A K →ₗ[K] A K | BSDerα K D}
  zero_mem' := ⟨bsder_zero, fun x => by simp⟩
  add_mem' hD hE :=
    ⟨bsder_add hD.1 hE.1, fun x => by
      simp only [LinearMap.add_apply, hD.2 x, hE.2 x, map_add]⟩
  smul_mem' c _ hD :=
    ⟨bsder_smul c hD.1, fun x => by
      simp only [LinearMap.smul_apply, hD.2 x, map_smul]⟩

/-! ## The candidate maps -/

/-- `ε ↦ ε`, that is `a + bε ↦ bε`: the paper's `D`. -/
def Dε (K : Type*) [Field K] : A K →ₗ[K] A K where
  toFun x := (0, x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem Dε_apply (x : A K) : Dε K x = (0, x.2) := rfl

@[simp] theorem Dε_fst (x : A K) : (Dε K x).1 = 0 := rfl

@[simp] theorem Dε_snd (x : A K) : (Dε K x).2 = x.2 := rfl

/-- `a + bε ↦ b`: the second basis vector of the derivations in characteristic two. -/
def E₁ (K : Type*) [Field K] : A K →ₗ[K] A K where
  toFun x := (x.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem E₁_apply (x : A K) : E₁ K x = (x.2, 0) := rfl

@[simp] theorem E₁_fst (x : A K) : (E₁ K x).1 = x.2 := rfl

@[simp] theorem E₁_snd (x : A K) : (E₁ K x).2 = 0 := rfl

theorem Dε_der : Der K (Dε K) := by
  intro x y
  ext <;> simp [mul] <;> ring

theorem Dε_ader : ADer K (Dε K) := by
  intro x y
  ext <;> simp [mul] <;> ring

theorem Dε_comm : ∀ x, Dε K (alphaLin x) = alphaLin (Dε K x) := by
  intro x
  ext <;> simp

theorem Dε_bsder : BSDer K (Dε K) := by
  intro x y
  ext <;> simp [tw, mul] <;> ring

theorem Dε_mem (K : Type*) [Field K] : (Dε K) ∈ BSDerαSub K := ⟨Dε_bsder, Dε_comm⟩

theorem Dε_mem_der (K : Type*) [Field K] : (Dε K) ∈ DerSub K := Dε_der

theorem Dε_mem_ader (K : Type*) [Field K] : (Dε K) ∈ ADerSub K := Dε_ader

/-- In `char K = 2` the map `a + bε ↦ b` is a derivation. -/
theorem E₁_der_of_char_two (h2 : (2 : K) = 0) : Der K (E₁ K) := by
  intro x y
  ext
  · simp [mul, E₁]
    ring
  · simp [mul, E₁]
    linear_combination (-(x.2 * y.2)) * h2

/-- In `char K = 2` the map `a + bε ↦ b` is also an `α`-derivation (`α = id`). -/
theorem E₁_ader_of_char_two (h2 : (2 : K) = 0) : ADer K (E₁ K) := by
  intro x y
  ext
  · simp [mul, E₁]
    ring
  · simp [mul, E₁, alphaLin_eps]
    linear_combination (x.2 * y.2) * h2

/-! ## Coordinates and the two criteria -/

/-- A linear endomorphism of the dual numbers is fixed by its two values. -/
theorem apply_coord (D : A K →ₗ[K] A K) (x : A K) :
    D x =
      (x.1 * (D (1, 0)).1 + x.2 * (D (0, 1)).1,
        x.1 * (D (1, 0)).2 + x.2 * (D (0, 1)).2) := by
  have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul]
  ext <;> simp [smul_eq_mul]

/-- Two linear endomorphisms agreeing on `1` and `ε` are equal. -/
theorem lin_eq_of_basis {F G : A K →ₗ[K] A K} (h0 : F (1, 0) = G (1, 0))
    (h1 : F (0, 1) = G (0, 1)) : F = G := by
  refine LinearMap.ext fun x => ?_
  rw [apply_coord F x, apply_coord G x, h0, h1]

theorem eq_zero_of_two_mul (h2 : (2 : K) ≠ 0) {x : K} (h : 2 * x = 0) : x = 0 := by
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd h' h2
  · exact h'

/-- A derivation kills `1` and sends `ε` into `2`-torsion. -/
theorem der_coord {D : A K →ₗ[K] A K} (hD : Der K D) :
    D (1, 0) = 0 ∧ 2 * (D (0, 1)).1 = 0 := by
  have h1 := hD (1, 0) (1, 0)
  have h2 := hD (0, 1) (0, 1)
  rw [show mul (1, 0) (1, 0) = ((1, 0) : A K) from by ext <;> simp [mul]] at h1
  rw [show mul (0, 1) (0, 1) = (0 : A K) from by ext <;> simp [mul], map_zero] at h2
  have h1c : D (1, 0) = (2 * (D (1, 0)).1, 2 * (D (1, 0)).2) := by
    conv_lhs => rw [h1]
    ext <;> simp [mul] <;> ring
  have hfst : (D (1, 0)).1 = 2 * (D (1, 0)).1 := by
    simpa using congrArg Prod.fst h1c
  have hsnd : (D (1, 0)).2 = 2 * (D (1, 0)).2 := by
    simpa using congrArg Prod.snd h1c
  have hp : (D (1, 0)).1 = 0 := by linear_combination (-1) * hfst
  have hq : (D (1, 0)).2 = 0 := by linear_combination (-1) * hsnd
  refine ⟨by ext <;> simp [hp, hq], ?_⟩
  have h2c : (mul (D (0, 1)) (0, 1) + mul (0, 1) (D (0, 1))).2 = 0 := by
    rw [← h2]; rfl
  have h2f : (mul (D (0, 1)) (0, 1) + mul (0, 1) (D (0, 1))).2
      = 2 * (D (0, 1)).1 := by
    simp [mul]; ring
  rw [h2f] at h2c
  exact h2c

/-- An `α`-derivation kills `1` and sends `ε` into `2`-torsion. -/
theorem ader_coord {D : A K →ₗ[K] A K} (hD : ADer K D) :
    D (1, 0) = 0 ∧ 2 * (D (0, 1)).1 = 0 := by
  have h1 := hD (1, 0) (1, 0)
  have h2 := hD (0, 1) (0, 1)
  rw [show mul (1, 0) (1, 0) = ((1, 0) : A K) from by ext <;> simp [mul], alphaLin_one] at h1
  rw [show mul (0, 1) (0, 1) = (0 : A K) from by ext <;> simp [mul], alphaLin_eps,
    map_zero] at h2
  have h1c : D (1, 0) = (2 * (D (1, 0)).1, 2 * (D (1, 0)).2) := by
    conv_lhs => rw [h1]
    ext <;> simp [mul] <;> ring
  have hfst : (D (1, 0)).1 = 2 * (D (1, 0)).1 := by
    simpa using congrArg Prod.fst h1c
  have hsnd : (D (1, 0)).2 = 2 * (D (1, 0)).2 := by
    simpa using congrArg Prod.snd h1c
  have hp : (D (1, 0)).1 = 0 := by linear_combination (-1) * hfst
  have hq : (D (1, 0)).2 = 0 := by linear_combination (-1) * hsnd
  refine ⟨by ext <;> simp [hp, hq], ?_⟩
  have h2c : (mul (D (0, 1)) (0, -1) + mul (0, -1) (D (0, 1))).2 = 0 := by
    rw [← h2]; rfl
  have h2f : (mul (D (0, 1)) (0, -1) + mul (0, -1) (D (0, 1))).2
      = -(2 * (D (0, 1)).1) := by
    simp [mul]; ring
  rw [h2f] at h2c
  linear_combination (-1) * h2c

/-! ## Characteristic different from two: all three classes are spanned by `Dε` -/

/-- In `char K ≠ 2` an `α`-commuting braided-symmetric derivation is a multiple
of `ε ↦ ε`. -/
theorem bsderα_apply (h2 : (2 : K) ≠ 0) {D : A K →ₗ[K] A K} (hD : BSDerα K D) :
    D = (D (0, 1)).2 • (Dε K) := by
  obtain ⟨hleib, hcomm⟩ := hD
  -- `α`-commutation: the `ε`-part of `D 1` and the scalar part of `D ε` vanish
  have hq2 : 2 * (D (1, 0)).2 = 0 := by
    have h := congrArg (fun x => x.2) (hcomm (1, 0))
    rw [alphaLin_one, alphaLin_snd] at h
    linear_combination h
  have hq : (D (1, 0)).2 = 0 := eq_zero_of_two_mul h2 hq2
  have hr2 : 2 * (D (0, 1)).1 = 0 := by
    have h := congrArg (fun x => x.1) (hcomm (0, 1))
    rw [alphaLin_eps, alphaLin_fst] at h
    rw [apply_coord D ((0 : K), (-1 : K))] at h
    norm_num at h
    linear_combination (-1) * h
  have hr : (D (0, 1)).1 = 0 := eq_zero_of_two_mul h2 hr2
  -- the twisted rule at `(1, 1)`: the scalar part of `D 1` vanishes too
  have hp2 : 2 * (D (1, 0)).1 = 0 := by
    have h := hleib (1, 0) (1, 0)
    have htw : tw (1, 0) (1, 0) = ((2 : K), 0) := by
      rw [tw_eq]; ext <;> simp
    rw [htw, tw_eq, tw_eq] at h
    have hL : D ((2 : K), 0) = (2 * (D (1, 0)).1, 2 * (D (1, 0)).2) := by
      rw [apply_coord D ((2 : K), (0 : K))]
      simp
    have h1 := congrArg Prod.fst h
    rw [hL] at h1
    simp only [Prod.fst_add] at h1
    linear_combination (-1) * h1
  have hp : (D (1, 0)).1 = 0 := eq_zero_of_two_mul h2 hp2
  refine lin_eq_of_basis ?_ ?_
  · rw [show D (1, 0) = 0 from by ext <;> simp [hp, hq],
      show ((D (0, 1)).2 • (Dε K)) (1, 0) = 0 from by simp]
  · rw [show ((D (0, 1)).2 • (Dε K)) (0, 1) = (D (0, 1)).2 • (0, 1) from by simp]
    ext <;> simp [hr]

theorem der_apply (h2 : (2 : K) ≠ 0) {D : A K →ₗ[K] A K} (hD : Der K D) :
    D = (D (0, 1)).2 • (Dε K) := by
  obtain ⟨h0, h2'⟩ := der_coord hD
  have hr : (D (0, 1)).1 = 0 := eq_zero_of_two_mul h2 h2'
  refine lin_eq_of_basis ?_ ?_
  · rw [h0, show ((D (0, 1)).2 • (Dε K)) (1, 0) = 0 from by simp]
  · rw [show ((D (0, 1)).2 • (Dε K)) (0, 1) = (D (0, 1)).2 • (0, 1) from by simp]
    ext <;> simp [hr]

theorem ader_apply (h2 : (2 : K) ≠ 0) {D : A K →ₗ[K] A K} (hD : ADer K D) :
    D = (D (0, 1)).2 • (Dε K) := by
  obtain ⟨h0, h2'⟩ := ader_coord hD
  have hr : (D (0, 1)).1 = 0 := eq_zero_of_two_mul h2 h2'
  refine lin_eq_of_basis ?_ ?_
  · rw [h0, show ((D (0, 1)).2 • (Dε K)) (1, 0) = 0 from by simp]
  · rw [show ((D (0, 1)).2 • (Dε K)) (0, 1) = (D (0, 1)).2 • (0, 1) from by simp]
    ext <;> simp [hr]

theorem singleton_eq_range (K : Type*) [Field K] : ({Dε K} : Set (A K →ₗ[K] A K)) = Set.range ![Dε K] := by
  ext F
  constructor
  · intro h
    exact ⟨0, by simpa using h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    rfl

theorem linIndep_Dε (K : Type*) [Field K] : LinearIndependent K (![Dε K] : Fin 1 → (A K →ₗ[K] A K)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  intro i
  fin_cases i
  have h := congrArg (fun (F : A K →ₗ[K] A K) => (F (0, 1)).2) hg
  simpa using h

theorem bsderαSub_eq_span (h2 : (2 : K) ≠ 0) :
    BSDerαSub K = Submodule.span K ({Dε K} : Set (A K →ₗ[K] A K)) := by
  refine le_antisymm (fun D hD => ?_) (Submodule.span_le.2 ?_)
  · rw [bsderα_apply h2 hD]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro D hD
    rw [Set.mem_singleton_iff] at hD
    rw [hD]
    exact Dε_mem K

theorem derSub_eq_span (h2 : (2 : K) ≠ 0) :
    DerSub K = Submodule.span K ({Dε K} : Set (A K →ₗ[K] A K)) := by
  refine le_antisymm (fun D hD => ?_) (Submodule.span_le.2 ?_)
  · rw [der_apply h2 hD]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro D hD
    rw [Set.mem_singleton_iff] at hD
    rw [hD]
    exact Dε_mem_der K

theorem aderSub_eq_span (h2 : (2 : K) ≠ 0) :
    ADerSub K = Submodule.span K ({Dε K} : Set (A K →ₗ[K] A K)) := by
  refine le_antisymm (fun D hD => ?_) (Submodule.span_le.2 ?_)
  · rw [ader_apply h2 hD]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro D hD
    rw [Set.mem_singleton_iff] at hD
    rw [hD]
    exact Dε_mem_ader K

/-- `dim BSDer_{σ_α}(A)^α = 1` in characteristic different from two. -/
theorem finrank_bsderαSub (h2 : (2 : K) ≠ 0) : Module.finrank K (BSDerαSub K) = 1 := by
  rw [bsderαSub_eq_span h2, singleton_eq_range K, finrank_span_eq_card (linIndep_Dε K)]
  simp

/-- `dim Der_α(A) = dim Der(A) = 1` in characteristic different from two. -/
theorem finrank_derSub (h2 : (2 : K) ≠ 0) : Module.finrank K (DerSub K) = 1 := by
  rw [derSub_eq_span h2, singleton_eq_range K, finrank_span_eq_card (linIndep_Dε K)]
  simp

theorem finrank_aderSub (h2 : (2 : K) ≠ 0) : Module.finrank K (ADerSub K) = 1 := by
  rw [aderSub_eq_span h2, singleton_eq_range K, finrank_span_eq_card (linIndep_Dε K)]
  simp

/-! ## Characteristic two: the twisted class is everything, the derivations are
two-dimensional -/

theorem bsderSub_eq_top (h2 : (2 : K) = 0) : BSDerSub K = ⊤ := by
  refine le_antisymm (fun _ _ => Submodule.mem_top) (fun D _ x y => ?_)
  rw [tw_eq_zero h2, tw_eq_zero h2, tw_eq_zero h2, map_zero, add_zero]

theorem derSub_eq_span_of_char_two (h2 : (2 : K) = 0) :
    DerSub K = Submodule.span K ({E₁ K, Dε K} : Set (A K →ₗ[K] A K)) := by
  refine le_antisymm (fun D hD => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨h0, -⟩ := der_coord hD
    have hcoord : D = (D (0, 1)).1 • (E₁ K) + (D (0, 1)).2 • (Dε K) := by
      refine lin_eq_of_basis ?_ ?_
      · rw [h0, show ((D (0, 1)).1 • (E₁ K) + (D (0, 1)).2 • (Dε K)) (1, 0) = 0 from by simp]
      · ext <;> simp
    rw [hcoord]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro D hD
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact E₁_der_of_char_two h2
    · exact Dε_der

theorem aderSub_eq_span_of_char_two (h2 : (2 : K) = 0) :
    ADerSub K = Submodule.span K ({E₁ K, Dε K} : Set (A K →ₗ[K] A K)) := by
  refine le_antisymm (fun D hD => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨h0, -⟩ := ader_coord hD
    have hcoord : D = (D (0, 1)).1 • (E₁ K) + (D (0, 1)).2 • (Dε K) := by
      refine lin_eq_of_basis ?_ ?_
      · rw [h0, show ((D (0, 1)).1 • (E₁ K) + (D (0, 1)).2 • (Dε K)) (1, 0) = 0 from by simp]
      · ext <;> simp
    rw [hcoord]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro D hD
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact E₁_ader_of_char_two h2
    · exact Dε_ader

theorem linIndep_E₁_Dε (K : Type*) [Field K] : LinearIndependent K (![E₁ K, Dε K] : Fin 2 → (A K →ₗ[K] A K)) := by
  rw [LinearIndependent.pair_iff]
  intro c d hcd
  have h := congrArg (fun (F : A K →ₗ[K] A K) => F (0, 1)) hcd
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, E₁_apply,
    Dε_apply, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, add_zero, mul_zero,
    zero_add, Prod.fst_zero, Prod.snd_zero] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem pair_eq_range (K : Type*) [Field K] : ({E₁ K, Dε K} : Set (A K →ₗ[K] A K)) = Set.range ![E₁ K, Dε K] := by
  ext F
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- `dim Der_α(A) = dim Der(A) = 2` in characteristic two. -/
theorem finrank_derSub_of_char_two (h2 : (2 : K) = 0) : Module.finrank K (DerSub K) = 2 := by
  rw [derSub_eq_span_of_char_two h2, pair_eq_range K, finrank_span_eq_card (linIndep_E₁_Dε K)]
  simp

theorem finrank_aderSub_of_char_two (h2 : (2 : K) = 0) : Module.finrank K (ADerSub K) = 2 := by
  rw [aderSub_eq_span_of_char_two h2, pair_eq_range K, finrank_span_eq_card (linIndep_E₁_Dε K)]
  simp

/-- `BSDer_{σ_α}(A)` is all of `End_K(A)` in characteristic two, hence
four-dimensional. -/
theorem finrank_bsderSub_of_char_two (h2 : (2 : K) = 0) :
    Module.finrank K (BSDerSub K) = 4 := by
  rw [bsderSub_eq_top h2, finrank_top, Module.finrank_linearMap K K (A K) (A K)]
  have hA : Module.finrank K (A K) = 2 := by
    rw [Module.finrank_prod]
    simp
  rw [hA]

/-! ## `Der_α(A) = Der(A)` in every characteristic -/

theorem aderSub_eq_derSub : ADerSub K = DerSub K := by
  by_cases h2 : (2 : K) = 0
  · rw [aderSub_eq_span_of_char_two h2, derSub_eq_span_of_char_two h2]
  · rw [aderSub_eq_span h2, derSub_eq_span h2]

end Ex45b
