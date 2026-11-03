/-
# Sharpness of the hypotheses: the necessity witnesses

The paper's results carry hypotheses that the paper does not show to be necessary.
This file machine-checks the witnesses:

1. **Corollary 3.5, "semiprime" is needed.**  The exterior algebra `Λ(F₃²)` is not
   semiprime, and `D(x) = x`, `D(1) = D(y) = D(xy) = 0` is a Jordan derivation that
   is not a derivation.  Since `α = id` here, `BSDer_{σ_α}(A)^α ∩ JDer = JDer`, so the
   corollary fails without semiprimality.  (It is not a defect of the paper: the
   corollary assumes semiprime.)

2. **Corollary 3.5, "2-torsion-free" is needed.**  `A = F₄` over `F₂`, `α` the
   Frobenius, `D(a + bω) = b`.  Then `A` is a field (so semiprime), `α` is an
   involutive automorphism, `D` commutes with `α` and satisfies the `σ_α`-Leibniz
   rule, and `D` is a Jordan derivation because in characteristic 2 the Jordan
   product `x ∘ y = xy + yx` vanishes; but `D` is not a derivation.  `A` is not
   2-torsion-free.

3. **Remark 4.6, the symmetry hypothesis of the sharpened statement is needed.**
   On the four-dimensional `F₃`-algebra with `x² = yx = y² = z`, `xy = 0` and `z`
   central zero, the map `D(x) = x + y` is a Jordan derivation, is not a derivation,
   and its defect is not symmetric: `E(x,y) = 2z` and `E(y,x) = z`.

4. **Remark 4.6, the weakened reducedness is strictly weaker than reducedness.**
   In `F₃[ε]/(ε³)` with `α(ε) = -ε` the element `ε` is nilpotent, so the algebra is
   not reduced, while no nonzero skew element has square zero (`A₋ = F₃ε` and
   `ε² ≠ 0`).  So the hypothesis printed at line 488 is satisfied by an algebra that
   reducedness excludes.

The computations are exact, on explicit finite structures; nothing here is a new
result of the paper, only the sharpness of what it assumes.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

namespace BraidedSymDerivSharpness

/-- `R` is semiprime if `a * R * a = 0` forces `a = 0` (Brešar 1988, p. 1003). -/
def Semiprime {A : Type*} [Zero A] (P : A → A → A) : Prop :=
  ∀ a : A, (∀ r : A, P (P a r) a = 0) → a = 0

/-- `A` is 2-torsion-free if `a + a = 0` forces `a = 0`. -/
def TwoTorsionFree (A : Type*) [Add A] [Zero A] : Prop := ∀ a : A, a + a = 0 → a = 0

/-! ## 1. Corollary 3.5: semiprime is needed — `Λ(F₃²)` -/

/-- The exterior algebra on two generators over `F₃`, in the basis `1, x, y, xy`. -/
abbrev L3 := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

/-- Multiplication: `x² = y² = 0`, `xy = -yx`. -/
def lmul (u v : L3) : L3 :=
  (u.1 * v.1, u.1 * v.2.1 + u.2.1 * v.1, u.1 * v.2.2.1 + u.2.2.1 * v.1,
   u.1 * v.2.2.2 + u.2.2.2 * v.1 + u.2.1 * v.2.2.1 - u.2.2.1 * v.2.1)

def ladd (u v : L3) : L3 :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1, u.2.2.2 + v.2.2.2)

/-- The Jordan product `x ∘ y = xy + yx`. -/
def ljor (u v : L3) : L3 := ladd (lmul u v) (lmul v u)

/-- The witness: `D(x) = x`, `D(1) = D(y) = D(xy) = 0`. -/
def lD (u : L3) : L3 := (0, u.2.1, 0, 0)

/-- `Λ(F₃²)` is not semiprime: `x * r * x = 0` for every `r`, and `x ≠ 0`. -/
theorem lam_not_semiprime : ¬ Semiprime lmul := by
  intro h
  have hx : (⟨0, 1, 0, 0⟩ : L3) = 0 :=
    h ⟨0, 1, 0, 0⟩ (by
      intro r
      simp only [lmul]
      ext <;> simp)
  exact absurd hx (by decide)

/-- `D` is a Jordan derivation. -/
theorem lD_jder :
    ∀ x y : L3, lD (ljor x y) = ladd (ljor (lD x) y) (ljor x (lD y)) := by
  intro x y
  simp only [lD, ljor, ladd, lmul]
  ext <;> simp <;> ring

/-- `D` is not a derivation: at `(x, y)` the left side is `D(xy) = 0` and the
right side is `xy = z ≠ 0`. -/
theorem lD_not_der :
    ¬ ∀ x y : L3, lD (lmul x y) = ladd (lmul (lD x) y) (lmul x (lD y)) := by
  intro h
  have hxy := h ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩
  simp only [lD, ladd, lmul] at hxy
  exact absurd hxy (by decide)

/-! ## 2. Corollary 3.5: 2-torsion-freeness is needed — `F₄` over `F₂` -/

/-- `F₄ = F₂[ω]/(ω² + ω + 1)`, elements `a + bω`. -/
abbrev F4 := ZMod 2 × ZMod 2

def f4mul (u v : F4) : F4 :=
  (u.1 * v.1 + u.2.1 * v.2.1, u.1 * v.2.1 + u.2.1 * v.1 + u.2.1 * v.2.1)

def f4add (u v : F4) : F4 := (u.1 + v.1, u.2.1 + v.2.1)

/-- The Frobenius `a + bω ↦ a + b + bω` (`ω² = ω + 1`). -/
def f4alpha (u : F4) : F4 := (u.1 + u.2.1, u.2.1)

/-- `D(a + bω) = b`: the coefficient of `ω`. -/
def f4D (u : F4) : F4 := (u.2.1, 0)

def f4jor (u v : F4) : F4 := f4add (f4mul u v) (f4mul v u)

/-- The `σ_α`-product `xy + α(y)α(x)`. -/
def f4tw (u v : F4) : F4 := f4add (f4mul u v) (f4mul (f4alpha v) (f4alpha u))

theorem f4_alpha_involutive : ∀ x : F4, f4alpha (f4alpha x) = x := by decide

theorem f4_alpha_mul : ∀ x y : F4, f4alpha (f4mul x y) = f4mul (f4alpha x) (f4alpha y) := by
  decide

theorem f4_D_comm : ∀ x : F4, f4D (f4alpha x) = f4alpha (f4D x) := by decide

/-- `D` satisfies the `σ_α`-Leibniz rule. -/
theorem f4_D_tw :
    ∀ x y : F4, f4D (f4tw x y) = f4add (f4tw (f4D x) y) (f4tw x (f4D y)) := by
  decide

/-- `D` is a Jordan derivation: in characteristic 2 the Jordan product vanishes. -/
theorem f4_D_jder :
    ∀ x y : F4, f4D (f4jor x y) = f4add (f4jor (f4D x) y) (f4jor x (f4D y)) := by
  decide

/-- `D` is not a derivation: at `(1, ω)` the left side is `D(ω) = 1` and the
right side is `0`. -/
theorem f4_D_not_der :
    ¬ ∀ x y : F4, f4D (f4mul x y) = f4add (f4mul (f4D x) y) (f4mul x (f4D y)) := by
  intro h
  have hxy := h ⟨0, 1⟩ ⟨0, 1⟩
  simp only [f4D, f4add, f4mul] at hxy
  exact absurd hxy (by decide)

/-- `F₄` is a field, hence semiprime. -/
theorem f4_semiprime : Semiprime f4mul := by
  intro a ha
  revert ha
  revert a
  decide

/-- `F₄` is not 2-torsion-free. -/
theorem f4_not_twoTorsionFree : ¬ TwoTorsionFree F4 := by
  intro h
  have h1 : (⟨1, 0⟩ : F4) + ⟨1, 0⟩ = 0 := by decide
  have h0 : (⟨1, 0⟩ : F4) = 0 := h _ h1
  exact absurd h0 (by decide)

/-! ## 3. Remark 4.6: the symmetry hypothesis is needed -/

/-- The four-dimensional `F₃`-algebra with `x² = yx = y² = z`, `xy = 0`, `z`
central and `z * A = 0`. -/
abbrev A489 := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

def m489 (u v : A489) : A489 :=
  (u.1 * v.1, u.1 * v.2.1 + u.2.1 * v.1, u.1 * v.2.2.1 + u.2.2.1 * v.1,
   u.1 * v.2.2.2 + u.2.2.2 * v.1 + u.2.1 * v.2.1 + u.2.2.1 * v.2.1 + u.2.2.1 * v.2.2.1)

def add489 (u v : A489) : A489 :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1, u.2.2.2 + v.2.2.2)

def jor489 (u v : A489) : A489 := add489 (m489 u v) (m489 v u)

/-- `D(x) = x + y`, `D(1) = D(y) = D(z) = 0`. -/
def D489 (u : A489) : A489 := (0, u.2.1, u.2.1, 0)

theorem D489_jder :
    ∀ x y : A489, D489 (jor489 x y) = add489 (jor489 (D489 x) y) (jor489 x (D489 y)) := by
  intro x y
  simp only [D489, jor489, add489, m489]
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h6 : (6 : ZMod 3) = 0 := by decide
  ext <;> simp <;> ring_nf <;> simp [h3, h6]

theorem D489_not_der :
    ¬ ∀ x y : A489, D489 (m489 x y) = add489 (m489 (D489 x) y) (m489 x (D489 y)) := by
  intro h
  have hxy := h ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩
  simp only [D489, add489, m489] at hxy
  exact absurd hxy (by decide)

/-- Subtraction, to write the defect `xy - Dx*y - x*Dy`. -/
def sub489 (u v : A489) : A489 :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2.1 - v.2.2.1, u.2.2.2 - v.2.2.2)

/-- The Leibniz defect `E(x,y) = xy - Dx*y - x*Dy`. -/
def E489 (x y : A489) : A489 :=
  sub489 (D489 (m489 x y)) (add489 (m489 (D489 x) y) (m489 x (D489 y)))

/-- The defect is not symmetric: `E(x,y) = 2z` and `E(y,x) = z`. -/
theorem E489_not_symm :
    E489 ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩ = (0, 0, 0, 2) ∧
      E489 ⟨0, 0, 1, 0⟩ ⟨0, 1, 0, 0⟩ = (0, 0, 0, 1) := by
  decide

/-! ## 4. Remark 4.6: the weakened reducedness is strictly weaker -/

/-- `F₃[ε]/(ε³)`. -/
abbrev A488 := ZMod 3 × ZMod 3 × ZMod 3

def m488 (u v : A488) : A488 :=
  (u.1 * v.1, u.1 * v.2.1 + u.2.1 * v.1,
   u.1 * v.2.2.1 + u.2.2.1 * v.1 + u.2.1 * v.2.1)

/-- `α(ε) = -ε`. -/
def alpha488 (u : A488) : A488 := (u.1, -u.2.1, u.2.2.1)

/-- The algebra is not reduced: `ε ≠ 0` and `ε³ = 0`. -/
theorem A488_not_reduced : ∃ z : A488, z ≠ 0 ∧ m488 (m488 z z) z = 0 := by
  refine ⟨⟨0, 1, 0⟩, by decide, ?_⟩
  simp only [m488]
  ext <;> simp

/-- But no nonzero skew element has square zero: `A₋ = F₃ε` and `ε² ≠ 0`. -/
theorem A488_no_skew_square_zero :
    ∀ z : A488, alpha488 z = -z → m488 z z = 0 → z = 0 := by
  intro z hz hs
  revert hz hs
  revert z
  decide

end BraidedSymDerivSharpness
