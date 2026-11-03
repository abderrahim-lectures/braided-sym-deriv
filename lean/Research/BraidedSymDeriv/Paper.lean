/-
# Results of "Braided-Symmetric Derivations of Algebras", v80

This module formalizes the results of the paper that the earlier files left out,
and it states them in the paper's own terms:

* `P` is the paper's product `x ·_σ y = μ(x⊗y) + μ(σ(x⊗y))`, taken at the level of
  the product (the paper works with `σ : A ⊗ A → A ⊗ A`; a binary map `P` is the
  product it induces).  That suffices for every derivation statement of the
  paper, but **not** for Remark 2.4's classification of the involutions `σ`
  themselves, which the product forgets (over a commutative `A`, the distinct
  involutions `id` and `τ` induce the same product `2xy`): that classification
  is formalized in `Remark24.lean`, in the `M₂(K)` matrix form of `V ⊗ V`;
* `BSDerP P D` is the braided-symmetric derivation condition for `P`;
* the dictionary of Remark 2.4, all four structure-free cases, including the
  degenerate `-id` and the Lie-derivation case `-τ` (which the binary-map
  encoding of `BraidedSymmetric.lean` cannot express);
* the bridge between `P` and the twisted identity of Proposition 3.2;
* Theorem 4.1 as an equivalence, and Corollary 3.5 both unconditionally
  (`corollary_3_5_unconditional`, using `Bresar1988.lean`, which proves
  Brešar's theorem) and in the conditional form that takes it as a hypothesis
  (`corollary_3_5`, kept for reference);
* the refinement of Proposition 3.2, the inner-derivation part of Remark 3.3,
  Example 4.3, and a counterexample showing Corollary 3.5 needs semiprimeness.

The ordinary, Jordan, Lie and inner derivations are aliases of the definitions
in `BraidedSymmetric.lean`, which this module imports (earlier versions
re-declared them here because that file's root-namespace `LieDerivation`
clashed with Mathlib and was unimportable; the clash is fixed).

Everything is stated for additive maps on rings, which is stronger than the
paper's K-linear maps on K-algebras.  No `sorry`, no `native_decide`.
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NoncommRing
import Research.BraidedSymDeriv.TwistedCommutative
import Research.BraidedSymDeriv.BraidedSymmetric
import Research.BraidedSymDeriv.Bresar1988

namespace BSD

open scoped Classical

variable {A : Type*} [Ring A]

/-! ## The product and the derivation conditions -/

/-- The paper's product `μ + μ ∘ σ`, at the level of the product: an alias of
`BraidedSymDeriv.symmetrizedProduct` from `BraidedSymmetric.lean`.  (Earlier
versions re-declared it here: the root-namespace `LieDerivation` of that file
clashed with Mathlib and made the library unimportable, so this file could not
import it.  The clash is fixed; the duplicate definitions are gone.) -/
abbrev Symm (σ : A → A → A) (x y : A) : A :=
  BraidedSymDeriv.symmetrizedProduct σ x y

/-- Braided-symmetric derivation for a product `P` (Definition 2.1). -/
def BSDerP (P : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y, D (P x y) = P (D x) y + P x (D y)

/-- Ordinary derivation: alias of `BraidedSymDeriv.Der`. -/
abbrev Der (D : A →+ A) : Prop := BraidedSymDeriv.Der D

/-- Jordan derivation, in the paper's `∘` form `D(x)∘y + x∘D(y)`: alias of
`BraidedSymDeriv.JordanDerivation`. -/
abbrev JDer (D : A →+ A) : Prop := BraidedSymDeriv.JordanDerivation D

/-- Lie derivation, in the paper's form `[D(x),y] + [x,D(y)]`: alias of
`BraidedSymDeriv.LieDerivation`. -/
abbrev LieDer (D : A →+ A) : Prop := BraidedSymDeriv.LieDerivation D

/-- `D` commutes with `α`. -/
def Comm (D : A →+ A) (α : A → A) : Prop := ∀ x, D (α x) = α (D x)

/-! ## Remark 2.4: the dictionary, all four structure-free cases -/

/-- The identity involution: `x·y = 2xy`; the class is `Der` when 2 is cancellable. -/
theorem bsderP_two_mul_iff (h2 : ∀ a : A, a + a = 0 → a = 0) (D : A →+ A) :
    BSDerP (fun x y => x * y + x * y) D ↔ Der D := by
  constructor
  · intro h x y
    have hxy := h x y
    simp only [map_add] at hxy
    have hz : (D (x * y) - (D x * y + x * D y)) +
        (D (x * y) - (D x * y + x * D y)) = 0 := by
      calc (D (x * y) - (D x * y + x * D y)) + (D (x * y) - (D x * y + x * D y))
          = (D (x * y) + D (x * y)) - ((D x * y + x * D y) + (D x * y + x * D y)) := by abel
        _ = 0 := by rw [hxy]; abel
    exact sub_eq_zero.mp (h2 _ hz)
  · intro h x y
    have hxy := h x y
    simp only [map_add, hxy]
    abel

/-- The swap `τ`: `x·y = xy + yx`; the class is `JDer`. -/
theorem bsderP_jordan_iff (D : A →+ A) :
    BSDerP (fun x y => x * y + y * x) D ↔ JDer D := by
  constructor
  · intro h x y
    have hxy := h x y
    dsimp only at hxy ⊢
    rw [hxy]; ac_rfl
  · intro h x y
    have hxy := h x y
    dsimp only at hxy ⊢
    rw [hxy]; ac_rfl

/-- The degenerate case `-id`: the product is zero, so every additive map qualifies. -/
theorem bsderP_zero (D : A →+ A) : BSDerP (fun _ _ => 0) D := by
  intro x y
  show D 0 = (0 : A) + 0
  simp

/-- The case `-τ`: the product is the commutator, so the class is `LieDer`. -/
theorem bsderP_commutator_iff (D : A →+ A) :
    BSDerP (fun x y => x * y - y * x) D ↔ LieDer D := Iff.rfl

/-! ## The bridge: `σ_α` and the twisted identity of Proposition 3.2 -/

/-- The twisted identity of the paper, written with `α : A →+* A`. -/
def TwistedAlpha (α : A →+* A) (D : A →+ A) : Prop :=
  ∀ x y, D (x * y + α (y * x)) =
    D x * y + α (y * D x) + (x * D y + α (D y * x))

/-- `Symm (fun _ y => α y)` is the twisted product `xy + α(y)α(x)`. -/
theorem symm_alpha (α : A →+* A) (x y : A) :
    Symm (fun _ y => α y) x y = x * y + α (y * x) := by
  simp [Symm, BraidedSymDeriv.symmetrizedProduct, map_mul]

/-- `BSDerP` for the twisted product is exactly the paper's twisted identity. -/
theorem bsderP_alpha_iff (α : A →+* A) (D : A →+ A) :
    BSDerP (Symm (fun _ y => α y)) D ↔ TwistedAlpha α D := by
  constructor
  · intro h x y
    have hxy := h x y
    simpa [Symm, BraidedSymDeriv.symmetrizedProduct, map_mul] using hxy
  · intro h x y
    have hxy := h x y
    simpa [Symm, BraidedSymDeriv.symmetrizedProduct, map_mul] using hxy

/-! ## Theorem 4.1 as an equivalence -/

/-- Every derivation is a Jordan derivation. -/
theorem der_jder {D : A →+ A} (h : Der D) : JDer D := by
  intro x y
  have h1 := h x y
  have h2 := h y x
  rw [map_add, h1, h2]
  abel

/-- **Theorem 4.1**, as an equivalence: for a commutative reduced algebra with `2`
invertible and `α` an involutive automorphism, the twisted class is the class of
derivations commuting with `α`. -/
theorem theorem_4_1 {A : Type*} [CommRing A] [IsReduced A]
    (α : A ≃+* A) (hαα : ∀ x, α (α x) = x) (D : A →+ A)
    (h2 : IsUnit (2 : A)) (hDα : Comm D α) :
    TwistedAlpha α D ↔ Der D := by
  constructor
  · intro h x y
    exact twisted_commutative α hαα D h2 hDα h x y
  · intro h
    exact (der_twisted_iff_comm α D h).2 hDα

/-- **Corollary 3.5**, conditional on Brešar's theorem (every Jordan derivation of
a 2-torsion-free semiprime ring is a derivation): the Jordan maps of the twisted
class are exactly the derivations commuting with `α`. -/
theorem corollary_3_5 (α : A ≃+* A) (_hαα : ∀ x, α (α x) = x) (D : A →+ A)
    (hDα : Comm D α) (hBresar : ∀ E : A →+ A, JDer E → Der E) :
    (TwistedAlpha α D ∧ JDer D) ↔ Der D := by
  constructor
  · rintro ⟨-, hJ⟩
    exact hBresar D hJ
  · intro hD
    exact ⟨(der_twisted_iff_comm α D hD).2 hDα, der_jder hD⟩

/-! ## Corollary 3.5 without hypotheses

Brešar's theorem is proved in `Bresar1988.lean`.  What is needed here is only
the bridge between this file's `JDer` (the library's expanded form) and the
`∘` form of `Background.JordanHerstein`. -/

/-- The two spellings of the Jordan condition agree. -/
theorem jder_iff_background {D : A →+ A} :
    JDer D ↔ Background.JordanHerstein.JDer D := by
  constructor
  · intro h x y
    have hxy := h x y
    simp only [Background.JordanHerstein.jordan]
    linear_combination (norm := noncomm_ring) hxy
  · intro h x y
    have hxy := h x y
    simp only [Background.JordanHerstein.jordan] at hxy
    linear_combination (norm := noncomm_ring) hxy

/-- **Brešar 1988, Theorem 1** in this file's vocabulary: on a 2-torsion-free
semiprime ring every Jordan derivation is a derivation. -/
theorem jder_eq_der_of_semiprime (h2 : Background.JordanHerstein.TwoTorsionFree A)
    (hs : Background.JordanHerstein.SemiprimeRing A) : ∀ E : A →+ A, JDer E → Der E :=
  fun E hE =>
    Bresar1988.bresar1988Theorem1_apply A h2 hs E ((jder_iff_background).1 hE)

/-- **Corollary 3.5, unconditional**: for a 2-torsion-free semiprime ring and an
involutive automorphism `α`, a map lies in the `α`-commuting twisted class and is
a Jordan derivation exactly when it is a derivation commuting with `α`. -/
theorem corollary_3_5_unconditional (h2 : Background.JordanHerstein.TwoTorsionFree A)
    (hs : Background.JordanHerstein.SemiprimeRing A) (α : A ≃+* A)
    (hαα : ∀ x, α (α x) = x) (D : A →+ A) (hDα : Comm D α) :
    (TwistedAlpha α D ∧ JDer D) ↔ Der D :=
  corollary_3_5 α hαα D hDα (jder_eq_der_of_semiprime h2 hs)

/-! ## The refinement of Proposition 3.2 (`2` invertible)

The paper splits the defect into `E_s` (symmetric) and `E_a` (antisymmetric) and
reads case (i) as "`E_s` takes values in `A_-` and `E_a` in `A_+`".  This is the
form used in Theorem 4.1 and in Proposition 4.4, both commutative, so it is
formalized here for commutative rings. -/

section Refinement

variable {A : Type*} [CommRing A]

/-- The symmetric part of the defect, `E_s = ½(E(x,y) + E(y,x))`. -/
def Es (D : A →+ A) (w : A) (x y : A) : A :=
  w * (ncDefect D x y + ncDefect D y x)

/-- The antisymmetric part of the defect, `E_a = ½(E(x,y) − E(y,x))`. -/
def Ea (D : A →+ A) (w : A) (x y : A) : A :=
  w * (ncDefect D x y - ncDefect D y x)

/-- `w = ½` is fixed by any ring automorphism: `α w = w`. -/
theorem alpha_half (α : A ≃+* A) {w : A} (hw : 2 * w = 1) : α w = w := by
  have h1 : (2 : A) * α w = 1 := by
    have h := congrArg α hw
    rw [map_mul, map_one, map_ofNat] at h
    exact h
  have hw' : w * 2 = 1 := by rw [mul_comm]; exact hw
  calc α w = 1 * α w := by rw [one_mul]
    _ = (w * 2) * α w := by rw [hw']
    _ = w * (2 * α w) := by ring
    _ = w * 1 := by rw [h1]
    _ = w := by rw [mul_one]

/-- **The refinement of Proposition 3.2**: with `2` invertible, the twisted
identity holds exactly when `E_s` is skew-valued and `E_a` symmetric-valued. -/
theorem refinement (α : A ≃+* A) (D : A →+ A) (hDα : Comm D α)
    {w : A} (hw : 2 * w = 1) :
    TwistedAlpha α D ↔
      (∀ x y, α (Es D w x y) = - Es D w x y) ∧
      (∀ x y, α (Ea D w x y) = Ea D w x y) := by
  have hαw : α w = w := alpha_half α hw
  have hw' : w * 2 = 1 := by rw [mul_comm]; exact hw
  have hsum : ∀ x y, Es D w x y + Ea D w x y = ncDefect D x y := by
    intro x y
    simp only [Es, Ea]
    rw [← mul_add]
    have h2 : (ncDefect D x y + ncDefect D y x) + (ncDefect D x y - ncDefect D y x)
        = 2 * ncDefect D x y := by ring
    rw [h2, ← mul_assoc, hw', one_mul]
  have hsub : ∀ x y, Es D w x y - Ea D w x y = ncDefect D y x := by
    intro x y
    simp only [Es, Ea]
    rw [← mul_sub]
    have h2 : (ncDefect D x y + ncDefect D y x) - (ncDefect D x y - ncDefect D y x)
        = 2 * ncDefect D y x := by ring
    rw [h2, ← mul_assoc, hw', one_mul]
  have hsplit : ∀ x y, ncDefect D x y = Es D w x y + Ea D w x y :=
    fun x y => (hsum x y).symm
  have hsplit' : ∀ x y, ncDefect D y x = Es D w x y - Ea D w x y :=
    fun x y => (hsub x y).symm
  constructor
  · intro h
    have hcond : ∀ x y, ncDefect D x y + α (ncDefect D y x) = 0 :=
      (prop_defect_aut α D hDα).1 h
    have key : ∀ x y, α (ncDefect D x y) = - ncDefect D y x := by
      intro x y
      have h' := hcond y x
      linear_combination h'
    constructor
    · intro x y
      show α (w * (ncDefect D x y + ncDefect D y x))
        = -(w * (ncDefect D x y + ncDefect D y x))
      rw [map_mul, map_add, key x y, key y x, hαw]
      ring
    · intro x y
      show α (w * (ncDefect D x y - ncDefect D y x))
        = w * (ncDefect D x y - ncDefect D y x)
      rw [map_mul, map_sub, key x y, key y x, hαw]
      ring
  · rintro ⟨hEs, hEa⟩
    refine (prop_defect_aut α D hDα).2 ?_
    intro x y
    rw [hsplit x y, hsplit' x y, map_sub, hEs x y, hEa x y]
    ring

end Refinement

/-! ## Remark 3.3: inner derivations -/

/-- The inner derivation `x ↦ gx - xg`: alias of
`BraidedSymDeriv.innerDerivation`. -/
abbrev innerDer (g : A) : A →+ A := BraidedSymDeriv.innerDerivation g

theorem innerDer_der (g : A) : Der (innerDer g) := by
  intro x y
  show g * (x * y) - (x * y) * g = (g * x - x * g) * y + x * (g * y - y * g)
  noncomm_ring

/-- `ad_g` commutes with `α` exactly when `g - α(g)` is central for `α` on the
image of `α`. -/
theorem innerDer_comm_iff (α : A ≃+* A) (g : A) :
    Comm (innerDer g) α ↔ ∀ x, (g - α g) * α x = α x * (g - α g) := by
  constructor
  · intro h x
    have hx : g * α x - α x * g = α g * α x - α x * α g := by
      simpa [BraidedSymDeriv.innerDerivation] using h x
    have key : (g - α g) * α x - α x * (g - α g)
        = (g * α x - α x * g) - (α g * α x - α x * α g) := by noncomm_ring
    rw [← sub_eq_zero, key, hx]
    abel
  · intro h x
    have hx : (g - α g) * α x = α x * (g - α g) := h x
    have key : (g - α g) * α x - α x * (g - α g)
        = (g * α x - α x * g) - (α g * α x - α x * α g) := by noncomm_ring
    have hzero : (g - α g) * α x - α x * (g - α g) = 0 := by rw [hx]; abel
    rw [key] at hzero
    simpa [BraidedSymDeriv.innerDerivation] using sub_eq_zero.mp hzero

/-- **Remark 3.3**, second half: an inner derivation lies in the twisted class iff
`g - α(g)` is central for `α`. -/
theorem innerDer_twisted_iff (α : A ≃+* A) (_hαα : ∀ x, α (α x) = x) (g : A) :
    TwistedAlpha α (innerDer g) ↔ ∀ x, (g - α g) * α x = α x * (g - α g) := by
  rw [← innerDer_comm_iff α g]
  exact der_twisted_iff_comm α (innerDer g) (innerDer_der g)


/-- **Remark 3.3**, the `∈ Z(A)` form: because `α` is bijective, commuting with `α(x)`
for all `x` is commuting with everything. -/
theorem innerDer_comm_iff_center (α : A ≃+* A) (g : A) :
    Comm (innerDer g) α ↔ (g - α g) ∈ Subring.center A := by
  rw [innerDer_comm_iff α g]
  constructor
  · intro h
    refine Subring.mem_center_iff.mpr fun x => ?_
    obtain ⟨y, rfl⟩ := α.surjective x
    exact (h y).symm
  · intro h x
    exact (Subring.mem_center_iff.mp h (α x)).symm

/-- **Remark 3.3**: `ad_g` lies in the twisted class iff `g - α(g) ∈ Z(A)`. -/
theorem innerDer_twisted_iff_center (α : A ≃+* A) (hαα : ∀ x, α (α x) = x) (g : A) :
    TwistedAlpha α (innerDer g) ↔ (g - α g) ∈ Subring.center A := by
  rw [innerDer_twisted_iff α hαα g]
  exact (innerDer_comm_iff α g).symm.trans (innerDer_comm_iff_center α g)

/-- **Remark 3.3**: `Inn_α(A) = Inn(A) ∩ BSDer_{σ_α}(A)^α`, the inner derivations with
`g - α(g) ∈ Z(A)` being exactly the inner derivations that lie in the `α`-commuting
twisted class. -/
theorem innAlpha_eq (α : A ≃+* A) (hαα : ∀ x, α (α x) = x) :
    {D : A →+ A | ∃ g, D = innerDer g ∧ (g - α g) ∈ Subring.center A}
      = {D : A →+ A | ∃ g, D = innerDer g}
        ∩ {D : A →+ A | TwistedAlpha α D ∧ Comm D α} := by
  ext D
  constructor
  · rintro ⟨g, rfl, hg⟩
    exact ⟨⟨g, rfl⟩, (innerDer_twisted_iff_center α hαα g).2 hg,
      (innerDer_comm_iff_center α g).2 hg⟩
  · rintro ⟨⟨g, rfl⟩, htw, hcomm⟩
    exact ⟨g, rfl, (innerDer_twisted_iff_center α hαα g).1 htw⟩

end BSD

/-! ## Example 4.3: `F₂ × F₂` -/

namespace BSD.Example43

abbrev A : Type := Fin 2 → ZMod 2

/-- The swap of the two factors. -/
def α : A ≃+* A where
  toFun v := fun i => v (Fin.rev i)
  invFun := fun v => fun i => v (Fin.rev i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_mul' u v := by funext i; simp [Pi.mul_apply]
  map_add' u v := by funext i; simp [Pi.add_apply]

/-- `D(p) = D(q) = e = (1,1)`: the sum of the two coordinates, in each coordinate. -/
def D : A →+ A where
  toFun v := fun _ => v 0 + v 1
  map_zero' := by funext i; simp
  map_add' u v := by funext i; simp [Pi.add_apply, add_assoc, add_comm, add_left_comm]

/-- `D` commutes with `α`. -/
theorem comm : BSD.Comm D α := by
  intro v
  funext i
  simp [D, α, add_comm]

/-- `D` satisfies the twisted identity on all four pairs. -/
theorem twisted : BSD.TwistedAlpha α D := by
  unfold BSD.TwistedAlpha
  decide

/-- `D` is not a derivation. -/
theorem not_der : ¬ BSD.Der D := by
  intro h
  have h1 := h (fun i => if i = 0 then 1 else 0) (fun i => if i = 0 then 1 else 0)
  revert h1
  decide

end BSD.Example43


/-! ## Example 2.3: the twisted product need not be associative or unital -/

namespace BSD.Example23

abbrev A : Type := Fin 2 → ZMod 5

/-- The swap of the two factors. -/
def α : A ≃+* A where
  toFun v := fun i => v (Fin.rev i)
  invFun v := fun i => v (Fin.rev i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_mul' u v := by funext i; simp [Pi.mul_apply]
  map_add' u v := by funext i; simp [Pi.add_apply]

/-- The twisted product `x·y = xy + α(xy)` of the commutative algebra. -/
def P (x y : A) : A := x * y + α (x * y)

def p : A := fun i => if i = 0 then 1 else 0
def q : A := fun i => if i = 0 then 0 else 1

/-- `(p·p)·q ≠ p·(p·q)`: the product is not associative. -/
theorem not_assoc : P (P p p) q ≠ P p (P p q) := by
  unfold P p q α
  decide

/-- No element is a left unit for `p`. -/
theorem no_unit : ∀ u : A, P u p ≠ p := by
  decide

end BSD.Example23
