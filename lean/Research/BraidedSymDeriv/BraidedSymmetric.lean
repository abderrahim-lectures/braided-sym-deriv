import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Braided-Symmetric Derivations

Definitions and basic lemmas for braided-symmetric derivations on
algebra objects in symmetric monoidal categories, following
[Adrabi2026, §2].

## Main definitions

* `BraidedSymmetricDerivation`: D satisfies the Leibniz rule for ·_σ.
* `JordanDerivation`: D(x∘y) = D(x)∘y + x∘D(y) where x∘y = xy+yx.
* `Der` / `Inn`: derivations and inner derivations.

## References

* [Adrabi2026] Adrabi, "Braided-Symmetric Derivations in Symmetric Monoidal Categories".
-/

-- A ranges over any (possibly noncommutative) ring; every definition below is
-- stated for this fixed but arbitrary A.
variable {A : Type*} [Ring A]

/-! ## The σ-symmetrized product -/

/-- The σ-symmetrized product: x ·_σ y = xy + σ(x,y)·σ(y,x). -/
def symmetrizedProduct (σ : A → A → A) (x y : A) : A :=
  -- Definition 2.1 in the paper: the ordinary product xy plus the product of
  -- the two braiding outputs σ(x,y) and σ(y,x), in that order.
  x * y + σ x y * σ y x

/-- The standard braiding σ(x⊗y) = y⊗x, written as a binary map σ(x,y) = y. -/
def standardBraiding (_x _y : A) : A := _y
-- standardBraiding never reads its first argument: the swap braiding on a
-- pure tensor x⊗y returns y⊗x, and a binary map σ(x,y) representing that
-- output's "second factor" is exactly the constant-in-x projection onto y.

@[simp] theorem symmetrizedProduct_std (x y : A) :
    symmetrizedProduct standardBraiding x y = x * y + y * x := rfl
-- Unfolds standardBraiding: standardBraiding x y = y and standardBraiding y x = x,
-- so σ(x,y)·σ(y,x) reduces to y*x, giving xy + yx, the Jordan product.
-- `rfl` closes it because both sides reduce to the same normal form by
-- unfolding definitions alone, with no ring axiom needed.

/-! ## Braided-symmetric derivations -/

/-- D is a braided-symmetric derivation for braiding σ:
    D(x ·_σ y) = D(x) ·_σ y + x ·_σ D(y). -/
def BraidedSymmetricDerivation (σ : A → A → A) (D : A →+ A) : Prop :=
  -- Definition 3.1 in the paper, equation (eq:sigma-leibniz): the additive
  -- map D satisfies the Leibniz rule with respect to ·_σ instead of ·.
  ∀ x y : A, D (symmetrizedProduct σ x y) =
    symmetrizedProduct σ (D x) y + symmetrizedProduct σ x (D y)

/-! ## Jordan derivations -/

/-- D(x∘y) = D(x)∘y + x∘D(y) where x∘y = xy+yx (Corollary 3.5). -/
def JordanDerivation (D : A →+ A) : Prop :=
  -- The classical Jordan-derivation identity, written out with the Jordan
  -- product xy+yx expanded on both sides rather than left as x∘y, so this
  -- definition does not itself depend on `symmetrizedProduct`.
  ∀ x y : A, D (x * y + y * x) = D x * y + x * D y + D y * x + y * D x

/-- (Proposition 3.4) Braided-symmetric derivations for the standard
    braiding are exactly Jordan derivations. -/
theorem jordanDerivation_of_braidedSymmetricDerivation_std {D : A →+ A} :
    BraidedSymmetricDerivation standardBraiding D → JordanDerivation D := by
  -- Forward direction of Proposition 3.4(a): σ = τ (standard swap) gives ⊆.
  intro h x y
  -- h : BraidedSymmetricDerivation standardBraiding D, instantiated below at
  -- the pair (x, y) we need for the current goal.
  have hxy := h x y
  -- Rewrite hxy's occurrences of symmetrizedProduct standardBraiding using
  -- the `rfl`-lemma above, turning it into a statement about xy+yx directly.
  simp only [symmetrizedProduct_std] at hxy
  -- hxy : D (x * y + y * x) = D x * y + y * D x + (x * D y + D y * x)
  -- goal : D (x * y + y * x) = D x * y + x * D y + D y * x + y * D x
  rw [hxy]
  -- goal : D x * y + y * D x + (x * D y + D y * x) = D x * y + x * D y + D y * x + y * D x
  -- The two sides are equal only up to reassociation and reordering of an
  -- additive commutative group; `abel_nf` normalizes both sides and closes
  -- the goal by reflexivity on the normal form (the underlying operation is
  -- addition in A, which is commutative, unlike the ring's multiplication).
  abel_nf

/-- (Proposition 3.4, converse) Jordan derivations are braided-symmetric
    derivations for the standard braiding. -/
theorem braidedSymmetricDerivation_of_jordanDerivation_std {D : A →+ A} :
    JordanDerivation D → BraidedSymmetricDerivation standardBraiding D := by
  -- Converse direction of Proposition 3.4(a): σ = τ gives ⊇, so together
  -- with the previous theorem, BSDer_τ(A) = JDer(A).
  intro h x y
  -- Unfold the goal's symmetrizedProduct standardBraiding occurrences first,
  -- before invoking h, so h x y can be matched against the resulting goal.
  simp only [symmetrizedProduct_std]
  -- goal : D (x * y + y * x) = D x * y + y * D x + (x * D y + D y * x)
  have hxy := h x y
  -- hxy : D (x * y + y * x) = D x * y + x * D y + D y * x + y * D x
  rw [hxy]
  -- goal : D x * y + x * D y + D y * x + y * D x = D x * y + y * D x + (x * D y + D y * x)
  -- Same reassociation-only gap as in the forward direction, closed the
  -- same way.
  abel_nf

/-! ## Derivations and inner derivations -/

/-- D is a derivation of (A, ·): D(xy) = D(x)y + xD(y). -/
def Der (D : A →+ A) : Prop :=
  -- The ordinary Leibniz rule, i.e. BraidedSymmetricDerivation for the
  -- identity braiding σ(x,y) = x (so ·_σ reduces to · alone) — stated
  -- directly rather than through symmetrizedProduct, matching how the
  -- paper first introduces Der(A) in the Introduction before Definition 3.1.
  ∀ x y : A, D (x * y) = D x * y + x * D y

/-- Inner derivation: D_a(x) = ax - xa. -/
def innerDerivation (a : A) : A →+ A :=
  -- AddMonoidHom.mk' packages the map x ↦ ax - xa together with a proof
  -- that it distributes over addition, which is what makes it a genuine
  -- A →+ A rather than a bare function.
  AddMonoidHom.mk' (fun x => a * x - x * a) fun x y => by noncomm_ring
  -- The additivity proof obligation is a(x+y)-(x+y)a = (ax-xa)+(ay-ya);
  -- `noncomm_ring` proves this by ring-normalizing both sides without
  -- assuming commutativity of multiplication (only the abelian group
  -- structure of + and the distributive laws are used).

/-- Inner derivation satisfies the Leibniz rule. -/
theorem innerDerivation_mem_Der (a : A) : Der (innerDerivation a) := by
  intro x y
  -- Unfold innerDerivation on both sides of the goal so the Leibniz-rule
  -- statement is phrased purely in terms of a, x, y and the ring operations.
  simp [innerDerivation]
  -- goal after simp: a*(x*y) - (x*y)*a = (a*x-x*a)*y + x*(a*y-y*a)
  -- This is the identity commutator [a,xy] = [a,x]y + x[a,y], a standard
  -- noncommutative-ring identity; `noncomm_ring` proves it by normalizing
  -- both sides as sums of monomials in a, x, y with signs, without
  -- commuting a past x or y.
  noncomm_ring

/-- Inner derivations form a subset of Der(A). -/
def Inn (D : A →+ A) : Prop :=
  -- D is inner iff it equals innerDerivation a for some a; this is an
  -- existence statement, not a subtype, matching the paper's Inn(A) as a
  -- subset of the ambient additive group of maps A →+ A.
  ∃ a : A, innerDerivation a = D

/-- (Corollary 3.5) Every derivation is a Jordan derivation. -/
theorem Der.subset_JDer {D : A →+ A} (hD : Der D) : JordanDerivation D := by
  -- This is the classical inclusion Der(A) ⊆ JDer(A) restated categorically
  -- in the paper as the comparison between the identity braiding and the
  -- standard swap braiding (Introduction, paragraph after Def 3.1).
  intro x y
  have h1 := hD x y
  -- h1 : D (x * y) = D x * y + x * D y
  have h2 := hD y x
  -- h2 : D (y * x) = D y * x + y * D x
  -- Rewrite D(xy+yx) as D(xy) + D(yx) using additivity of D (map_add),
  -- then substitute h1 and h2 to expand both summands.
  rw [map_add D (x * y) (y * x), h1, h2]
  -- goal : D x * y + x * D y + (D y * x + y * D x)
  --        = D x * y + x * D y + D y * x + y * D x
  -- Purely a reassociation of a four-term sum; `abel_nf` normalizes and
  -- closes it, same pattern as the two proofs above.
  abel_nf

/-! ## The antisymmetrized product and Lie derivations -/

/-- The σ-antisymmetrized product: x ·_σ⁻ y = xy − σ(x,y)·σ(y,x). -/
def antisymmetrizedProduct (σ : A → A → A) (x y : A) : A :=
  x * y - σ x y * σ y x

@[simp] theorem antisymmetrizedProduct_std (x y : A) :
    antisymmetrizedProduct standardBraiding x y = x * y - y * x := rfl

/-- D is a braided-antisymmetric derivation for σ:
    D(x ·_σ⁻ y) = D(x) ·_σ⁻ y + x ·_σ⁻ D(y). -/
def BraidedAntisymmetricDerivation (σ : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (antisymmetrizedProduct σ x y) =
    antisymmetrizedProduct σ (D x) y + antisymmetrizedProduct σ x (D y)

/-- D([x,y]) = [D(x),y] + [x,D(y)] where [x,y] = xy − yx. -/
def LieDerivation (D : A →+ A) : Prop :=
  ∀ x y : A, D (x * y - y * x) = (D x * y - y * D x) + (x * D y - D y * x)

/-- Braided-antisymmetric derivations for the standard braiding are
    exactly Lie derivations. -/
theorem lieDerivation_iff_braidedAntisymmetricDerivation_std {D : A →+ A} :
    LieDerivation D ↔ BraidedAntisymmetricDerivation standardBraiding D := by
  constructor
  · intro h x y
    rw [antisymmetrizedProduct_std, antisymmetrizedProduct_std, antisymmetrizedProduct_std]
    exact h x y
  · intro h x y
    have hxy := h x y
    rw [antisymmetrizedProduct_std, antisymmetrizedProduct_std, antisymmetrizedProduct_std] at hxy
    exact hxy

/-- Every derivation is a Lie derivation. -/
theorem Der.subset_LDer {D : A →+ A} (hD : Der D) : LieDerivation D := by
  intro x y
  rw [map_sub D (x * y) (y * x), hD x y, hD y x]
  abel_nf

/-- A derivation vanishes on the unit. -/
theorem Der.map_one {D : A →+ A} (hD : Der D) : D 1 = 0 := by
  have h := hD 1 1
  simp only [one_mul, mul_one] at h
  -- h : D 1 = D 1 + D 1
  calc D 1 = D 1 + D 1 - D 1 := (add_sub_cancel_right (D 1) (D 1)).symm
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

/-- A derivation plus an additive map with central values that vanishes on
    commutators is a Lie derivation (the shape in Martindale's and
    Brešar's theorems). -/
theorem LieDerivation.add_central {d τ : A →+ A} (hd : Der d)
    (hc : ∀ x y : A, τ x * y = y * τ x) (hk : ∀ x y : A, τ (x * y - y * x) = 0) :
    LieDerivation (d + τ) := by
  intro x y
  have hlie := Der.subset_LDer hd x y
  have hx := hc x y
  have hy := hc y x
  rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, AddMonoidHom.add_apply,
    hlie, hk x y, add_mul, mul_add, add_mul, mul_add, hx, hy]
  -- only the central terms y·τx and x·τy remain; they cancel in pairs
  abel_nf

/-- The central part of a Lie derivation `d + τ` is detected at the unit:
    if `τ 1 ≠ 0` then `d + τ` is not a derivation. -/
theorem not_Der_of_add_central {d τ : A →+ A} (hd : Der d) (h1 : τ 1 ≠ 0) :
    ¬ Der (d + τ) := by
  intro h
  have hsum := Der.map_one h
  rw [AddMonoidHom.add_apply, Der.map_one hd, zero_add] at hsum
  exact h1 hsum

/-! ## Lie derivations of matrix algebras -/
namespace BraidedSymDerivTrace

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- τ(x) = tr(x)·I on M_n(K). -/
def traceScalar : Matrix n n K →+ Matrix n n K :=
  AddMonoidHom.mk' (fun x => Matrix.scalar n (Matrix.trace x)) fun x y => by
    rw [Matrix.trace_add, map_add]

theorem traceScalar_central (x y : Matrix n n K) :
    traceScalar x * y = y * traceScalar x := by
  show Matrix.scalar n (Matrix.trace x) * y = y * Matrix.scalar n (Matrix.trace x)
  exact ((Matrix.scalar_commute (Matrix.trace x) (fun _ => Commute.all _ _) y)).eq

theorem traceScalar_commutator (x y : Matrix n n K) :
    traceScalar (x * y - y * x) = 0 := by
  show Matrix.scalar n (Matrix.trace (x * y - y * x)) = 0
  rw [Matrix.trace_sub, Matrix.trace_mul_comm x y, sub_self, map_zero]

theorem traceScalar_one : traceScalar (1 : Matrix n n K) = Matrix.scalar n (Fintype.card n : K) := by
  show Matrix.scalar n (Matrix.trace (1 : Matrix n n K)) = _
  rw [Matrix.trace_one]

/-- On M_n(K) with n ≠ 0 in K, x ↦ tr(x)·I is a Lie derivation and not a
    derivation. -/
theorem traceScalar_lie_not_der (hn : (Fintype.card n : K) ≠ 0) :
    LieDerivation (0 + traceScalar : Matrix n n K →+ Matrix n n K) ∧
      ¬ Der (0 + traceScalar : Matrix n n K →+ Matrix n n K) := by
  have hd : Der (0 : Matrix n n K →+ Matrix n n K) := by
    intro x y
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply,
      zero_mul, mul_zero, add_zero]
  refine ⟨LieDerivation.add_central hd traceScalar_central traceScalar_commutator, ?_⟩
  have hne : Nonempty n :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h0 => hn (by rw [h0, Nat.cast_zero]))
  apply not_Der_of_add_central hd
  rw [traceScalar_one]
  intro h
  exact hn ((Matrix.scalar_inj (n := n)).mp (h.trans (map_zero _).symm))

end BraidedSymDerivTrace

/-! ## The identity braiding -/

/-- The identity braiding σ(x⊗y) = x⊗y, written as a binary map σ(x,y) = x. -/
def identityBraiding (x _y : A) : A := x

theorem symmetrizedProduct_id (x y : A) :
    symmetrizedProduct identityBraiding x y = x * y + x * y := rfl

/-- (Proposition 3.2(a)) When 2 is cancellable in A, the braided-symmetric
    derivations for the identity braiding are exactly the derivations. -/
theorem braidedSymmetricDerivation_id_iff_Der
    (h2 : ∀ a : A, a + a = 0 → a = 0) {D : A →+ A} :
    BraidedSymmetricDerivation identityBraiding D ↔ Der D := by
  constructor
  · intro h x y
    have hxy := h x y
    rw [symmetrizedProduct_id, symmetrizedProduct_id, symmetrizedProduct_id,
      map_add] at hxy
    -- hxy : D(xy) + D(xy) = (Dx y + Dx y) + (x Dy + x Dy)
    apply eq_of_sub_eq_zero
    apply h2
    rw [← sub_eq_zero.mpr hxy]
    abel
  · intro h x y
    rw [symmetrizedProduct_id, symmetrizedProduct_id, symmetrizedProduct_id,
      map_add, h x y]
    abel

/-- (Remark after Proposition 3.2) When 2 = 0 in A, every additive map is a
    braided-symmetric derivation for the identity braiding. -/
theorem braidedSymmetricDerivation_id_of_two_eq_zero
    (h2 : ∀ a : A, a + a = 0) (D : A →+ A) :
    BraidedSymmetricDerivation identityBraiding D := by
  intro x y
  rw [symmetrizedProduct_id, symmetrizedProduct_id, symmetrizedProduct_id,
    h2 (x * y), h2 (D x * y), h2 (x * D y), map_zero, add_zero]
