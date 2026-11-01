import Mathlib
import References.Basic

/-!
# References/Nonassoc.lean -- Jacobson 1937 (Part I) and Martindale 1964

The two notions that `paper/braided-sym-deriv.tex` (v63) takes from these
bibliography entries, stated in the generality in which the paper uses them:

* Jacobson, N., *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc.
  42 (1937), 206--224, **Part I**. Cited at paper line 96 for "the derivations
  of an arbitrary nonassociative algebra", and again at line 238.
* Martindale, W. S., *Lie derivations of primitive rings*, Michigan Math. J. 11
  (1964), 183--187, **p. 183**. Cited at paper lines 98 and 266 for the
  definition of a Lie derivation.

## Encoding

The paper works with a `K`-linear involution `σ` of `A ⊗ A` and the product
`x ·_σ y = μ(x ⊗ y) + μ(σ(x ⊗ y))`. Since `Mathlib` is the only permitted
import, `σ` is encoded *binary* by a map `σ : A → A → A × A`: the pair
`σ x y = (a, b)` stands for the pure tensor `σ(x ⊗ y) = a ⊗ b`, and
`Symm σ x y = x * y + (σ x y).1 * (σ x y).2` is `μ + μ ∘ σ` on pure tensors.
This pair encoding represents every `σ` whose value on a pure tensor is again a
pure tensor, in particular all four structure-free involutions of Remark 2.4.
(The single-map encoding `σ : A → A → A` of
`Research.BraidedSymDeriv.Paper.Symm`, `x * y + σ x y * σ y x`, reads
`σ(x ⊗ y) = σ x y ⊗ σ y x`: it forces the second factor of `σ(x ⊗ y)` to be the
first factor of `σ(y ⊗ x)`, so it does not represent `-id` or `-τ`.)

## Generality

The paper's algebras are unital associative `K`-algebras and its maps are
`K`-linear. Everything below is stated for an arbitrary ring `A` with additive
maps `D : A →+ A`, as the paper allows ("we say so when a result cited below
holds more generally for additive maps on rings") and as the ring-level
convention for Jacobson 1937 and Martindale 1964 asks; over a `K`-algebra every
additive map here is `K`-linear, so nothing is lost.

## What is proved, and what is not

Proved: `BSDer_σ(A)` is the set of derivations of `(A, ·_σ)` in Jacobson's sense
(Remark 2.4, paper line 238); the four structure-free involutions as products --
`id` gives `2xy` and hence `Der` when `2` is cancellable, `τ` gives the `∘` form
`JDer`, `-id` gives the zero product and every additive map, `-τ` gives the
commutator product and the Lie derivations of Martindale; `Der ⊆ LieDer`;
`D 1 = 0` for a derivation; inner derivations are derivations and Lie
derivations. Witnesses on `ZMod 2` and on `ZMod 2 × ZMod 2` show that these
inclusions are strict, and that a nonzero nonassociative product can have a
derivation that is not a ring derivation.

Not formalized: Martindale's structure theorem (a Lie derivation of a primitive
ring with a nontrivial idempotent and characteristic `≠ 2` is `δ + τ` with `δ` a
derivation and `τ` an additive map into the centre vanishing on commutators,
Michigan Math. J. 11 (1964), 183--187, main theorem). The paper cites this entry
at p. 183 for the *definition* only and uses no theorem from it, so no theorem
is taken over here; its exact hypotheses could not be checked against the
original in this environment, and a mis-stated deep theorem is worse than none.
-/

namespace RefNonassoc

/-! ## Prelude (may be lifted) -/

section Prelude

variable {A : Type*} [Ring A]

/-- The commutator `[x, y] = xy - yx` (paper, §2). -/
def commutator (x y : A) : A := x * y - y * x

/-- A derivation of the associative product, `D(xy) = D(x)y + xD(y)` (paper, §1,
introductory definition, attributed there to Jacobson 1937, Part I). -/
def Der (D : A →+ A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- A derivation of an *arbitrary* product `mul` on `A`, with no associativity
assumption: `D(mul x y) = mul (D x) y + mul x (D y)`. This is the notion of
Jacobson 1937, Part I ("the derivations of an arbitrary nonassociative
algebra"), used at paper line 238 for the product `·_σ`; `mul` is a bare
function `A → A → A`, so nothing about associativity is assumed. It is stated
here for a ring `A` and an additive `D` (the ring-level convention for this
entry); over a `K`-algebra, `D` additive is `D` `K`-linear. -/
def NonassocDer (mul : A → A → A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (mul x y) = mul (D x) y + mul x (D y)

/-- The binary encoding of a linear map `σ : A ⊗ A → A ⊗ A`: `σ x y = (a, b)`
means `σ(x ⊗ y) = a ⊗ b`. The paper's symmetrized product
`x ·_σ y = μ(x ⊗ y) + μ(σ(x ⊗ y))` (paper, §2) becomes
`Symm σ x y = x * y + (σ x y).1 * (σ x y).2`. -/
def Symm (σ : A → A → A × A) (x y : A) : A := x * y + (σ x y).1 * (σ x y).2

/-- A braided-symmetric derivation for `σ`, that is Definition 2.1 of the paper
(identity `eq:sigma-leibniz`): `D(x ·_σ y) = D(x) ·_σ y + x ·_σ D(y)`. -/
def BSDer (σ : A → A → A × A) (D : A →+ A) : Prop :=
  ∀ x y : A, D (Symm σ x y) = Symm σ (D x) y + Symm σ x (D y)

/-- A Jordan derivation in the `∘` form, `D(x ∘ y) = D(x) ∘ y + x ∘ D(y)` with
`x ∘ y = xy + yx` (paper line 266, "`BSDer_τ(A) = JDer(A)` in every
characteristic"). The right-hand side is grouped as `Symm` groups it for the
swap, so that `bsder_swap_iff_jder` below is definitional. -/
def JDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (x * y + y * x) = (D x * y + y * D x) + (x * D y + D y * x)

/-- A Lie derivation, `D([x, y]) = [D(x), y] + [x, D(y)]` (Martindale 1964,
p. 183; paper lines 98 and 266). -/
def LieDer (D : A →+ A) : Prop :=
  ∀ x y : A, D (commutator x y) = commutator (D x) y + commutator x (D y)

/-- The inner derivation `ad_g(x) = [g, x] = gx - xg` (paper, §2). -/
def innerDer (g : A) : A →+ A where
  toFun x := g * x - x * g
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]; abel

/-- The value of `innerDer g`, by definition (paper, §2). -/
@[simp] theorem innerDer_apply (g x : A) : innerDer g x = g * x - x * g := rfl

/-- `A` is `2`-torsion-free, `2a = 0 → a = 0` (paper, §1; the paper writes
`2a` for `a + a`). -/
def TwoTorsionFree (A : Type*) [AddGroup A] : Prop := ∀ a : A, a + a = 0 → a = 0

/-- In a `2`-torsion-free additive group doubling is injective: this is the
"we divide by `2`" step of Remark 2.4 of the paper (line 266). -/
theorem eq_of_add_add_eq (h2 : TwoTorsionFree A) {a b : A} (h : a + a = b + b) : a = b := by
  have hz : (a - b) + (a - b) = 0 := by
    have h' : (a - b) + (a - b) = (a + a) - (b + b) := by abel
    rw [h', h, sub_self]
  exact sub_eq_zero.mp (h2 (a - b) hz)

end Prelude

/-! ## Jacobson 1937, Part I: derivations of a nonassociative algebra -/

section Jacobson

variable {A : Type*} [Ring A]

/-- Remark 2.4 of the paper (line 238): "`BSDer_σ(A)` is the set of derivations of
the nonassociative algebra `(A, ·_σ)`, in the sense of Jacobson 1937, Part I".
Both sides are `∀ x y, D (x ·_σ y) = D x ·_σ y + x ·_σ D y`; with the binary
encoding of `σ` they unfold to the same statement, so this is `Iff.rfl`: the
paper's content at that line is the identification of `·_σ` with the product of
Jacobson's theory, which the `symm_*` lemmas below spell out in the four
cases. -/
theorem nonassocDer_symm_iff_bsder (σ : A → A → A × A) (D : A →+ A) :
    NonassocDer (Symm σ) D ↔ BSDer σ D := Iff.rfl

/-- `σ = id`: the product is `x ·_σ y = xy + xy = 2xy` (Remark 2.4, line 266). -/
theorem symm_id (x y : A) : Symm (fun a b => (a, b)) x y = x * y + x * y := rfl

/-- `σ = τ`, the swap: `x ·_σ y = xy + yx`, the Jordan product `x ∘ y` of the
paper (Remark 2.4, line 266). -/
theorem symm_swap (x y : A) : Symm (fun a b => (b, a)) x y = x * y + y * x := rfl

/-- `σ = -id`: `x ·_σ y = xy - xy = 0`, the zero product (Remark 2.4, line 266). -/
theorem symm_negId (x y : A) : Symm (fun a b => (a, -b)) x y = 0 := by
  simp [Symm]

/-- `σ = -τ`: `x ·_σ y = xy - yx`, the commutator product `[x, y]`
(Remark 2.4, line 266). -/
theorem symm_negSwap (x y : A) : Symm (fun a b => (b, -a)) x y = commutator x y := by
  simp only [Symm, commutator]
  noncomm_ring

/-- The commutator written as the product `·_{-τ}` writes it,
`[x, y] = xy + y(-x)`; this is the form used in `bsder_negSwap_iff_lie`
(Remark 2.4 of the paper, line 266). -/
theorem commutator_eq (x y : A) : commutator x y = x * y + y * (-x) := by
  simp only [commutator]
  noncomm_ring

/-- The zero product is a nonassociative product, and every additive map is a
derivation of it (paper line 266: "every linear map is a derivation of the zero
product"). -/
theorem nonassocDer_zero (D : A →+ A) : NonassocDer (fun _ _ => (0 : A)) D := by
  intro x y
  simp

/-- Remark 2.4, case `σ = -id`: every additive map is a braided-symmetric
derivation for `-id`, because the product `·_{-id}` is zero (paper line 266:
"`BSDer_{-id}(A) = End_K(A)`"). -/
theorem bsder_negId (D : A →+ A) : BSDer (fun a b => (a, -b)) D := by
  intro x y
  simp [Symm]

/-- Remark 2.4, case `σ = -τ`: the product `·_{-τ}` is the commutator, so the
class is the space of Lie derivations of Martindale 1964, p. 183 (paper line
266: "`BSDer_{-τ}(A)` is the space of Lie derivations of `A`"). -/
theorem bsder_negSwap_iff_lie (D : A →+ A) :
    BSDer (fun a b => (b, -a)) D ↔ LieDer D := by
  constructor
  · intro h x y
    have hxy := h x y
    simp only [commutator_eq]
    exact hxy
  · intro h x y
    have hxy := h x y
    simp only [commutator_eq] at hxy ⊢
    exact hxy

/-- Remark 2.4, case `σ = τ`: the product `·_τ` is `x ∘ y = xy + yx`, so
`BSDer_τ(A) = JDer(A)` in every characteristic (paper line 266). -/
theorem bsder_swap_iff_jder (D : A →+ A) :
    BSDer (fun a b => (b, a)) D ↔ JDer D := Iff.rfl

/-- Every derivation is a Jordan derivation (paper line 266, citing Bresar 1988,
p. 1003), hence `Der(A) ⊆ BSDer_τ(A)`. -/
theorem der_jder {D : A →+ A} (h : Der D) : JDer D := by
  intro x y
  have h1 := h x y
  have h2 := h y x
  show D (x * y + y * x) = (D x * y + y * D x) + (x * D y + D y * x)
  rw [map_add, h1, h2]
  abel

/-- Remark 2.4, case `σ = id`: the product is `2xy`, so on a `2`-torsion-free
algebra the class is `Der(A)` (line 266: "if `char K ≠ 2`, we divide by `2` and
get `BSDer_id(A) = Der(A)`"). -/
theorem bsder_id_iff_der (h2 : TwoTorsionFree A) (D : A →+ A) :
    BSDer (fun a b => (a, b)) D ↔ Der D := by
  constructor
  · intro h x y
    have h1 : D (x * y + x * y) = (D x * y + D x * y) + (x * D y + x * D y) := h x y
    rw [map_add] at h1
    have hz : D (x * y) + D (x * y) =
        (D x * y + x * D y) + (D x * y + x * D y) := by
      rw [h1]; abel
    exact eq_of_add_add_eq h2 hz
  · intro h x y
    show D (x * y + x * y) = (D x * y + D x * y) + (x * D y + x * D y)
    rw [map_add, h x y]
    abel

end Jacobson

/-! ## Martindale 1964, p. 183: Lie derivations -/

section Martindale

variable {A : Type*} [Ring A]

/-- Every derivation is a Lie derivation, by the Leibniz rule for the commutator
(paper line 98). -/
theorem der_lie {D : A →+ A} (h : Der D) : LieDer D := by
  intro x y
  have h1 := h x y
  have h2 := h y x
  show D (x * y - y * x) = (D x * y - y * D x) + (x * D y - D y * x)
  rw [map_sub, h1, h2]
  abel

/-- Every derivation satisfies `D 1 = 0`, since
`D 1 = D (1 · 1) = 2 D 1` (paper line 175). -/
theorem der_one {D : A →+ A} (h : Der D) : D 1 = 0 := by
  have h1 : D 1 = D 1 + D 1 := by
    have h' := h 1 1
    simpa using h'
  have h2 : D 1 + 0 = D 1 + D 1 := by
    rw [add_zero]
    exact h1
  exact (add_left_cancel h2).symm

/-- The inner derivation `ad_g(x) = [g, x]` is a derivation (paper, §2). -/
theorem innerDer_der (g : A) : Der (innerDer g) := by
  intro x y
  simp only [innerDer_apply]
  noncomm_ring

/-- Inner derivations are Lie derivations: they satisfy the Leibniz rule for the
commutator (Martindale 1964, p. 183; paper, §2). -/
theorem innerDer_lie (g : A) : LieDer (innerDer g) := der_lie (innerDer_der g)

end Martindale

/-! ## Witnesses

Remark 2.4 of the paper asserts that the classes above are strictly larger than
`Der(A)` for `A ≠ 0`; the examples below are concrete. -/

section Witness

/-- On `ZMod 2` the identity map is a derivation of the zero product, in the
sense of Jacobson 1937, Part I (Remark 2.4, line 266). -/
theorem zmod2_id_nonassocDer_zero :
    NonassocDer (fun _ _ => (0 : ZMod 2)) (AddMonoidHom.id (ZMod 2)) :=
  nonassocDer_zero _

/-- The identity map of `ZMod 2` is a Lie derivation: `ZMod 2` is commutative,
so both sides of `D([x, y]) = [D(x), y] + [x, D(y)]` vanish. -/
theorem zmod2_id_lie : LieDer (AddMonoidHom.id (ZMod 2)) := by
  intro x y
  show x * y - y * x = (x * y - y * x) + (x * y - y * x)
  rw [mul_comm x y, sub_self]
  simp

/-- The identity map of `ZMod 2` is not a derivation, since it sends `1` to `1`
while every derivation sends `1` to `0` (paper line 175). Together with
`zmod2_id_lie` and `zmod2_id_nonassocDer_zero` this makes the inclusions
`Der ⊊ LieDer` and `Der ⊊ BSDer_{-id}` strict, as Remark 2.4 (line 266)
asserts. -/
theorem zmod2_id_not_der : ¬ Der (AddMonoidHom.id (ZMod 2)) := by
  intro h
  have h1 : (1 : ZMod 2) = 0 := by
    have h' := der_one h
    simpa only [AddMonoidHom.id_apply] using h'
  exact one_ne_zero h1

/-- The additive projection `(x₁, x₂) ↦ (x₁, 0)` on `ZMod 2 × ZMod 2`. -/
def proj : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun x := (x.1, 0)
  map_zero' := rfl
  map_add' x y := by ext <;> simp

/-- A nonassociative product on `ZMod 2 × ZMod 2`: `x · y = (x₁y₂, 0)`. -/
def nassocMul (x y : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (x.1 * y.2, 0)

/-- The product `nassocMul` is not associative, so Jacobson's generality (an
arbitrary nonassociative algebra) is needed for it. -/
theorem nassocMul_not_associative :
    ∃ x y z : ZMod 2 × ZMod 2,
      nassocMul (nassocMul x y) z ≠ nassocMul x (nassocMul y z) := by
  refine ⟨(1, 1), (1, 1), (1, 1), ?_⟩
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

/-- The projection `proj` is a derivation of `nassocMul` in the sense of Jacobson
1937, Part I: the product already lands in the first coordinate, so the Leibniz
rule holds. -/
theorem proj_nonassocDer : NonassocDer nassocMul proj := by
  intro x y
  ext <;> simp [nassocMul, proj]

/-- The projection `proj` is not a derivation of the ring `ZMod 2 × ZMod 2`: it
sends `1` to `(1, 0) ≠ 0`, while every derivation sends `1` to `0` (paper line
175). So a nonzero nonassociative product can have a derivation that is not a
ring derivation. -/
theorem proj_not_der : ¬ Der proj := by
  intro h
  have h1 : (1 : ZMod 2) = 0 := congrArg Prod.fst (der_one h)
  exact one_ne_zero h1

end Witness


/-! ## Bridge to the shared prelude

`Basic.lean` states the same classes of maps with the same formulas; the local
versions are kept because the pair encoding of the braiding and its lemmas are
stated in their own vocabulary, and the two definitions agree definitionally. -/

theorem der_iff_ref {A : Type*} [Ring A] (D : A →+ A) : Der D ↔ Ref.Der D := Iff.rfl

theorem jder_iff_ref {A : Type*} [Ring A] (D : A →+ A) : JDer D ↔ Ref.JDer D := by
  simp only [JDer, Ref.JDer, Ref.jordan]

theorem lieDer_iff_ref {A : Type*} [Ring A] (D : A →+ A) : LieDer D ↔ Ref.LieDer D := by
  simp only [LieDer, Ref.LieDer, commutator, Ref.commutator]

theorem twoTorsionFree_iff_ref {A : Type*} [AddGroup A] :
    TwoTorsionFree A ↔ Ref.TwoTorsionFree A := Iff.rfl

end RefNonassoc
