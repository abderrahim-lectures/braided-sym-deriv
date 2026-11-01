import Mathlib

/-!
# Herstein 1976, *Rings with Involution*: involutions of a ring

The paper `paper/braided-sym-deriv.tex` (line 285) quotes
\citet[\S1.2]{Herstein1976}: an involutive anti-automorphism is an *involution of
the ring* `A` in the sense of Herstein §1.2, a map `*` with `a** = a`,
`(a + b)* = a* + b*` and `(ab)* = b* a*`.

This module formalises that notion (`RingInvolution`), the elementary identities
following from the three axioms, the dictionary with ring equivalences
`A ≃+* Aᵐᵒᵖ` whose underlying self-map squares to the identity, the transpose of
a matrix ring as Herstein's standard example, the symmetric/skew splitting
`A = A_+ ⊕ A_-` used at paper line 294, and the paper's use of an involution at
line 281: the twist `σ_α(x ⊗ y) = α(y) ⊗ α(x)` of `A ⊗ A` is an involution
exactly when `α² = id`, because `σ_α² = α² ⊗ α²`. The paper cites this entry for
a *definition* only, so there is no hypothesis-`Prop` here: every declaration is
a definition, an identity provable in any ring, or a witness of non-vacuity.
Herstein, I. N.: *Rings with Involution*, Chicago Lectures in Mathematics,
University of Chicago Press, Chicago (1976); §1.2 is the definition and the
symmetric and skew elements. Pure tensors are encoded by pairs `(x, y)`, as in
`Research/BraidedSymDeriv/BraidedSymmetric.lean`.
-/

open scoped Matrix

namespace Background.Involution

/-- An involution of a ring in the sense of Herstein 1976, §1.2: a map `*` with
`a** = a`, `(a + b)* = a* + b*` and `(ab)* = b* a*`. The paper (line 285)
records exactly this definition and calls such a map an involutive
anti-automorphism. -/
structure RingInvolution (A : Type*) [Ring A] where
  /-- The underlying map `a ↦ a*`. -/
  toFun : A → A
  /-- `(a + b)* = a* + b*` (Herstein 1976, §1.2). -/
  map_add' : ∀ a b : A, toFun (a + b) = toFun a + toFun b
  /-- `(ab)* = b* a*` (Herstein 1976, §1.2). -/
  map_mul' : ∀ a b : A, toFun (a * b) = toFun b * toFun a
  /-- `a** = a` (Herstein 1976, §1.2). -/
  involutive' : ∀ a : A, toFun (toFun a) = a

/-! ## Prelude (may be lifted) -/

section Prelude

variable {A : Type*} [Ring A]

instance instCoeFun : CoeFun (RingInvolution A) (fun _ => A → A) :=
  ⟨RingInvolution.toFun⟩

/-- `(a + b)* = a* + b*` (Herstein 1976, §1.2), as a rewrite rule. -/
@[simp] theorem star_add (s : RingInvolution A) (a b : A) : s (a + b) = s a + s b :=
  s.map_add' a b

/-- `(ab)* = b* a*` (Herstein 1976, §1.2), as a rewrite rule. -/
@[simp] theorem star_mul (s : RingInvolution A) (a b : A) : s (a * b) = s b * s a :=
  s.map_mul' a b

/-- `a** = a` (Herstein 1976, §1.2), as a rewrite rule. -/
@[simp] theorem star_star (s : RingInvolution A) (a : A) : s (s a) = a := s.involutive' a

/-- `0* = 0`, from additivity (Herstein 1976, §1.2). -/
theorem star_zero (s : RingInvolution A) : s 0 = 0 := by
  simpa using s.map_add' 0 0

/-- `(-a)* = -a*`, from additivity (Herstein 1976, §1.2). -/
theorem star_neg (s : RingInvolution A) (a : A) : s (-a) = -s a := by
  have h : s a + s (-a) = 0 := by
    rw [← s.map_add' a (-a), add_neg_cancel, star_zero]
  exact eq_neg_of_add_eq_zero_right h

/-- `(a - b)* = a* - b*`, from additivity (Herstein 1976, §1.2). -/
theorem star_sub (s : RingInvolution A) (a b : A) : s (a - b) = s a - s b := by
  rw [sub_eq_add_neg, s.map_add', star_neg, sub_eq_add_neg]

/-- `1* = 1`. Herstein 1976, §1.2 does not assume this; it follows from the three
three given axioms, since `(1 · a)* = a* · 1*` makes `1*` a right identity. -/
theorem star_one (s : RingInvolution A) : s 1 = 1 := by
  have h := s.map_mul' 1 (s 1)
  rw [one_mul, s.involutive', one_mul] at h
  exact h.symm

/-- `(aⁿ)* = (a*)ⁿ` (Herstein 1976, §1.2). -/
theorem star_pow (s : RingInvolution A) (a : A) (n : ℕ) : s (a ^ n) = (s a) ^ n := by
  induction n with
  | zero => simpa using star_one s
  | succ k ih => rw [pow_succ', s.map_mul', ih, pow_succ]

/-- An involution fixes `2 = 1 + 1` (Herstein 1976, §1.2). -/
theorem star_two (s : RingInvolution A) : s (2 : A) = 2 := by
  rw [← one_add_one_eq_two, s.map_add', star_one, one_add_one_eq_two]

/-! ## Involutions are the involutive anti-automorphisms `A ≃+* Aᵐᵒᵖ`

A bijective anti-automorphism of `A` is a ring equivalence `A ≃+* Aᵐᵒᵖ`, and
Herstein's involutions are the ones whose self-map squares to the identity;
both directions and both round trips are below. -/

/-- An involution of `A` (Herstein 1976, §1.2) read as a ring equivalence
`A ≃+* Aᵐᵒᵖ`: the anti-automorphism `a ↦ a*` composed with `MulOpposite.op`. -/
def toAntiEquiv (s : RingInvolution A) : A ≃+* Aᵐᵒᵖ where
  toFun a := MulOpposite.op (s a)
  invFun m := s m.unop
  left_inv a := by simp
  right_inv m := by rw [← MulOpposite.op_unop m]; simp
  map_add' a b := by simp
  map_mul' a b := by simp

/-- An anti-automorphism `A ≃+* Aᵐᵒᵖ` whose underlying self-map squares to the
identity is an involution in the sense of Herstein 1976, §1.2. -/
def ofAntiEquiv (e : A ≃+* Aᵐᵒᵖ) (hinv : ∀ a, (e ((e a).unop)).unop = a) :
    RingInvolution A where
  toFun a := (e a).unop
  map_add' a b := by simp
  map_mul' a b := by simp
  involutive' := hinv

/-- `toAntiEquiv` sends `a` to `op (a*)` (Herstein 1976, §1.2). -/
@[simp] theorem toAntiEquiv_apply (s : RingInvolution A) (a : A) :
    toAntiEquiv s a = MulOpposite.op (s a) := rfl

/-- `toAntiEquiv s` squares to the identity once read back through
`MulOpposite.unop` — the involutivity of Herstein 1976, §1.2. -/
theorem toAntiEquiv_sq (s : RingInvolution A) (a : A) :
    (toAntiEquiv s ((toAntiEquiv s a).unop)).unop = a := by
  simp

/-- `toAntiEquiv` then `ofAntiEquiv` gives back the involution (Herstein 1976, §1.2). -/
theorem ofAntiEquiv_toAntiEquiv (s : RingInvolution A) :
    ofAntiEquiv (toAntiEquiv s) (toAntiEquiv_sq s) = s := by
  obtain ⟨f, ha, hm, hi⟩ := s
  rfl

/-- `ofAntiEquiv` then `toAntiEquiv` gives back `e`: Herstein 1976, §1.2's
involutions are exactly these ring equivalences `A ≃+* Aᵐᵒᵖ`. -/
theorem toAntiEquiv_ofAntiEquiv (e : A ≃+* Aᵐᵒᵖ)
    (hinv : ∀ a, (e ((e a).unop)).unop = a) : toAntiEquiv (ofAntiEquiv e hinv) = e := by
  ext a
  show MulOpposite.op ((e a).unop) = e a
  exact MulOpposite.op_unop (e a)

/-- In a commutative ring the identity map is an involution in the sense of
Herstein 1976, §1.2: there an anti-automorphism is an endomorphism, so
`(ab)* = b* a*` is commutativity. This is the paper's `α = id` at line 300. -/
def idRingInvolution (B : Type*) [CommRing B] : RingInvolution B where
  toFun := id
  map_add' _ _ := rfl
  map_mul' a b := (mul_comm b a).symm
  involutive' _ := rfl

/-! ## The transpose of `Mₙ(K)`

The paper, line 285: "By `(xy)ᵀ = yᵀ xᵀ`, the transpose is an anti-automorphism
of `Mₙ(K)`"; Herstein 1976, §1.2's standard example. -/

/-- The transpose is an involution of the matrix ring `Mₙ(K)`
(Herstein 1976, §1.2; paper, line 285). -/
def matrixTranspose (n : Type*) [Fintype n] [DecidableEq n] (K : Type*) [CommRing K] :
    RingInvolution (Matrix n n K) where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_mul' := Matrix.transpose_mul
  involutive' := Matrix.transpose_transpose

/-- The transpose is genuinely anti-multiplicative and not multiplicative: on
`M₂(𝔽₂)`, `(MN)ᵀ ≠ MᵀNᵀ`, so the reversal in Herstein 1976, §1.2 cannot be dropped. -/
theorem matrixTranspose_not_mul :
    (!![1, 1; 0, 0] * !![1, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ ≠
      (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ * !![1, 0; 1, 0]ᵀ := by
  decide

/-! ## Symmetric and skew elements when `2` is invertible

The paper, line 294: "When `2` is invertible, an involutive `α` splits
`A = A_+ ⊕ A_-`, where `A_± = {x ∈ A : α(x) = ±x}`. Indeed, for `x ∈ A`,
`x = ½(x + α(x)) + ½(x - α(x))`." The sets `A_+` and `A_-` are Herstein
1976, §1.2's symmetric and skew elements. -/

section TwoInvertible

variable [Invertible (2 : A)]

/-- The half `⅟2` is central: an elementary ring identity, used below (paper, line 294). -/
theorem invOf_two_comm (a : A) : ⅟(2 : A) * a = a * ⅟(2 : A) := by
  have h : Commute (2 : A) a := by
    show (2 : A) * a = a * 2
    rw [two_mul, mul_two]
  exact Commute.invOf_left h

/-- An involution fixes `⅟2`: `2 * (⅟2)* = 1* = 1` (Herstein 1976, §1.2). -/
theorem star_invOf_two (s : RingInvolution A) : s (⅟(2 : A)) = ⅟(2 : A) := by
  have h : (2 : A) * s (⅟(2 : A)) = 1 := by
    have h1 := s.map_mul' (⅟(2 : A)) 2
    rw [invOf_mul_self, star_one, star_two] at h1
    exact h1.symm
  exact (invOf_eq_right_inv h).symm

/-- The symmetric part `½(x + x*)` of an element (paper, line 294). -/
def symmPart (s : RingInvolution A) (a : A) : A := ⅟(2 : A) * (a + s a)

/-- The skew part `½(x - x*)` of an element (paper, line 294). -/
def skewPart (s : RingInvolution A) (a : A) : A := ⅟(2 : A) * (a - s a)

/-- `½(x + x*)` is symmetric, i.e. lies in `A_+` (paper, line 294). -/
theorem star_symmPart (s : RingInvolution A) (a : A) : s (symmPart s a) = symmPart s a := by
  calc s (symmPart s a)
      = s (a + s a) * s (⅟(2 : A)) := s.map_mul' _ _
    _ = (s a + a) * ⅟(2 : A) := by rw [s.map_add', s.involutive', star_invOf_two]
    _ = (a + s a) * ⅟(2 : A) := by rw [add_comm (s a) a]
    _ = ⅟(2 : A) * (a + s a) := (invOf_two_comm _).symm
    _ = symmPart s a := rfl

/-- `½(x - x*)` is skew, i.e. lies in `A_-` (paper, line 294). -/
theorem star_skewPart (s : RingInvolution A) (a : A) : s (skewPart s a) = -skewPart s a := by
  calc s (skewPart s a)
      = s (a - s a) * s (⅟(2 : A)) := s.map_mul' _ _
    _ = (s a - a) * ⅟(2 : A) := by rw [star_sub, s.involutive', star_invOf_two]
    _ = -((a - s a) * ⅟(2 : A)) := by noncomm_ring
    _ = -(⅟(2 : A) * (a - s a)) := by rw [invOf_two_comm]
    _ = -skewPart s a := rfl

/-- The decomposition `x = ½(x + x*) + ½(x - x*)` of paper, line 294. -/
theorem symmPart_add_skewPart (s : RingInvolution A) (a : A) :
    symmPart s a + skewPart s a = a := by
  show ⅟(2 : A) * (a + s a) + ⅟(2 : A) * (a - s a) = a
  have h : ⅟(2 : A) * (a + s a) + ⅟(2 : A) * (a - s a) =
      ⅟(2 : A) * a + ⅟(2 : A) * a := by
    rw [mul_add, mul_sub]
    abel
  rw [h, ← add_mul, invOf_two_add_invOf_two, one_mul]

end TwoInvertible
end Prelude

/-! ## The twist `σ_α(x ⊗ y) = α(y) ⊗ α(x)` of the paper

The paper, §3 (lines 281--292), puts `σ_α(x ⊗ y) = α(y) ⊗ α(x)` for an involutive
automorphism or anti-automorphism `α`, and observes that `σ_α² = α² ⊗ α²`, so
`σ_α` is an involution of `A ⊗ A` exactly when `α² = id`; it is the composite of
the swap with `α ⊗ α`. At the binary level it sends the pair `(x, y)` to
`(α y, α x)`, which needs no ring structure. -/

/-- Binary encoding of `σ_α(x ⊗ y) = α(y) ⊗ α(x)` (paper, §3, line 281): a pure
tensor is encoded by the ordered pair of its two factors. -/
def sigmaAlpha {A : Type*} (α : A → A) (p : A × A) : A × A := (α p.2, α p.1)

/-- The paper, §3 after line 292: `σ_α` is the composite of the swap with `α ⊗ α`. -/
theorem sigmaAlpha_eq_swap_comp {A : Type*} (α : A → A) (p : A × A) :
    sigmaAlpha α p = (fun q : A × A => (α q.1, α q.2)) (Prod.swap p) := rfl

/-- The paper, §3 line 290: `σ_α² = α² ⊗ α²`, i.e. applying `σ_α` twice
multiplies both tensor factors by `α²`. -/
theorem sigmaAlpha_sq {A : Type*} (α : A → A) (p : A × A) :
    sigmaAlpha α (sigmaAlpha α p) = (α (α p.1), α (α p.2)) := rfl

/-- The paper, §3 lines 290--292: `σ_α` is an involution of the pair space exactly
when `α² = id`. (`σ_α` is an involution of `A ⊗ A` exactly when `α² ⊗ α² = id`,
and the paper argues that this forces `α² = id`.) -/
theorem sigmaAlpha_involutive_iff {A : Type*} (α : A → A) :
    Function.Involutive (sigmaAlpha α) ↔ ∀ x : A, α (α x) = x := by
  constructor
  · intro h x
    have hx := congrArg Prod.fst (h (x, x))
    simpa [sigmaAlpha_sq] using hx
  · intro h p
    rw [sigmaAlpha_sq]
    exact Prod.ext (h p.1) (h p.2)

section RingTwist

variable {A : Type*} [Ring A]

/-- Herstein's involution (Herstein 1976, §1.2) is an involutive
anti-automorphism, so its twist `σ_*` is an involution of `A ⊗ A`
(paper, §3, line 292). -/
theorem sigmaAlpha_ringInvolution (s : RingInvolution A) :
    Function.Involutive (sigmaAlpha s) :=
  (sigmaAlpha_involutive_iff s).2 s.involutive'

/-- The `σ_α`-symmetrized product `x ·_{σ_α} y = xy + α(y)α(x)` of the paper,
equation (3.1) at line 300. -/
def twistedProduct (α : A → A) (x y : A) : A := x * y + α y * α x

/-- Paper, §3 lines 302--304: for an anti-automorphism `α`, the twisted product
is `xy + α(xy)`. -/
theorem twistedProduct_of_anti {α : A → A} (h : ∀ x y : A, α (x * y) = α y * α x)
    (x y : A) : twistedProduct α x y = x * y + α (x * y) := by
  rw [twistedProduct, h x y]

/-- Paper, §3 lines 302--304: for an automorphism `α`, the twisted product is
`xy + α(yx)`. -/
theorem twistedProduct_of_mul {α : A → A} (h : ∀ x y : A, α (x * y) = α x * α y)
    (x y : A) : twistedProduct α x y = x * y + α (y * x) := by
  rw [twistedProduct, h y x]

end RingTwist

end Background.Involution
