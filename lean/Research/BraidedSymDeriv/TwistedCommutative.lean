import Mathlib

/-- The Leibniz defect `E_D(a, b) = D(ab) - D(a) b - a D(b)` of a map `D`. -/
def leibnizDefect {R : Type*} [CommRing R] (D : R → R) (a b : R) : R :=
  D (a * b) - D a * b - a * D b

/-- The defect is symmetric in a commutative ring. -/
theorem leibnizDefect_comm {R : Type*} [CommRing R] (D : R → R) (a b : R) :
    leibnizDefect D a b = leibnizDefect D b a := by
  unfold leibnizDefect
  rw [mul_comm a b]
  ring

/-- The Hochschild 2-cocycle identity for the Leibniz defect, `δE = 0`:
`a E(b,c) - E(ab,c) + E(a,bc) - E(a,b) c = 0`. It holds for every map `D`
because `E = -δD` and `δδ = 0`. -/
theorem leibnizDefect_cocycle {R : Type*} [CommRing R] (D : R → R) (a b c : R) :
    a * leibnizDefect D b c - leibnizDefect D (a * b) c + leibnizDefect D a (b * c)
      - leibnizDefect D a b * c = 0 := by
  unfold leibnizDefect
  rw [mul_assoc a b c]
  ring

/-- The mixed-parity step of the commutative twisted Herstein theorem.
`e` is the Leibniz defect of `D` at `(x, y)`. The hypotheses are the
vanishing of the defect on the three same-parity pairs `(e, xy)`, `(e, y)`
and `(x, ey)`. The conclusion is `e * e = 0`. The proof applies the cocycle
identity at `(e, x, y)` and at `(x, e, y)`. -/
theorem twisted_defect_sq_zero {R : Type*} [CommRing R] (D : R → R) (x y : R)
    (h2 : leibnizDefect D (leibnizDefect D x y) (x * y) = 0)
    (h3 : leibnizDefect D (leibnizDefect D x y) y = 0)
    (h4 : leibnizDefect D x (leibnizDefect D x y * y) = 0) :
    leibnizDefect D x y * leibnizDefect D x y = 0 := by
  have c1 := leibnizDefect_cocycle D (leibnizDefect D x y) x y
  have c2 := leibnizDefect_cocycle D x (leibnizDefect D x y) y
  rw [mul_comm x (leibnizDefect D x y)] at c2
  have hs := leibnizDefect_comm D (leibnizDefect D x y) x
  linear_combination c1 - h2 + y * hs - c2 + x * h3 + h4

namespace UV

/-! `A = K[u,v]/(u², v²)` over `K = ZMod 5`, basis `1, u, v, uv` as `Fin 4`.
`α` fixes `u` and negates `v`. `D` sends `uv` to `uv` and the rest to `0`. -/

abbrev K := ZMod 5
abbrev V := Fin 4 → K

/-- Product of basis vectors `i, j` (bitmask: bit 0 is `u`, bit 1 is `v`). -/
def bmul (i j : Fin 4) : V := fun k =>
  if i.val &&& j.val = 0 ∧ k.val = i.val ||| j.val then 1 else 0

def mul (a b : V) : V := fun k =>
  ∑ i : Fin 4, ∑ j : Fin 4, a i * b j * bmul i j k

def alpha (a : V) : V := fun k => if k.val = 2 ∨ k.val = 3 then -a k else a k
def D (a : V) : V := fun k => if k.val = 3 then a 3 else 0
def e (i : Fin 4) : V := fun k => if k = i then 1 else 0

/-- Twisted product `x·y = xy + α(y)α(x)`. -/
def tmul (a b : V) : V := mul a b + mul (alpha b) (alpha a)

/-- `D` commutes with `α`. -/
theorem D_comm_alpha : ∀ i : Fin 4, D (alpha (e i)) = alpha (D (e i)) := by
  decide  -- explicit-proof-exempt: computational falsification battery (machine witness, not a theorem proof)

/-- `D` is a derivation of the twisted product on basis pairs. -/
theorem D_twisted : ∀ i j : Fin 4,
    D (tmul (e i) (e j)) = tmul (D (e i)) (e j) + tmul (e i) (D (e j)) := by
  decide  -- explicit-proof-exempt: computational falsification battery (machine witness, not a theorem proof)

/-- `D` is not a derivation: the Leibniz rule fails at `(u, v)`. -/
theorem D_not_der : D (mul (e 1) (e 2)) ≠ mul (D (e 1)) (e 2) + mul (e 1) (D (e 2)) := by
  decide  -- explicit-proof-exempt: computational falsification battery (machine witness, not a theorem proof)

end UV

/-- Remark `rem:inner-twisted`: an additive map satisfying the Leibniz rule
satisfies the `σ_α`-twisted identity exactly when it commutes with `α`. -/
theorem der_twisted_iff_comm {R : Type*} [Ring R] (α : R ≃+* R) (D : R →+ R)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    (∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
      ↔ ∀ z, D (α z) = α (D z) := by
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    rw [one_mul, mul_one, one_mul] at h
    exact left_eq_add.mp h
  constructor
  · intro h z
    have hz := h 1 z
    rw [one_mul, mul_one, h1, zero_mul, mul_zero, map_zero, zero_add, one_mul, mul_one,
      map_add] at hz
    rw [zero_add] at hz
    exact add_left_cancel hz
  · intro h x y
    rw [map_add, h (y * x), hD x y, hD y x, map_add, map_mul, map_mul]
    abel

/-! ### Theorem `thm:twisted-commutative`, full proof

`A` is a commutative reduced ring with `2` invertible, `α` an involutive ring
automorphism, `D` an additive map commuting with `α`. -/

section Full

variable {A : Type*} [CommRing A]

/-- The Leibniz defect is additive in the first argument. -/
theorem leibnizDefect_add_left (D : A →+ A) (a a' b : A) :
    leibnizDefect D (a + a') b = leibnizDefect D a b + leibnizDefect D a' b := by
  unfold leibnizDefect
  rw [add_mul, map_add, map_add, add_mul]
  ring

/-- The Leibniz defect is additive in the second argument. -/
theorem leibnizDefect_add_right (D : A →+ A) (a b b' : A) :
    leibnizDefect D a (b + b') = leibnizDefect D a b + leibnizDefect D a b' := by
  unfold leibnizDefect
  rw [mul_add, map_add, map_add, mul_add]
  ring

/-- Proposition `prop:defect`(i) for a commutative ring: the twisted identity
gives `E(x,y) + α(E(y,x)) = 0`. -/
theorem defect_twisted (α : A ≃+* A) (D : A →+ A) (hDα : ∀ x, D (α x) = α (D x))
    (h : ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
    (x y : A) : leibnizDefect D x y + α (leibnizDefect D y x) = 0 := by
  unfold leibnizDefect
  have h' := h x y
  rw [map_add, hDα] at h'
  simp only [map_sub, map_mul] at h' ⊢
  linear_combination h'

/-- `E` is equivariant when `D` commutes with `α`. -/
theorem defect_equivariant (α : A ≃+* A) (D : A →+ A) (hDα : ∀ x, D (α x) = α (D x))
    (x y : A) : α (leibnizDefect D x y) = leibnizDefect D (α x) (α y) := by
  unfold leibnizDefect
  have hm : α x * α y = α (x * y) := (map_mul α x y).symm
  rw [hm, hDα, hDα, hDα, map_sub, map_sub, map_mul α (D x) y, map_mul α x (D y)]

/-- Same parity (`α x = s x`, `α y = s y`, `s = ±1`): the defect vanishes. -/
theorem defect_same_parity (α : A ≃+* A) (D : A →+ A) (h2 : IsUnit (2 : A))
    (hDα : ∀ x, D (α x) = α (D x))
    (h : ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
    (x y : A) (s : A) (hs : s = 1 ∨ s = -1) (hx : α x = s * x) (hy : α y = s * y) :
    leibnizDefect D x y = 0 := by
  have h1 := defect_twisted α D hDα h x y
  rw [leibnizDefect_comm D y x] at h1
  have h3 := defect_equivariant α D hDα x y
  have h4 : α (leibnizDefect D x y) = leibnizDefect D x y := by
    rw [h3]
    rcases hs with rfl | rfl
    · rw [hx, hy, one_mul, one_mul]
    · rw [hx, hy]
      unfold leibnizDefect
      rw [neg_one_mul, neg_one_mul, neg_mul_neg, map_neg, map_neg]
      ring
  rw [h4] at h1
  exact (h2.mul_right_eq_zero).mp (by rw [two_mul]; exact h1)

/-- Mixed parity (`α x = x`, `α y = -y`): the defect vanishes in a reduced ring. -/
theorem defect_mixed_parity [IsReduced A] (α : A ≃+* A) (D : A →+ A) (h2 : IsUnit (2 : A))
    (hDα : ∀ x, D (α x) = α (D x))
    (h : ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
    (x y : A) (hx : α x = x) (hy : α y = -y) : leibnizDefect D x y = 0 := by
  have h1 := defect_twisted α D hDα h x y
  rw [leibnizDefect_comm D y x] at h1
  have hz : α (leibnizDefect D x y) = -leibnizDefect D x y := eq_neg_of_add_eq_zero_right h1
  have e2 := defect_same_parity α D h2 hDα h (leibnizDefect D x y) (x * y) (-1) (Or.inr rfl)
    (by rw [hz]; ring) (by rw [map_mul, hx, hy]; ring)
  have e3 := defect_same_parity α D h2 hDα h (leibnizDefect D x y) y (-1) (Or.inr rfl)
    (by rw [hz]; ring) (by rw [hy]; ring)
  have e4 := defect_same_parity α D h2 hDα h x (leibnizDefect D x y * y) 1 (Or.inl rfl)
    (by rw [hx]; ring) (by rw [map_mul, hz, hy]; ring)
  have hsq := twisted_defect_sq_zero D x y e2 e3 e4
  exact IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hsq⟩

/-- Theorem `thm:twisted-commutative`: on a reduced commutative ring with `2`
invertible, an additive map commuting with an involutive automorphism `α` and
satisfying the `σ_α`-identity is a derivation. -/
theorem twisted_commutative [IsReduced A] (α : A ≃+* A) (hαα : ∀ x, α (α x) = x)
    (D : A →+ A) (h2 : IsUnit (2 : A)) (hDα : ∀ x, D (α x) = α (D x))
    (h : ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x))) :
    ∀ x y, D (x * y) = D x * y + x * D y := by
  intro x y
  obtain ⟨w, hw⟩ := h2.exists_right_inv
  have hw' : 2 * α w = 1 := by
    have h := congrArg α hw
    rwa [map_mul, map_ofNat, map_one] at h
  have hαw : α w = w := by
    calc α w = (2 * w) * α w := by rw [hw, one_mul]
      _ = w * (2 * α w) := by ring
      _ = w := by rw [hw', mul_one]
  have hxab : x = w * (x + α x) + w * (x - α x) := by linear_combination (-x) * hw
  have hyab : y = w * (y + α y) + w * (y - α y) := by linear_combination (-y) * hw
  have ha : α (w * (x + α x)) = 1 * (w * (x + α x)) := by
    rw [map_mul, map_add, hαw, hαα]; ring
  have hb : α (w * (x - α x)) = -1 * (w * (x - α x)) := by
    rw [map_mul, map_sub, hαw, hαα]; ring
  have hc : α (w * (y + α y)) = 1 * (w * (y + α y)) := by
    rw [map_mul, map_add, hαw, hαα]; ring
  have hd : α (w * (y - α y)) = -1 * (w * (y - α y)) := by
    rw [map_mul, map_sub, hαw, hαα]; ring
  have hE : leibnizDefect D x y = 0 := by
    have hx' : leibnizDefect D x y
        = leibnizDefect D (w * (x + α x) + w * (x - α x)) (w * (y + α y) + w * (y - α y)) := by
      rw [← hxab, ← hyab]
    have e1 := defect_same_parity α D h2 hDα h (w * (x + α x)) (w * (y + α y)) 1
      (Or.inl rfl) ha hc
    have e2 := defect_same_parity α D h2 hDα h (w * (x - α x)) (w * (y - α y)) (-1)
      (Or.inr rfl) hb hd
    have e3 := defect_mixed_parity α D h2 hDα h (w * (x + α x)) (w * (y - α y))
      (by rw [ha]; ring) (by rw [hd]; ring)
    have e4 := defect_mixed_parity α D h2 hDα h (w * (y + α y)) (w * (x - α x))
      (by rw [hc]; ring) (by rw [hb]; ring)
    rw [hx', leibnizDefect_add_left, leibnizDefect_add_right, leibnizDefect_add_right,
      leibnizDefect_comm D (w * (x - α x)) (w * (y + α y)), e1, e2, e3, e4]
    ring
  unfold leibnizDefect at hE
  linear_combination hE

end Full

/-! ### Proposition `prop:defect`, general rings

`R` need not be commutative. `E_D(x,y) = D(xy) - D(x) y - x D(y)`. -/

section Defect

variable {R : Type*} [Ring R]

/-- The Leibniz defect of an additive map on a ring. -/
def ncDefect (D : R →+ R) (a b : R) : R := D (a * b) - D a * b - a * D b

/-- `prop:defect`(i): for an automorphism `α`, a map `D` commuting with `α` satisfies the
`σ_α`-identity iff `E(x,y) + α(E(y,x)) = 0`. -/
theorem prop_defect_aut (α : R ≃+* R) (D : R →+ R) (hDα : ∀ x, D (α x) = α (D x)) :
    (∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
      ↔ ∀ x y, ncDefect D x y + α (ncDefect D y x) = 0 := by
  constructor
  · intro h x y
    have h' := h x y
    rw [map_add, hDα, ← sub_eq_zero] at h'
    unfold ncDefect
    rw [map_sub, map_sub, ← h']
    abel
  · intro h x y
    have h' := h x y
    unfold ncDefect at h'
    rw [map_sub, map_sub] at h'
    rw [map_add, hDα, ← sub_eq_zero, ← h']
    abel

/-- `prop:defect`(ii): for an involutive anti-automorphism `α`, the identity is
`E(x,y) + α(E(x,y)) = 0`. -/
theorem prop_defect_anti (α : R →+ R) (hmul : ∀ x y, α (x * y) = α y * α x)
    (D : R →+ R) (hDα : ∀ x, D (α x) = α (D x)) :
    (∀ x y, D (x * y + α (y) * α (x)) = D x * y + α y * α (D x) + (x * D y + α (D y) * α x))
      ↔ ∀ x y, ncDefect D x y + α (ncDefect D x y) = 0 := by
  constructor
  · intro h x y
    have h' := h x y
    rw [← hmul x y, ← hmul (D x) y, ← hmul x (D y), map_add, hDα, ← sub_eq_zero] at h'
    unfold ncDefect
    rw [map_sub, map_sub, ← h']
    abel
  · intro h x y
    have h' := h x y
    unfold ncDefect at h'
    rw [map_sub, map_sub] at h'
    rw [← hmul x y, ← hmul (D x) y, ← hmul x (D y), map_add, hDα, ← sub_eq_zero, ← h']
    abel

end Defect

/-! ### Proposition `prop:twisted`: witnesses on `F_3[ε]/(ε³)`

Basis `1, ε, ε²` as `Fin 3`; `α(ε) = -ε`. `D1` keeps `ε` and `ε²`, `d(ε^i) = i ε^i`. The checks
are on basis pairs; both sides of each identity are bilinear in the pair. -/

namespace TW

abbrev K := ZMod 3
abbrev V := Fin 3 → K

def mul (a b : V) : V := fun k =>
  ∑ i : Fin 3, ∑ j : Fin 3, if i.val + j.val = k.val then a i * b j else 0
def alpha (a : V) : V := fun k => if k.val = 1 then -a k else a k
def D1 (a : V) : V := fun k => if k.val = 0 then 0 else a k
def dd (a : V) : V := fun k => (k.val : K) * a k
def e (i : Fin 3) : V := fun k => if k = i then 1 else 0
def tmul (a b : V) : V := mul a b + mul (alpha b) (alpha a)

theorem D1_comm_alpha : ∀ i : Fin 3, D1 (alpha (e i)) = alpha (D1 (e i)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check on basis elements)

theorem D1_alphader : ∀ i j : Fin 3,
    D1 (mul (e i) (e j)) = mul (D1 (e i)) (alpha (e j)) + mul (alpha (e i)) (D1 (e j)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check on basis pairs)

theorem D1_not_twisted :
    D1 (tmul (e 1) (e 1)) ≠ tmul (D1 (e 1)) (e 1) + tmul (e 1) (D1 (e 1)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check at the pair (ε, ε))

theorem dd_comm_alpha : ∀ i : Fin 3, dd (alpha (e i)) = alpha (dd (e i)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check on basis elements)

theorem dd_der : ∀ i j : Fin 3,
    dd (mul (e i) (e j)) = mul (dd (e i)) (e j) + mul (e i) (dd (e j)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check on basis pairs)

theorem dd_not_alphader :
    dd (mul (e 1) (e 1)) ≠ mul (dd (e 1)) (alpha (e 1)) + mul (alpha (e 1)) (dd (e 1)) := by
  decide  -- explicit-proof-exempt: computational witness (machine check at the pair (ε, ε))

end TW
