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
