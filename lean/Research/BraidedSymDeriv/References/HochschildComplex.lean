import Mathlib

import Research.BraidedSymDeriv.References.Basic

/-!
# The full Hochschild complex in low degree (companion to `Hochschild.lean`)

`Hochschild.lean` states the part of the Hochschild complex that the paper
actually uses — degrees 0, 1 and 2, with the cochains written in uncurried form
so that they plug into `Basic.lean`'s `delta1`, `delta2` and `leibnizDefect`.

This module is the fuller development of the same two references: cochains
curried and additive in each variable, the coboundary up to degree 3 with
`δ ∘ δ = 0` in degrees 0, 1 and 2, `HH^1(A,A)` as the quotient of the
1-cocycles by the 1-coboundaries, the identification of the 1-coboundaries with
the inner derivations, and two non-vacuity examples: a non-zero 2-cocycle (the
defect of a map that is not a derivation) and the non-triviality of
`HH^1(F₂[t], F₂[t])` (the formal derivative is a 1-cocycle and not a
1-coboundary, because every inner derivation of a commutative ring vanishes).

Both modules are consistent: `der_iff_ref` and `leibnizDefect_eq_ref` at the end
identify the two notions of derivation and of defect definitionally.
-/

/-!
# Hochschild 1945 and Weibel 1994: cochains, cocycles, and the Leibniz defect

This module formalizes the notions and results that `paper/braided-sym-deriv.tex`
takes from two bibliography entries:

* G. Hochschild, *On the cohomology groups of an associative algebra*, Ann. of
  Math. **46** (1945), 58--67: the cocycles of an associative algebra
  (cited at paper, line 97 as `\S\S 2 and 4`), and in particular the coboundary
  of a `1`-cochain (paper, line 332, citing `\S 2, Definition 2.1`).
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Stud. Adv.
  Math. 38, Cambridge University Press, 1994: the Hochschild complex and
  `δ \circ δ = 0` (`\S 9.1`, paper, lines 325--330), and the name *principal
  derivation* for `ad_g(x) = [g, x]` (`\S 9.2`, paper, line 176).

What the paper uses is in `\S 3`, lines 325--341:

* an `n`-cochain is a `K`-multilinear map `A^n \to A`; a `1`-cochain is a linear
  map `A \to A`, and the `1`-cocycles are exactly the derivations;
* `(\delta D)(x,y) = xD(y) - D(xy) + D(x)y`, so the Leibniz defect
  `E_D(x,y) = D(xy) - D(x)y - xD(y)` of Definition 3.1 is `-δD`;
* `δ \circ δ = 0` makes `E_D` a `2`-cocycle, the paper's identity (`eq:cocycle`)
  `aE_D(b,c) - E_D(ab,c) + E_D(a,bc) - E_D(a,b)c = 0`;
* `HH^n(A,A)` is `n`-cocycles modulo the images of `δ`, and `ad_g` is inner.

## Conventions

Weibel's complex has `C^n = Hom(A^{\otimes(n+1)}, A)`, so his cochains take
`n + 1` arguments (the Connes convention). The paper's `n`-cochains take `n`
arguments, and we follow the paper. With `n` arguments the coboundary is
`(δf)(x_1,...,x_{n+1}) = x_1 f(x_2,...,x_{n+1})
  + \sum_{i=1}^{n} (-1)^i f(x_1,...,x_ix_{i+1},...,x_{n+1})
  + (-1)^{n+1} f(x_1,...,x_n)x_{n+1}`,
which on `1`-cochains is `(δD)(x,y) = xD(y) - D(xy) + D(x)y` (paper, line 332,
Hochschild 1945, `\S 2`, Definition 2.1) and on `2`-cochains is
`(δf)(x,y,z) = xf(y,z) - f(xy,z) + f(x,yz) - f(x,y)z`. On `0`-cochains it gives
`(δa)(x) = xa - ax = -ad_a(x)`, so the `1`-coboundaries are the inner
derivations up to sign. With these signs `δ \circ δ = 0`
(`delta1_delta0`, `delta2_delta1`, `delta3_delta2`) holds.

Everything is stated for an arbitrary ring `A` and **additive** maps `A →+ A`,
which is the stronger reading the paper allows ("we say so when a result cited
below holds more generally for additive maps on rings"): no `K`-linearity is
used, so no `Algebra R A` appears. `A` is not assumed commutative or unital,
except in the concrete witness `ExamplePolynomial`.

## Main definitions

* `RefHochschildComplex.Cochain0` ... `Cochain3`: `n`-cochains as additive maps
  (Hochschild 1945, `\S 2`; Weibel 1994, `\S 9.1`).
* `RefHochschildComplex.delta0` ... `delta3`: the Hochschild coboundary in the paper's
  signs (Hochschild 1945, `\S 2`, Definition 2.1).
* `RefHochschildComplex.IsCocycle1`, `IsCoboundary1`, `Cocycle1`, `HH1`: `1`-cocycles,
  `1`-coboundaries, and `HH^1(A,A)` (Weibel 1994, `\S 9.1`).
* `RefHochschildComplex.leibnizDefect`, `Der`, `innerDer`: the paper's `E_D`
  (Definition 3.1, Cusack 1975, `\S 2`), derivations, and `ad_g`
  (Weibel 1994, `\S 9.2`).

## Main results

* `delta1_zero_iff_der`: the `1`-cocycles are exactly the derivations.
* `delta2_delta1`, `delta3_delta2`: `δ \circ δ = 0` (Weibel 1994, `\S 9.1`).
* `leibnizDefect_cocycle`: the paper's `eq:cocycle`, i.e. `E_D` is a `2`-cocycle.
* `defectCochain_apply`: `E_D = -δD`.
* `delta0_eq_neg_innerDer`, `isCoboundary_iff_exists_innerDer`: `δa = -ad_a`, and
  the `1`-coboundaries are exactly the inner derivations.
* `der_comp_innerDer`: `[D, ad_g] = ad_{D(g)}` for a derivation `D`.
* `ExamplePolynomial.hh1_nontrivial`: `HH^1(F_2[t], F_2[t])` is non-trivial, so
  the notions above are not vacuous.

Every declaration below is proved; there are no placeholders.
-/

set_option autoImplicit false

namespace RefHochschildComplex

/-! ## Prelude (may be lifted) -/

section Prelude

variable {A : Type*} [Ring A]

/-- `D` is a derivation of the ring `A`: `D(xy) = D(x)y + xD(y)` for all `x, y`
(paper, §1; the ring-level form of the paper's `K`-linear definition). -/
def Der (D : A →+ A) : Prop := ∀ x y : A, D (x * y) = D x * y + x * D y

/-- The Leibniz defect `E_D(x,y) = D(xy) - D(x)y - xD(y)` of a map `D`, the
paper's Definition 3.1 (the map itself is Cusack 1975, §2). It is `-δD`; see
`defectCochain_apply`. -/
def leibnizDefect (D : A →+ A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- The inner derivation `ad_g(x) = [g,x] = gx - xg` of `g` (paper, line 176;
Weibel 1994, §9.2, where such a map is called a *principal* derivation). -/
def innerDer (g : A) : A →+ A where
  toFun x := g * x - x * g
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]; abel

/-- `ad_g(x) = gx - xg` (Weibel 1994, §9.2). -/
@[simp] theorem innerDer_apply (g x : A) : innerDer g x = g * x - x * g := rfl

/-- Every inner derivation is a derivation (Weibel 1994, §9.2). -/
theorem innerDer_der (g : A) : Der (innerDer g) := by
  intro x y
  simp only [innerDer_apply]
  noncomm_ring

/-- `ad_{-g} = -ad_g` (elementary, in the notation of Weibel 1994, §9.2). -/
theorem innerDer_neg (g : A) : innerDer (-g) = -innerDer g := by
  ext x
  simp only [innerDer_apply, neg_mul, mul_neg, AddMonoidHom.neg_apply]
  abel

/-- In a commutative ring every inner derivation vanishes, `ad_g(x) = gx - xg = 0`
(Weibel 1994, §9.2: the principal derivations of a commutative ring are zero). -/
theorem innerDer_eq_zero_of_comm (hcomm : ∀ x y : A, x * y = y * x) (g : A) :
    innerDer g = 0 := by
  ext x
  simp only [innerDer_apply, hcomm x g, sub_self, AddMonoidHom.zero_apply]

end Prelude

/-! ## Cochains

The paper's `n`-cochain is a `K`-multilinear map `A^n → A` (paper, line 326).
Over a ring, without `K`-linearity, a cochain is encoded as a map additive in
each variable; for `n = 0` it is just an element of `A` (paper, line 327). -/

section Cochains

variable {A : Type*} [Ring A]

/-- A `0`-cochain is an element of `A` (paper, line 327, citing
Hochschild 1945, §2). -/
abbrev Cochain0 (A : Type*) : Type _ := A

/-- A `1`-cochain is an additive map `A → A` (Hochschild 1945, §2). -/
abbrev Cochain1 (A : Type*) [Ring A] : Type _ := A →+ A

/-- A `2`-cochain: additive in each variable (Hochschild 1945, §2). -/
abbrev Cochain2 (A : Type*) [Ring A] : Type _ := A →+ A →+ A

/-- A `3`-cochain: additive in each variable (Hochschild 1945, §2). -/
abbrev Cochain3 (A : Type*) [Ring A] : Type _ := A →+ A →+ A →+ A

end Cochains

/-! ## The Hochschild coboundary

The signs are those of the paper, lines 328--338, that is, Hochschild 1945, §2,
Definition 2.1: the alternating sum starts with `+` on the term that multiplies
by the first variable on the left and ends with the sign `(-1)^{n+1}` on the term
that multiplies by the last variable on the right. -/

section Coboundary

variable {A : Type*} [Ring A]

/-- `δ` on a `0`-cochain: `(δa)(x) = xa - ax` (Hochschild 1945, §2,
Definition 2.1, in degree `0`). -/
def delta0 (a : Cochain0 A) : Cochain1 A where
  toFun x := x * a - a * x
  map_zero' := by simp
  map_add' x y := by simp only [add_mul, mul_add]; abel

/-- `(δa)(x) = xa - ax` (Hochschild 1945, §2, Definition 2.1). -/
@[simp] theorem delta0_apply (a : Cochain0 A) (x : A) :
    delta0 a x = x * a - a * x := rfl

-- `mul_add` and `add_mul` are not in the default simp set; the additivity proofs
-- of the cochains below need them.
attribute [local simp] mul_add add_mul

/-- `δ` on a `1`-cochain: `(δD)(x,y) = xD(y) - D(xy) + D(x)y`
(Hochschild 1945, §2, Definition 2.1; paper, line 332). -/
def delta1 (D : Cochain1 A) : Cochain2 A where
  toFun x :=
    { toFun := fun y => x * D y - D (x * y) + D x * y
      map_zero' := by simp
      map_add' := by
        intro y z
        simp
        all_goals abel }
  map_zero' := by
    ext y
    simp
  map_add' := by
    intro x x'
    ext y
    simp
    all_goals abel

/-- `(δD)(x,y) = xD(y) - D(xy) + D(x)y` (Hochschild 1945, §2,
Definition 2.1; paper, line 332). -/
@[simp] theorem delta1_apply (D : Cochain1 A) (x y : A) :
    delta1 D x y = x * D y - D (x * y) + D x * y := rfl

/-- `δ` on a `2`-cochain: `(δf)(x,y,z) = xf(y,z) - f(xy,z) + f(x,yz) - f(x,y)z`
(Weibel 1994, §9.1; paper, line 328). -/
def delta2 (f : Cochain2 A) : Cochain3 A where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => x * f y z - f (x * y) z + f x (y * z) - f x y * z
          map_zero' := by simp
          map_add' := by
            intro z z'
            simp
            all_goals abel }
      map_zero' := by
        ext z
        simp
      map_add' := by
        intro y y'
        ext z
        simp
        all_goals abel }
  map_zero' := by
    ext y z
    simp
  map_add' := by
    intro x x'
    ext y z
    simp
    all_goals abel

/-- `(δf)(x,y,z) = xf(y,z) - f(xy,z) + f(x,yz) - f(x,y)z`
(Weibel 1994, §9.1; paper, line 328). -/
@[simp] theorem delta2_apply (f : Cochain2 A) (x y z : A) :
    delta2 f x y z = x * f y z - f (x * y) z + f x (y * z) - f x y * z := rfl

/-- `δ` on a `3`-cochain:
`(δf)(x,y,z,w) = xf(y,z,w) - f(xy,z,w) + f(x,yz,w) - f(x,y,zw) + f(x,y,z)w`
(Weibel 1994, §9.1). -/
def delta3 (f : Cochain3 A) : A →+ A →+ A →+ A →+ A where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z =>
            { toFun := fun w =>
                x * f y z w - f (x * y) z w + f x (y * z) w - f x y (z * w)
                  + f x y z * w
              map_zero' := by simp
              map_add' := by
                intro w w'
                simp
                all_goals abel }
          map_zero' := by
            ext w
            simp
          map_add' := by
            intro z z'
            ext w
            simp
            all_goals abel }
      map_zero' := by
        ext z w
        simp
      map_add' := by
        intro y y'
        ext z w
        simp
        all_goals abel }
  map_zero' := by
    ext y z w
    simp
  map_add' := by
    intro x x'
    ext y z w
    simp
    all_goals abel

/-- `(δf)(x,y,z,w) = xf(y,z,w) - f(xy,z,w) + f(x,yz,w) - f(x,y,zw) + f(x,y,z)w`
(Weibel 1994, §9.1). -/
@[simp] theorem delta3_apply (f : Cochain3 A) (x y z w : A) :
    delta3 f x y z w = x * f y z w - f (x * y) z w + f x (y * z) w
      - f x y (z * w) + f x y z * w := rfl

/-- The Leibniz defect as a `2`-cochain: `E_D = -δD` (paper, line 333). -/
def defectCochain (D : Cochain1 A) : Cochain2 A := -delta1 D

/-- The defect cochain is the Leibniz defect: `E_D = -δD` (paper, line 333;
Hochschild 1945, §2, Definition 2.1). -/
theorem defectCochain_apply (D : Cochain1 A) (x y : A) :
    defectCochain D x y = leibnizDefect D x y := by
  simp only [defectCochain, leibnizDefect, delta1_apply, AddMonoidHom.neg_apply]
  abel

/-- `δa = -ad_a`: a `1`-coboundary is the negative of an inner derivation
(Hochschild 1945, §2; Weibel 1994, §9.2). -/
theorem delta0_eq_neg_innerDer (a : Cochain0 A) : delta0 a = -innerDer a := by
  ext x
  simp only [delta0_apply, innerDer_apply, AddMonoidHom.neg_apply]
  abel

/-- `δ` is additive on `0`-cochains: the degree-`0` case of the additivity of
the Hochschild coboundary (Hochschild 1945, §2). -/
theorem delta0_add (a b : Cochain0 A) : delta0 (a + b) = delta0 a + delta0 b := by
  ext x
  simp only [delta0_apply, AddMonoidHom.add_apply]
  noncomm_ring

/-- `δ(-a) = -δa` on `0`-cochains (Hochschild 1945, §2). -/
theorem delta0_neg (a : Cochain0 A) : delta0 (-a) = -delta0 a := by
  ext x
  simp only [delta0_apply, AddMonoidHom.neg_apply]
  noncomm_ring

/-- `δ0 = 0` on `0`-cochains (Hochschild 1945, §2). -/
theorem delta0_zero : delta0 (0 : Cochain0 A) = 0 := by
  ext x
  simp only [delta0_apply, AddMonoidHom.zero_apply, mul_zero, zero_mul, sub_self]

/-- `δ \circ δ = 0` in degree `0`: the coboundary of a `0`-cochain is a
`1`-cocycle (Weibel 1994, §9.1). -/
theorem delta1_delta0 (a : Cochain0 A) : delta1 (delta0 a) = 0 := by
  ext x y
  simp only [delta1_apply, delta0_apply, AddMonoidHom.zero_apply]
  noncomm_ring

/-- `δ \circ δ = 0` in degree `1`, pointwise: `δ(δD)(x,y,z) = 0`
(Weibel 1994, §9.1). -/
theorem delta2_delta1_apply (D : Cochain1 A) (x y z : A) :
    delta2 (delta1 D) x y z = 0 := by
  simp only [delta2_apply, delta1_apply, mul_assoc]
  noncomm_ring

/-- `δ \circ δ = 0` in degree `1`: `δ(δD) = 0` (Weibel 1994, §9.1). -/
theorem delta2_delta1 (D : Cochain1 A) : delta2 (delta1 D) = 0 := by
  ext x y z
  exact delta2_delta1_apply D x y z

/-- `δ \circ δ = 0` in degree `2`, pointwise: `δ(δf)(x,y,z,w) = 0`
(Weibel 1994, §9.1). -/
theorem delta3_delta2_apply (f : Cochain2 A) (x y z w : A) :
    delta3 (delta2 f) x y z w = 0 := by
  simp only [delta3_apply, delta2_apply, mul_assoc]
  noncomm_ring

/-- `δ \circ δ = 0` in degree `2`: `δ(δf) = 0` (Weibel 1994, §9.1). -/
theorem delta3_delta2 (f : Cochain2 A) : delta3 (delta2 f) = 0 := by
  ext x y z w
  exact delta3_delta2_apply f x y z w

/-- The `1`-cocycles are exactly the derivations: `δD = 0` iff
`D(xy) = D(x)y + xD(y)` (Hochschild 1945, §2; paper, line 334). -/
theorem delta1_zero_iff_der (D : Cochain1 A) : delta1 D = 0 ↔ Der D := by
  constructor
  · intro h x y
    have h' : delta1 D x y = 0 := by
      simpa using congrArg (fun f : A →+ A →+ A => f x y) h
    have key : delta1 D x y = D x * y + x * D y - D (x * y) := by
      simp only [delta1_apply]
      abel
    rw [key] at h'
    exact (sub_eq_zero.mp h').symm
  · intro h
    ext x y
    simp only [delta1_apply, h x y, AddMonoidHom.zero_apply]
    abel

/-- **The paper's identity (`eq:cocycle`)**: the defect of any additive map is a
`2`-cocycle, `aE_D(b,c) - E_D(ab,c) + E_D(a,bc) - E_D(a,b)c = 0` for all
`a, b, c` (paper, lines 335--339, citing Weibel 1994, §9.1). -/
theorem leibnizDefect_cocycle (D : Cochain1 A) (a b c : A) :
    a * leibnizDefect D b c - leibnizDefect D (a * b) c
      + leibnizDefect D a (b * c) - leibnizDefect D a b * c = 0 := by
  have h : a * delta1 D b c - delta1 D (a * b) c + delta1 D a (b * c)
      - delta1 D a b * c = 0 := delta2_delta1_apply D a b c
  have key : ∀ x y : A, leibnizDefect D x y = -delta1 D x y := by
    intro x y
    simp only [leibnizDefect, delta1_apply]
    abel
  simp only [key]
  have hneg : a * (-(delta1 D b c)) - (-(delta1 D (a * b) c))
      + (-(delta1 D a (b * c))) - (-(delta1 D a b)) * c
      = -(a * delta1 D b c - delta1 D (a * b) c + delta1 D a (b * c)
          - delta1 D a b * c) := by
    noncomm_ring
  rw [hneg, h, neg_zero]

/-- For a derivation `D`, the commutator of `D` with the inner derivation `ad_g`
is the inner derivation `ad_{D(g)}`: `[D, ad_g] = ad_{D(g)}`. The inner
derivations form a Lie ideal of the derivations (Weibel 1994, §9.2 for the
terminology; paper, line 176). -/
theorem der_comp_innerDer (D : Cochain1 A) (hD : Der D) (g : A) :
    D.comp (innerDer g) - (innerDer g).comp D = innerDer (D g) := by
  ext x
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, innerDer_apply,
    map_sub, hD g x, hD x g]
  abel

end Coboundary

/-! ## `HH^1`: cocycles modulo coboundaries -/

section Cohomology

variable {A : Type*} [Ring A]

/-- A `1`-cochain is a `1`-cocycle when `δD = 0` (Weibel 1994, §9.1;
paper, line 329). -/
def IsCocycle1 (D : Cochain1 A) : Prop := delta1 D = 0

/-- A `1`-cochain is a `1`-coboundary when it is `δ` of a `0`-cochain
(Weibel 1994, §9.1; paper, line 330). -/
def IsCoboundary1 (D : Cochain1 A) : Prop := ∃ a : Cochain0 A, D = delta0 a

/-- Every inner derivation is a `1`-coboundary: `ad_g = -δg` (Hochschild 1945,
§2; Weibel 1994, §9.2). -/
theorem innerDer_isCoboundary (g : A) : IsCoboundary1 (innerDer g) :=
  ⟨-g, by rw [delta0_eq_neg_innerDer, innerDer_neg, neg_neg]⟩

/-- The `1`-coboundaries are exactly the inner derivations (Hochschild 1945, §2;
Weibel 1994, §9.2). -/
theorem isCoboundary_iff_exists_innerDer (D : Cochain1 A) :
    IsCoboundary1 D ↔ ∃ g : A, D = innerDer g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by rw [delta0_eq_neg_innerDer, innerDer_neg]⟩
  · rintro ⟨g, rfl⟩
    exact innerDer_isCoboundary g

/-- A `1`-coboundary is a `1`-cocycle, that is, `Inn(A) ⊆ Der(A)`: the case
`n = 1` of `δ \circ δ = 0` (Weibel 1994, §9.1). -/
theorem isCoboundary_isCocycle {D : Cochain1 A} (h : IsCoboundary1 D) :
    IsCocycle1 D := by
  obtain ⟨g, rfl⟩ := (isCoboundary_iff_exists_innerDer D).mp h
  exact (delta1_zero_iff_der _).mpr (innerDer_der g)

/-- The type of `1`-cocycles (Weibel 1994, §9.1; paper, line 329). -/
abbrev Cocycle1 (A : Type*) [Ring A] : Type _ := {D : Cochain1 A // IsCocycle1 D}

/-- Two `1`-cocycles are cohomologous when they differ by a `1`-coboundary
(Weibel 1994, §9.1; paper, line 330). -/
def HH1Rel (D E : Cocycle1 A) : Prop := ∃ a : Cochain0 A, D.1 - E.1 = delta0 a

/-- Cohomology of cocycles is reflexive (the equivalence relation of
Weibel 1994, §9.1). -/
theorem hh1Rel_refl (D : Cocycle1 A) : HH1Rel D D :=
  ⟨0, by rw [sub_self, delta0_zero]⟩

/-- Cohomology of cocycles is symmetric (the equivalence relation of
Weibel 1994, §9.1). -/
theorem hh1Rel_symm {D E : Cocycle1 A} (h : HH1Rel D E) : HH1Rel E D := by
  obtain ⟨a, ha⟩ := h
  refine ⟨-a, ?_⟩
  rw [← neg_sub, ha, delta0_neg]

/-- Cohomology of cocycles is transitive (the equivalence relation of
Weibel 1994, §9.1). -/
theorem hh1Rel_trans {D E F : Cocycle1 A} (h₁ : HH1Rel D E) (h₂ : HH1Rel E F) :
    HH1Rel D F := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  refine ⟨a + b, ?_⟩
  have ha' : D.1 = delta0 a + E.1 := sub_eq_iff_eq_add.mp ha
  have hb' : E.1 = delta0 b + F.1 := sub_eq_iff_eq_add.mp hb
  rw [ha', hb', delta0_add]
  abel

/-- The equivalence relation "differ by a `1`-coboundary" on `1`-cocycles
(Weibel 1994, §9.1; paper, line 330). -/
def hh1Setoid (A : Type*) [Ring A] : Setoid (Cocycle1 A) :=
  ⟨HH1Rel, hh1Rel_refl, hh1Rel_symm, hh1Rel_trans⟩

/-- `HH^1(A,A)`: the `1`-cocycles modulo the `1`-coboundaries
(Weibel 1994, §9.1; paper, line 330). -/
def HH1 (A : Type*) [Ring A] : Type _ := Quotient (hh1Setoid A)

/-- Two `1`-cocycles have the same class in `HH^1(A,A)` exactly when they differ
by a `1`-coboundary (Weibel 1994, §9.1). -/
theorem hh1_mk_eq_iff (D E : Cocycle1 A) :
    (Quotient.mk (hh1Setoid A) D = Quotient.mk (hh1Setoid A) E) ↔ HH1Rel D E :=
  Quotient.eq

end Cohomology

/-! ## A non-zero `2`-cocycle: the defect of a map that is not a derivation -/

namespace ExampleDefect

/-- `A = F_2 × F_2`, the smallest commutative ring in which the construction
below is visible. -/
abbrev A : Type := Fin 2 → ZMod 2

/-- The additive map `(x,y) ↦ (x,x)`, which is not a derivation
(elementary witness for paper, line 334; not a cited result). -/
def D : A →+ A where
  toFun v := fun _ => v 0
  map_zero' := by funext i; simp
  map_add' u v := by funext i; simp

/-- `p = (1,0)`: the element at which the defect of `D` is computed
(elementary witness, not a cited result). -/
def p : A := fun i => if i = 0 then 1 else 0

/-- `D` is not a derivation: `E_D(p,p) = (1,1) ≠ 0`, so the `1`-cocycles of
`delta1_zero_iff_der` are a proper subclass of the additive maps
(Hochschild 1945, §2; paper, line 334). -/
theorem not_der : ¬ Der D := by
  intro h
  have h1 := h p p
  revert h1
  decide

/-- The defect of `D` does not vanish, so the `2`-cocycle `E_D` of
`leibnizDefect_cocycle` is non-zero (paper, lines 335--339). -/
theorem leibnizDefect_ne_zero : leibnizDefect D p p ≠ 0 := by
  decide

/-- `E_D` is a non-zero `2`-cocycle: `leibnizDefect_cocycle` says it is a cocycle
and `leibnizDefect_ne_zero` says it is not zero (paper, lines 335--339, citing
Weibel 1994, §9.1). -/
theorem defectCochain_ne_zero : defectCochain D ≠ 0 := by
  intro h
  have h0 : defectCochain D p p = 0 := by rw [h]; rfl
  rw [defectCochain_apply] at h0
  exact leibnizDefect_ne_zero h0

end ExampleDefect

/-! ## `HH^1(F_2[t], F_2[t])` is non-trivial -/

namespace ExamplePolynomial

/-- The algebra `F_2[t]`. -/
abbrev A : Type := Polynomial (ZMod 2)

/-- The formal derivative `d/dt`, the standard non-zero derivation of `F_2[t]`
(Weibel 1994, §9.1, §9.2). -/
noncomputable def D : A →+ A where
  toFun := Polynomial.derivative
  map_zero' := by simp
  map_add' x y := by simp

/-- The formal derivative is a derivation, hence a `1`-cocycle
(Hochschild 1945, §2; paper, line 334). -/
theorem der : Der D := by
  intro x y
  exact Polynomial.derivative_mul

/-- The formal derivative is not the zero map, because `d/dt (t) = 1`
(elementary; Weibel 1994, §9.2). -/
theorem ne_zero : D ≠ 0 := by
  intro h
  have h1 : D Polynomial.X = 1 := Polynomial.derivative_X
  rw [h] at h1
  simp only [AddMonoidHom.zero_apply] at h1
  exact zero_ne_one h1

/-- Every inner derivation of the commutative ring `F_2[t]` vanishes
(Weibel 1994, §9.2). -/
theorem innerDer_zero (g : A) : innerDer g = 0 :=
  innerDer_eq_zero_of_comm (fun x y => mul_comm x y) g

/-- The formal derivative is not a `1`-coboundary: the `1`-coboundaries are the
inner derivations (Hochschild 1945, §2; Weibel 1994, §9.2). -/
theorem not_coboundary : ¬ IsCoboundary1 D := by
  intro h
  obtain ⟨g, hg⟩ := (isCoboundary_iff_exists_innerDer D).mp h
  rw [innerDer_zero g] at hg
  exact ne_zero hg

/-- `HH^1(F_2[t], F_2[t])` is non-trivial: the formal derivative is a `1`-cocycle
which is not a `1`-coboundary, so the classes of `hh1_mk_eq_iff` are not all
equal (Weibel 1994, §9.1, §9.2; paper, lines 325--339). -/
theorem hh1_nontrivial : Nontrivial (HH1 A) := by
  have hD : IsCocycle1 D := (delta1_zero_iff_der D).mpr der
  have h0 : IsCocycle1 (0 : Cochain1 A) := by
    show delta1 (0 : Cochain1 A) = 0
    ext x y
    simp
  refine ⟨⟨Quotient.mk (hh1Setoid A) ⟨D, hD⟩, Quotient.mk (hh1Setoid A) ⟨0, h0⟩, ?_⟩⟩
  intro heq
  have hrel : HH1Rel ⟨D, hD⟩ ⟨0, h0⟩ := (hh1_mk_eq_iff _ _).mp heq
  obtain ⟨a, ha⟩ := hrel
  rw [sub_zero] at ha
  exact not_coboundary ⟨a, ha⟩

end ExamplePolynomial

end RefHochschildComplex

/-! ## Agreement with the shared prelude

`Basic.lean` states the derivation condition and the defect in uncurried form;
the curried notions above agree with them definitionally, so the catalogue has
one notion of defect and one notion of derivation, not two. -/

namespace RefHochschildComplex

theorem der_iff_ref {A : Type*} [Ring A] (D : A →+ A) :
    Der D ↔ Ref.Der D := Iff.rfl

theorem leibnizDefect_eq_ref {A : Type*} [Ring A] (D : A →+ A) (x y : A) :
    leibnizDefect D x y = Ref.leibnizDefect D x y := rfl

end RefHochschildComplex
