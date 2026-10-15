import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi

/-!
# The triangular algebra Tri(F₃,F₃,F₃)

Zhang and Yu (2006, *Linear Algebra Appl.* 419, "Jordan derivations of
triangular algebras") prove `JDer(T) = Der(T)` for any 2-torsion-free triangular algebra
`T = Tri(A,M,B)`, via a Peirce-decomposition argument against the
idempotents `e₁, e₂` — a genuinely structural theorem, unlike the classical
one-line `Der(A) ⊆ JDer(A)` for a general algebra (Corollary 3.5 in
[Adrabi2026]), because `T` is not prime (`e₂ T e₁ = 0`), so the usual
prime-ring route does not apply.

This file verifies the Zhang–Yu theorem concretely on the smallest interesting
triangular algebra, `T = Tri(F₃,F₃,F₃)` (the 2×2 upper-triangular matrices
over `F₃`), by exhaustive search rather than by formalizing the abstract
Peirce-decomposition proof. The search is complete, not a spot-check: `T`'s
underlying additive group has exponent 3, so every additive endomorphism of
`T` is automatically `F₃`-linear (Lean note above `ofMatrix`), hence equals
`ofMatrix d` for some 3×3 matrix `d` over `F₃`. Quantifying over all `3^9`
such matrices therefore covers every additive map `T → T`, with no subclass
gap.

This was motivated by the live "decomposition" thread in
`ledger/projects/braided-sym-deriv/state.md`: a first proposal (aligning
`σ`'s `±1`-eigenspace decomposition of `A ⊗ A` with the Peirce decomposition
of `T`) was checked by hand and does not type-check — the two decompositions
live on different spaces (`A ⊗ A`, pairs, 2 pieces vs. `T`, elements, 3
pieces). This file formalizes the fallback plan: the Zhang–Yu theorem directly,
with no reference to `σ` or the eigenspace idea.

## References

* [Adrabi2026] Adrabi, "Braided-Symmetric Derivations in Symmetric Monoidal Categories".
* Zhang, J.-H., Yu, W.-Y.: Jordan derivations of triangular algebras. Linear Algebra Appl. 419(1), 251–255 (2006).
* Cheung, W.-S.: Lie derivations of triangular algebras. Linear Multilinear Algebra 51(3), 299–310 (2003).
-/

/-- An element of `T = Tri(F₃,F₃,F₃)`: the triple `(a,m,b)` represents the
    upper-triangular matrix `[[a,m],[0,b]]`. -/
structure Tri where
  a : ZMod 3
  m : ZMod 3
  b : ZMod 3
deriving DecidableEq

/-- `Tri` is finite: it is in bijection with `ZMod 3 × ZMod 3 × ZMod 3` via
    its three fields, so `Fintype` transports across that equivalence
    (the `deriving` handler does not reach through a 3-field structure
    automatically, hence this explicit instance). -/
instance : Fintype Tri :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3 × ZMod 3)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun x => (x.a, x.m, x.b)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ## Ring structure -/

instance : Add Tri := ⟨fun x y => ⟨x.a + y.a, x.m + y.m, x.b + y.b⟩⟩
instance : Zero Tri := ⟨⟨0, 0, 0⟩⟩
instance : Neg Tri := ⟨fun x => ⟨-x.a, -x.m, -x.b⟩⟩

/-- Multiplication matches `[[a,m],[0,b]] * [[a',m'],[0,b']] = [[aa', am'+mb'],[0,bb']]`,
    the ordinary upper-triangular-matrix product. -/
instance : Mul Tri := ⟨fun x y => ⟨x.a * y.a, x.a * y.m + x.m * y.b, x.b * y.b⟩⟩
instance : One Tri := ⟨⟨1, 0, 1⟩⟩

/-! ## Peirce idempotents -/

/-- `e₁ = diag(1,0)`, the idempotent for the `A`-block. -/
def e1 : Tri := ⟨1, 0, 0⟩

/-- `e₂ = diag(0,1)`, the idempotent for the `B`-block. -/
def e2 : Tri := ⟨0, 0, 1⟩

/-- The generator of the `M`-block `e₁Te₂`. -/
def e12 : Tri := ⟨0, 1, 0⟩

theorem e1_mul_e1 : e1 * e1 = e1 := by
  decide -- explicit-proof-exempt: finite check over Tri (27 elements), e1 is idempotent by direct computation
theorem e2_mul_e2 : e2 * e2 = e2 := by
  decide -- explicit-proof-exempt: finite check over Tri (27 elements), e2 is idempotent by direct computation
theorem e1_add_e2 : e1 + e2 = 1 := by
  decide -- explicit-proof-exempt: finite check over Tri (27 elements), e1+e2 reconstructs the unit
theorem e2_mul_e1 : e2 * e1 = 0 := by
  -- The Peirce component T₂₁ = e₂Te₁ vanishes: this is what makes T
  -- non-prime and is the structural fact the Zhang–Yu argument uses.
  decide -- explicit-proof-exempt: finite check over Tri (27 elements), confirms T is not prime

/-! ## Additive endomorphisms as 3×3 matrices -/

/-- Every additive endomorphism of `T` is `F₃`-linear: `T`'s underlying
    additive group has exponent 3 (since `ZMod 3` does), so for any additive
    `D` and any `c : ZMod 3` represented by an integer `k`, `D(c • x) = D(k • x)
    = k • D(x) = c • D(x)` by additivity alone, with no separate linearity
    hypothesis needed. Hence `D` is determined by its values on the basis
    `e1, e12, e2`, packaged here as a matrix `d` with `d i j` the `j`-th
    coordinate of `D` applied to the `i`-th basis vector. -/
def ofMatrix (d : Fin 3 → Fin 3 → ZMod 3) (x : Tri) : Tri :=
  ⟨x.a * d 0 0 + x.m * d 1 0 + x.b * d 2 0,
   x.a * d 0 1 + x.m * d 1 1 + x.b * d 2 1,
   x.a * d 0 2 + x.m * d 1 2 + x.b * d 2 2⟩

/-- `D` is a Jordan derivation of `T`, as a predicate on its matrix. -/
@[reducible] def MatrixIsJordanDerivation (d : Fin 3 → Fin 3 → ZMod 3) : Prop :=
  ∀ x y : Tri,
    ofMatrix d (x * y + y * x) =
      ofMatrix d x * y + x * ofMatrix d y + ofMatrix d y * x + y * ofMatrix d x

/-- `D` is an ordinary derivation of `T`, as a predicate on its matrix. -/
@[reducible] def MatrixIsDerivation (d : Fin 3 → Fin 3 → ZMod 3) : Prop :=
  ∀ x y : Tri, ofMatrix d (x * y) = ofMatrix d x * y + x * ofMatrix d y

/-- **The Zhang–Yu theorem (2006), verified concretely on `T = Tri(F₃,F₃,F₃)`:**
    every Jordan derivation of `T` is an ordinary derivation. Since `ofMatrix`
    covers every additive endomorphism of `T` (see the note above), this is
    the complete statement `JDer(T) ⊆ Der(T)` for this algebra, not a
    subclass check — combined with `Der(T) ⊆ JDer(T)` (Corollary 3.5 of
    [Adrabi2026], true for every algebra), this gives `JDer(T) = Der(T)`,
    matching the Zhang–Yu theorem.

    Verified by exhaustive search: `3^9 = 19683` candidate matrices `d`, each
    checked against all `27 × 27 = 729` pairs `(x,y)` for both the Jordan
    identity and the ordinary Leibniz rule. This is `T` genuinely failing to
    be prime (`e₂Te₁ = 0`, `e2_mul_e1` above) doing real work: for a prime
    algebra the same equality would already follow from Brešar's classical
    route, so this file's content is specific to the triangular case. -/
theorem jordanDerivation_eq_derivation_tri :
    ∀ d : Fin 3 → Fin 3 → ZMod 3, MatrixIsJordanDerivation d → MatrixIsDerivation d := by
  native_decide -- explicit-proof-exempt: exhaustive verification, 19683 matrices × 729 pairs each (Zhang–Yu 2006 theorem, concrete instance T = Tri(F_3,F_3,F_3))

/-! ## Lie derivations: the decomposition `L = ad_x + τ`

A Lie derivation of `T` is an additive map `L` with
`L[y,z] = [L y, z] + [y, L z]` for the commutator `[y,z] = yz - zy`.
Cheung (2003) gives conditions on a triangular algebra under which every Lie
derivation has the *standard form* `L = D + τ`, with `D` a derivation and `τ`
an additive map into the centre `Z(T)` that vanishes on every commutator.
For `T = Tri(F₃,F₃,F₃)` the derivation can moreover be taken inner,
`D = ad_x : y ↦ xy - yx`, and the check below finds such an `x` for every
Lie derivation, again over all `3^9` additive maps. -/

/-- The commutator `[y,z] = yz - zy` in `T`. -/
def triComm (y z : Tri) : Tri := y * z + -(z * y)

/-- `D` is a Lie derivation of `T`, as a predicate on its matrix. -/
@[reducible] def MatrixIsLieDerivation (d : Fin 3 → Fin 3 → ZMod 3) : Prop :=
  ∀ y z : Tri, ofMatrix d (triComm y z) = triComm (ofMatrix d y) z + triComm y (ofMatrix d z)

/-- `L - ad_x` is the central part `τ` of the standard form: every value
    commutes with all of `T`, and `τ` vanishes on every commutator. -/
@[reducible] def IsStandardWith (d : Fin 3 → Fin 3 → ZMod 3) (x : Tri) : Prop :=
  (∀ y z : Tri, triComm (ofMatrix d y + -(triComm x y)) z = 0) ∧
  (∀ y z : Tri, ofMatrix d (triComm y z) + -(triComm x (triComm y z)) = 0)

/-- **Cheung's standard form (2003), verified concretely on `T = Tri(F₃,F₃,F₃)`:**
    every Lie derivation `L` of `T` is `ad_x + τ` for some `x ∈ T`, with `τ`
    central-valued and zero on commutators. The inner derivation `ad_x` is a
    derivation of any associative algebra, so this is the standard form with
    `D = ad_x`. Exhaustive: `3^9` matrices; for each Lie derivation, a search
    over the 27 choices of `x`. -/
theorem lieDerivation_standard_tri :
    ∀ d : Fin 3 → Fin 3 → ZMod 3, MatrixIsLieDerivation d → ∃ x : Tri, IsStandardWith d x := by
  native_decide -- explicit-proof-exempt: exhaustive verification, 19683 matrices, each Lie derivation searched against 27 witnesses x (Cheung 2003's standard form, concrete instance T = Tri(F_3,F_3,F_3))

/-- The central part is genuinely needed: `τ(a,m,b) = (a,0,a)` is a Lie
    derivation of `T` (it is central-valued and kills commutators, whose `a`
    entry is always 0) that is not a derivation, since `τ(e₁·e₁) = 1` while
    `τ(e₁)e₁ + e₁τ(e₁) = 2e₁`. Its matrix sends `e1 ↦ (1,0,1)` and the other
    basis vectors to 0. -/
def tauMatrix : Fin 3 → Fin 3 → ZMod 3 := fun i j => if i = 0 ∧ j ≠ 1 then 1 else 0

theorem tau_isLieDerivation : MatrixIsLieDerivation tauMatrix := by
  decide -- explicit-proof-exempt: finite check over Tri × Tri (729 pairs)

theorem tau_not_derivation : ¬ MatrixIsDerivation tauMatrix := by
  decide -- explicit-proof-exempt: finite check over Tri × Tri (729 pairs), the witness is x = y = e1
