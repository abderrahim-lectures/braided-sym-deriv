import Mathlib
import References.Basic

/-!
# The Hochschild complex in low degree (Hochschild 1945, Weibel 1994)

The paper (§1, line 97; §3, lines 325--341) uses the Hochschild complex with
coefficients in the algebra itself, in low degree:

* "Hochschild 1945, §§2 and 4 defined the cocycles of an associative algebra, and
  its 1-cocycles are the derivations";
* the coboundary of a 1-cochain is `(δD)(x,y) = xD(y) - D(xy) + D(x)y`
  (Hochschild 1945, §2, Definition 2.1), so that `E_D = -δD` and the derivations
  are exactly the 1-cocycles;
* `δ ∘ δ = 0` (Weibel 1994, §9.1), so the defect `E_D` of any map is a 2-cocycle,
  which is the paper's identity (3.2);
* an inner derivation `ad_g(x) = [g,x]` is called a *principal derivation* by
  Weibel 1994, §9.2, and `ad_g` is (minus) the coboundary of the 0-cochain `g`.

The catalogue keeps the paper's convention: an `n`-cochain takes `n` arguments.
(Connes' convention, used for instance by TauCeti's cyclic-cohomology
development, shifts this by one, so its `n+1`-argument cochains agree with ours
only after the index shift.)

What is formalized is degree 0, 1 and 2, which is what the paper uses. The
general degree-`n` coboundary is the alternating sum of cofaces; it is stated in
Mathlib-free form in TauCeti's `RingTheory/CyclicCohomology/Cochain.lean` under an
incompatible toolchain, and is not reproduced here.

## Main results

* `RefHochschild.delta0`: the coboundary of a 0-cochain, `x ↦ x a - a x`.
* `RefHochschild.delta1_delta0`: `δ¹ δ⁰ = 0`.
* `RefHochschild.innerDer_eq_neg_delta0`: `ad_g = -δ⁰ g`, so the principal
  derivations of Weibel §9.2 are the 1-coboundaries.
* `RefHochschild.Cocycle1`, `Coboundary1`, `coboundary_imp_cocycle`,
  `cocycle1_iff_der`, `coboundary1_iff_inner`: the dictionary of the paper's §3.

## References

* Hochschild, G.: On the cohomology groups of an associative algebra. Ann. of
  Math. 46 (1945), 58--67, §§2 and 4, Definition 2.1.
* Weibel, C. A.: An Introduction to Homological Algebra. Cambridge Stud. Adv.
  Math. 38, Cambridge University Press (1994), §§9.1 and 9.2.
-/

namespace RefHochschild

open Ref

variable {A : Type*} [Ring A]

/-- The coboundary of a 0-cochain `a`, `x ↦ x a - a x`. A 0-cochain is an
element of `A` (Hochschild 1945, §2; Weibel 1994, §9.1). -/
def delta0 (a : A) : A →+ A where
  toFun x := x * a - a * x
  map_zero' := by simp
  map_add' x y := by simp only [add_mul, mul_add]; abel

@[simp]
theorem delta0_apply (a x : A) : delta0 a x = x * a - a * x := rfl

/-- `δ¹ δ⁰ = 0`: the coboundary of a 0-cochain is a 1-cocycle. This is the
degree-0 case of `δ ∘ δ = 0` (Weibel 1994, §9.1). -/
theorem delta1_delta0 (a x y : A) : delta1 (delta0 a) x y = 0 := by
  simp only [delta1, delta0_apply]
  noncomm_ring

/-- The inner derivation is minus the coboundary of the 0-cochain `g`. Weibel
1994, §9.2 calls `ad_g` a principal derivation; Hochschild's 1-coboundaries are
exactly these, up to the sign convention of the paper's `E_D = -δD`. -/
theorem innerDer_eq_neg_delta0 (g : A) : innerDer g = -(delta0 g) := by
  ext x
  simp only [innerDer_apply, delta0_apply, AddMonoidHom.neg_apply]
  abel

/-- The 1-cocycle condition, `δD = 0`. -/
def Cocycle1 (D : A →+ A) : Prop := ∀ x y : A, delta1 D x y = 0

/-- The 1-coboundary condition, `D = δ⁰ a` for some 0-cochain `a`. -/
def Coboundary1 (D : A →+ A) : Prop := ∃ a : A, D = delta0 a

/-- A 1-coboundary is a 1-cocycle: this is `δ² = 0` read in degree one. -/
theorem coboundary_imp_cocycle {D : A →+ A} (h : Coboundary1 D) : Cocycle1 D := by
  obtain ⟨a, rfl⟩ := h
  intro x y
  exact delta1_delta0 a x y

/-- **The 1-cocycles are the derivations** (Hochschild 1945, §2; the paper's §3
sentence "derivations are the 1-cocycles"). -/
theorem cocycle1_iff_der (D : A →+ A) : Cocycle1 D ↔ Der D :=
  delta1_eq_zero_iff_der D

/-- The 1-coboundaries are the inner derivations, up to sign (Weibel 1994, §9.2;
Hochschild 1945, §2). -/
theorem coboundary1_iff_inner {D : A →+ A} : Coboundary1 D ↔ ∃ g : A, D = -innerDer g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [innerDer_eq_neg_delta0, neg_neg]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, by rw [innerDer_eq_neg_delta0, neg_neg]⟩

/-- The paper's identity (3.2): the defect of an arbitrary map is a 2-cocycle,
`aE(b,c) - E(ab,c) + E(a,bc) - E(a,b)c = 0` (Weibel 1994, §9.1). This is
`Ref.leibnizDefect_cocycle`, restated here as the cocycle property. -/
theorem defect_is_twoCocycle (D : A →+ A) (a b c : A) :
    a * leibnizDefect D b c - leibnizDefect D (a * b) c
      + leibnizDefect D a (b * c) - leibnizDefect D a b * c = 0 :=
  leibnizDefect_cocycle D a b c

end RefHochschild
