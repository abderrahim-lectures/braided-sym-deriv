import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

namespace BraidedSymDerivCounterexamples

/-! ## F1: Theorem 4.3 (trivial-extension extension) is false

A = F₃[ε]/(ε³) with elements (a, b, c) = a + bε + cε², stored as nested
pairs (a, (b, c)). D(a,b,c) = (b, 2c, 0) is a genuine derivation with D(ε)=1.
u = (ε, 0), v = (0, δ_ε). The flip braiding condition fails at y = ε. -/

-- The underlying algebra F₃[ε]/(ε³): elements are triples (a, b, c) over
-- ZMod 3, read as a + bε + cε² (a "small" finite ring, small enough for
-- `decide`/`native_decide` to check universally quantified statements
-- about it by brute enumeration).
abbrev A3 := ZMod 3 × ZMod 3 × ZMod 3

def addA (x y : A3) : A3 := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)
-- Componentwise addition, matching addition of polynomials modulo ε³.

def mulA (x y : A3) : A3 :=
  (x.1 * y.1,
   -- Coefficient of ε: a₁b₂ + a₂b₁ (cross terms with ε¹).
   x.1 * y.2.1 + x.2.1 * y.1,
   -- Coefficient of ε²: a₁b₃ + a₂b₂ + a₃b₁; any term with ε³ or higher
   -- (e.g. a₂b₂·ε² is already accounted for; a₂b₃·ε³ and higher vanish
   -- since ε³ = 0 in this quotient, so those terms are simply omitted).
   x.1 * y.2.2 + x.2.1 * y.2.1 + x.2.2 * y.1)
-- This is exactly polynomial multiplication in F₃[ε] truncated at degree 2,
-- i.e. multiplication in the quotient ring F₃[ε]/(ε³).

def zeroA : A3 := (0, 0, 0)
def oneA : A3 := (1, 0, 0)
def eps : A3 := (0, 1, 0)
-- eps represents ε itself.
def eps2 : A3 := (0, 0, 1)
-- eps2 represents ε².

/-- Derivative D(1)=0, D(ε)=1, D(ε²)=2ε. -/
def D (v : A3) : A3 := (v.2.1, 2 * v.2.2, 0)
-- Formal differentiation: d/dε(a + bε + cε²) = b + 2cε, encoded as
-- (b, 2c, 0). This is the genuine derivation witness for F1.

/-- Functionals f = (f(1), f(ε), f(ε²)); eta-eval f (a+bε+cε²) = f1·a + f2·b + f3·c. -/
abbrev Func := ZMod 3 × ZMod 3 × ZMod 3
-- A functional on A3 is determined by its three values on the basis
-- {1, ε, ε²}; represented as a triple in the same shape as A3 elements
-- themselves, but interpreted as coefficients of a linear functional, not
-- as a ring element.

def evalF (f : Func) (v : A3) : ZMod 3 := f.1 * v.1 + f.2.1 * v.2.1 + f.2.2 * v.2.2
-- Evaluates the functional f at the algebra element v by pairing
-- coefficientwise and summing: this is the natural bilinear pairing
-- Func × A3 → ZMod 3.

def zeroF : Func := (0, 0, 0)

def addF (f g : Func) : Func := (f.1 + g.1, f.2.1 + g.2.1, f.2.2 + g.2.2)
-- Pointwise addition of functionals, componentwise on their coefficients.

/-- Left bimodule action (a·g)(y) = g(y·a). -/
def leftAct (a : A3) (g : Func) : Func :=
  -- (a·g) is the functional whose value at each basis vector 1, ε, ε² is
  -- g evaluated at that basis vector multiplied by a on the right, so
  -- (a·g)(1) = g(1·a) = g(a), etc.
  (evalF g (mulA oneA a), evalF g (mulA eps a), evalF g (mulA eps2 a))

/-- Right bimodule action (f·b)(y) = f(b·y). -/
def rightAct (f : Func) (b : A3) : Func :=
  -- Mirror image of leftAct: (f·b)(y) = f(by), with b multiplied on the
  -- left of each basis vector before evaluating f.
  (evalF f (mulA b oneA), evalF f (mulA b eps), evalF f (mulA b eps2))

/-- D*f: (D*(f))(y) = f(D(y)). -/
def dualD (f : Func) : Func :=
  -- The dual (transpose) action of D on functionals: precompose f with D
  -- on each basis vector.
  (evalF f (D oneA), evalF f (D eps), evalF f (D eps2))

-- T = A ⋉ Func is the trivial extension of A3 by its own dual bimodule
-- Func, the object Theorem 4.3 makes a claim about.
abbrev T := A3 × Func

def addT (u v : T) : T := (addA u.1 v.1, addF u.2 v.2)
-- Addition in the trivial extension is componentwise on the algebra part
-- and the module part.

def mulT (u v : T) : T := (mulA u.1 v.1, addF (leftAct u.1 v.2) (rightAct u.2 v.1))
-- Trivial-extension multiplication: (a,f)(b,g) = (ab, a·g + f·b), the
-- standard formula for A ⋉ M with the module part carrying no self-product.

def dtilde (u : T) : T := (D u.1, dualD u.2)
-- The candidate extension D̃ of D to T = A ⋉ Func, acting as D on the
-- algebra part and as the dual action of D on the module part — this is
-- exactly the map Theorem 4.3 claimed extends D to a derivation, and
-- disproving that claim is F1's purpose.

def symT (u v : T) : T := addT (mulT u v) (mulT v u)
-- The Jordan-symmetrized product uv + vu in T, used to state the flip-
-- braiding (Jordan-derivation) condition D̃ is tested against.

/-- δ_ε : Kronecker functional killing 1 and ε², with δ(ε) = 1. -/
def deltaEps : Func := (0, 1, 0)
-- The dual basis vector to ε: evalF deltaEps picks out exactly the
-- ε-coefficient of whatever A3 element it is applied to.

def u0 : T := (eps, zeroF)
-- u0 = (ε, 0) in T, the algebra-only witness element named in the header.
def v0 : T := (zeroA, deltaEps)
-- v0 = (0, δ_ε) in T, the module-only witness element.

/-- Flip-braiding condition, evaluated to Bool. -/
def cond (u v : T) : Bool :=
  -- Tests whether D̃(u ·_σ v) = D̃(u) ·_σ v + u ·_σ D̃(v) for the swap
  -- braiding's symmetrized product symT, i.e. whether D̃ is a
  -- braided-symmetric derivation at the specific pair (u, v).
  decide (dtilde (symT u v) = addT (symT (dtilde u) v) (symT u (dtilde v)))

/-- D is additive and satisfies Leibniz: a genuine derivation. -/
example : (∀ a b : A3, D (addA a b) = addA (D a) (D b)) ∧
          (∀ a b : A3, D (mulA a b) = addA (mulA (D a) b) (mulA a (D b))) := by
  -- Both universally quantified claims range over the 27-element ring A3,
  -- so `decide` settles them by exhaustive enumeration of all 27×27 pairs;
  -- this establishes D is a genuine derivation of A3, the premise F1 needs
  -- before it can say anything about extending D.
  decide  -- explicit-proof-exempt: computational falsification battery (machine witness, not a theorem proof)

-- Witness values at y = ε: LHS second component = 2, RHS second component = 0.
-- This #eval prints the two sides of the flip-braiding condition's
-- ε-coefficient directly, as a human-readable cross-check of the Bool
-- result computed by `cond` below.
#eval (evalF (dualD (addF (leftAct eps deltaEps) (rightAct deltaEps eps))) eps,
       evalF (addF
         (addF (addF (leftAct oneA deltaEps) (rightAct deltaEps oneA))
               (leftAct eps (dualD deltaEps)))
         (rightAct (dualD deltaEps) eps)) eps)

/-- Falsification: the braided-symmetric condition fails at (u0, v0). -/
example : cond u0 v0 = false := by
  -- `native_decide` compiles `cond u0 v0` to native code and evaluates it,
  -- rather than reducing the `decide` kernel term symbolically; this is
  -- the actual F1 falsification of Theorem 4.3's extension claim.
  native_decide

/-! ## F2: Proposition 3.4(b) is false

A = M₂(F₃), α = transpose, g = E₁₂ − E₂₁ (skew-symmetric).
D_g(x) = gx − xg commutes with α, is braided-symmetric for σ_α,
yet it is not an α-derivation. -/

-- 2×2 matrices over F₃, the ambient algebra for the F2 counterexample.
abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)

def gM : M2 := fun i j =>
  match (i.val, j.val) with
  | (0, 1) => (1 : ZMod 3)
  | (1, 0) => (-1 : ZMod 3)
  | _ => 0
-- gM = E₁₂ − E₂₁, the skew-symmetric matrix named in the header, used to
-- build the inner-derivation-like map Dm below.

def e11 : M2 := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => (1 : ZMod 3)
  | _ => 0
-- The matrix unit E₁₁, used as a test input in the #eval witness below.

def e12 : M2 := fun i j =>
  match (i.val, j.val) with
  | (0, 1) => (1 : ZMod 3)
  | _ => 0
-- The matrix unit E₁₂, the other test input for the #eval witness.

def trans (x : M2) : M2 := fun i j => x j i
-- The transpose map, playing the role of the involutive automorphism α.

def Dm (x : M2) : M2 := gM * x - x * gM
-- Dm(x) = [g, x] = gx − xg, the commutator-with-g map; this is an inner
-- derivation of the ordinary product, tested here against the α-derivation
-- and braided-symmetric identities instead.

/-- σ_α(x ⊗ y) = α(y) ⊗ α(x): symmetrized product xy + α(y)α(x). -/
def symp (x y : M2) : M2 := x * y + trans y * trans x
-- The α-twisted symmetrized product ·_σα on M2, following the general
-- formula x·_σy = xy + σ(x,y)σ(y,x) instantiated at σ(x,y) = α(y)⊗α(x).

-- Witness: at (E₁₁, E₁₂) the α-derivation rule fails (LHS ≠ RHS).
-- Human-readable printout of both sides of the α-derivation identity
-- Dm(xy) = Dm(x)α(y) + α(x)Dm(y) at (x,y) = (E₁₁, E₁₂), to be compared by
-- eye against the Bool results computed below.
#eval (Dm (e11 * e12), Dm e11 * trans e12 + trans e11 * Dm e12)

/-- Dm satisfies the α-derivation rule for no pair (x, y). -/
def isAlphaDeriv : Bool :=
  -- Quantifies over all 3^4 = 81 matrices for both x and y (6561 pairs, an
  -- enumeration small enough for `decide`); this is the negative half of
  -- the F2 falsification.
  decide (∀ x y : M2, Dm (x * y) = Dm x * trans y + trans x * Dm y)

/-- Dm is braided-symmetric for σ_α. -/
def isBraidedSym : Bool :=
  -- The positive half of F2: Dm does satisfy the braided-symmetric Leibniz
  -- rule for the α-twisted braiding, checked over all pairs.
  decide (∀ x y : M2, Dm (symp x y) = symp (Dm x) y + symp x (Dm y))

/-- Dm commutes with the transpose. -/
def commutesAlpha : Bool :=
  decide (∀ x : M2, trans (Dm x) = Dm (trans x))

/-- Dm is a derivation. -/
def isDerivation : Bool :=
  -- Included for completeness/contrast: Dm is (as expected of any
  -- commutator map) an ordinary derivation of the untwisted product too.
  decide (∀ x y : M2, Dm (x * y) = Dm x * y + x * Dm y)

-- Prints the full (α-deriv, braided-sym, commutes-with-α, derivation)
-- tuple in one line, matching the tuple order quoted in the paper's
-- Example (§5, counterexamples): expected (false, true, true, true).
#eval (isAlphaDeriv, isBraidedSym, commutesAlpha, isDerivation)

/-! ## F2b: the surviving inclusion (α-derivation ⇒ braided-symmetric ∧ α-commuting) is false (v5)

F2a refuted the converse in Prop 3.4(b). Referee review 02 reconstructed that the
INCLUSION direction survives: every α-derivation is braided-symmetric and commutes
with α. F2b refutes the inclusion too. A = F₃[ε]/(ε³), same (a, (b, c)) = a + bε + cε²
encoding as F1, α(ε) = −ε (an involution and an algebra automorphism). D2(1) = 0,
D2(ε) = ε, D2(ε²) = ε²:  D2(a, b, c) = (0, b, c). D2 is a genuine α-derivation and
commutes with α, yet is not braided-symmetric for σ_α: at (ε, ε), with x ·_σ y = xy + α(y)α(x),
LHS D2(ε ·_σ ε) = D2(2ε²) = 2ε² ≠ RHS ε ·_σ ε + ε ·_σ ε = 4ε² = ε² (char 3). -/

/-- α(ε) = −ε on F₃[ε]/(ε³): α(a, b, c) = (a, −b, c). -/
def alphaA (v : A3) : A3 := (v.1, -v.2.1, v.2.2)
-- Fixes the constant and ε² coefficients, negates the ε coefficient: this
-- is a ring automorphism because ε ↦ −ε extends multiplicatively (ε² is
-- fixed since (−ε)² = ε²) and is its own inverse.

/-- D2(1) = 0, D2(ε) = ε, D2(ε²) = ε², i.e. D2(a, b, c) = (0, b, c). -/
def D2 (v : A3) : A3 := (0, v.2.1, v.2.2)
-- The F2b witness map: kills the constant term, is the identity on the ε
-- and ε² coefficients.

/-- σ_α-symmetrized product x ·_σ y = xy + α(y)α(x). -/
def sympA (x y : A3) : A3 := addA (mulA x y) (mulA (alphaA y) (alphaA x))
-- Same general formula as symp above, instantiated for A3 and alphaA.

/-- α is an involution and a ring automorphism (so σ_α is a braiding). -/
def alphaInvolutive : Bool :=
  -- Checks α∘α = id, α additive, and α multiplicative simultaneously, all
  -- three conjuncts required for σ_α to be a genuine braiding on A3.
  decide (∀ x y : A3, (alphaA (alphaA x) = x) ∧
    (alphaA (addA x y) = addA (alphaA x) (alphaA y)) ∧
    (alphaA (mulA x y) = mulA (alphaA x) (alphaA y)))

/-- D2 is additive. -/
def D2Additive : Bool := decide (∀ x y : A3, D2 (addA x y) = addA (D2 x) (D2 y))

/-- D2 satisfies the α-derivation rule D(xy) = D(x)α(y) + α(x)D(y). -/
def isAlphaDerivA : Bool :=
  decide (∀ x y : A3, D2 (mulA x y) = addA (mulA (D2 x) (alphaA y)) (mulA (alphaA x) (D2 y)))

/-- D2 commutes with α. -/
def commutesAlphaA : Bool :=
  decide (∀ x : A3, alphaA (D2 x) = D2 (alphaA x))

/-- D2 is braided-symmetric for σ_α. -/
def isBraidedSymA : Bool :=
  -- This is the conjunct F2b needs to come out false, refuting the
  -- referee's reconstructed inclusion direction.
  decide (∀ x y : A3, D2 (sympA x y) = addA (sympA (D2 x) y) (sympA x (D2 y)))

-- Witness at (ε, ε): LHS = 2ε² = (0, (0, 2)), RHS = ε² = (0, (0, 1)).
-- Direct printout of the specific failing instance, matching the by-hand
-- computation given in the paper's Example (§5).
#eval (D2 (sympA eps eps), addA (sympA (D2 eps) eps) (sympA eps (D2 eps)))

-- Falsification: D2 is an alpha-derivation that commutes with alpha, but is not
-- braided-symmetric for sigma_alpha.
-- Prints the full 5-tuple in the same order the paper's Example quotes it:
-- expected (true, true, true, true, false).
#eval (alphaInvolutive, D2Additive, isAlphaDerivA, commutesAlphaA, isBraidedSymA)

/-- Machine witness: (α-involution, additive, α-deriv, α-comm, BS) = (tt, tt, tt, tt, ff). -/
example : (alphaInvolutive, D2Additive, isAlphaDerivA, commutesAlphaA, isBraidedSymA)
        = (true, true, true, true, false) := by
  -- Records the exact tuple as a checked proposition, not just a printed
  -- #eval, so a future change to any of the five Bool definitions above
  -- that breaks this witness fails the build instead of silently going
  -- unnoticed.
  native_decide


/-! ## v16: the Euler derivation on the same algebra

d(a + bε + cε²) = bε + 2cε² is a derivation commuting with α, so it lies in
the twisted class by Proposition prop:defect, but it is not an α-derivation.
This replaces the transpose witness, which used an anti-automorphism. -/

def dE (v : A3) : A3 := (0, v.2.1, 2 * v.2.2)

/-- dE satisfies the ordinary Leibniz rule. -/
def isDerivE : Bool :=
  decide (∀ x y : A3, dE (mulA x y) = addA (mulA (dE x) y) (mulA x (dE y)))

/-- dE commutes with α. -/
def commutesAlphaE : Bool := decide (∀ x : A3, alphaA (dE x) = dE (alphaA x))

/-- dE is braided-symmetric for σ_α. -/
def isBraidedSymE : Bool :=
  decide (∀ x y : A3, dE (sympA x y) = addA (sympA (dE x) y) (sympA x (dE y)))

/-- dE satisfies the α-derivation rule. -/
def isAlphaDerivE : Bool :=
  decide (∀ x y : A3, dE (mulA x y) = addA (mulA (dE x) (alphaA y)) (mulA (alphaA x) (dE y)))

#eval (isDerivE, commutesAlphaE, isBraidedSymE, isAlphaDerivE)

/-- Machine witness: (derivation, α-comm, BS, α-deriv) = (tt, tt, tt, ff). -/
example : (isDerivE, commutesAlphaE, isBraidedSymE, isAlphaDerivE)
        = (true, true, true, false) := by
  -- Same pattern as the D2 witness above: the tuple is a checked
  -- proposition, so a change that breaks the witness fails the build.
  native_decide

/-! ## Example 5.1 (v5): the dual numbers K[ε]/(ε²) — the honest computation

Every map D(a + bε) = bδ (δ ∈ K) is both an ordinary derivation and a Jordan
derivation, in EVERY characteristic (referee M1/M2's char-2 restriction is its own
slip). Machine instances: ZMod 5 and ZMod 2, checking all δ ∈ K. With α(ε) = −ε
on ZMod 5, D(a + bε) = bε is an α-derivation, commutes with α, and IS braided-
symmetric for σ_α — the small case where the inclusion genuinely holds. -/

-- Dual numbers over ZMod 5: pairs (a, b) read as a + bε with ε² = 0.
abbrev DN := ZMod 5 × ZMod 5

def addDN (x y : DN) : DN := (x.1 + y.1, x.2 + y.2)

def mulDN (x y : DN) : DN := (x.1 * y.1, x.1 * y.2 + x.2 * y.1)
-- (a+bε)(c+dε) = ac + (ad+bc)ε, since ε² = 0 drops the bd·ε² term entirely.

/-- The Jordan product xy + yx on dual numbers. -/
def sympDN (x y : DN) : DN := addDN (mulDN x y) (mulDN y x)
-- The standard-braiding symmetrized product on DN, used to test the
-- ordinary Jordan-derivation identity below.

/-- D(a + bε) = b·δ with parameter δ. -/
def Dd (δ : ZMod 5) (v : DN) : DN := (0, δ * v.2)
-- A one-parameter family of maps, all of the shape "kill the constant
-- term, scale the ε-coefficient by δ" — this is the general form every
-- derivation of the dual numbers takes.

/-- For every δ, D(a + bε) = bδ is a Jordan derivation over ZMod 5. -/
def dn_jordan_all : Bool :=
  -- Quantifies over all 5 choices of δ and all pairs x, y in the 25-element
  -- ring, so 5×25×25 = 3125 instances checked by `decide`.
  decide (∀ δ : ZMod 5, ∀ x y : DN,
    Dd δ (sympDN x y) = addDN (sympDN (Dd δ x) y) (sympDN x (Dd δ y)))

-- Dual numbers over ZMod 2 (characteristic 2), the case the referee
-- claimed needed a separate restriction; DN2 re-runs the same check there.
abbrev DN2 := ZMod 2 × ZMod 2

def addDN2 (x y : DN2) : DN2 := (x.1 + y.1, x.2 + y.2)

def mulDN2 (x y : DN2) : DN2 := (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

def sympDN2 (x y : DN2) : DN2 := addDN2 (mulDN2 x y) (mulDN2 y x)

def Dd2 (δ : ZMod 2) (v : DN2) : DN2 := (0, δ * v.2)

/-- For every δ, D(a + bε) = bδ is a Jordan derivation over ZMod 2 (char 2). -/
def dn2_jordan_all : Bool :=
  -- Same family and same check as dn_jordan_all, but over the 4-element
  -- ring ZMod 2 × ZMod 2 instead of the 25-element one: this is the
  -- char-2 case the referee's M1/M2 restriction claimed would fail.
  decide (∀ δ : ZMod 2, ∀ x y : DN2,
    Dd2 δ (sympDN2 x y) = addDN2 (sympDN2 (Dd2 δ x) y) (sympDN2 x (Dd2 δ y)))

-- α(ε) = −ε on dual numbers.
def alphaDN (v : DN) : DN := (v.1, -v.2)
-- Negates the ε-coefficient, fixes the constant term: an involutive
-- automorphism of DN since ε² = 0 is preserved trivially.

/-- σ_α-symmetrized product on dual numbers. -/
def sympADN (x y : DN) : DN := addDN (mulDN x y) (mulDN (alphaDN y) (alphaDN x))
-- The α-twisted symmetrized product on DN, instantiating the general
-- formula at alphaDN.

/-- D(a + bε) = bε is an α-derivation for α(ε) = −ε. -/
def dn_alphaDeriv : Bool :=
  -- Specializes Dd at δ = 1 (so D(a+bε) = bε exactly) and checks the
  -- α-derivation identity over all pairs.
  decide (∀ x y : DN, Dd 1 (mulDN x y) = addDN (mulDN (Dd 1 x) (alphaDN y)) (mulDN (alphaDN x) (Dd 1 y)))

/-- D(a + bε) = bε commutes with α. -/
def dn_commAlpha : Bool :=
  decide (∀ x : DN, alphaDN (Dd 1 x) = Dd 1 (alphaDN x))

/-- D(a + bε) = bε is braided-symmetric for σ_α (the inclusion holds here). -/
def dn_braidedSym : Bool :=
  -- Unlike the F2b matrix/dual-number counterexamples above, this instance
  -- checks true: the dual numbers are the "positive baseline" the paper's
  -- Examples section names, where the inclusion the referee reconstructed
  -- genuinely does hold.
  decide (∀ x y : DN, Dd 1 (sympADN x y) = addDN (sympADN (Dd 1 x) y) (sympADN x (Dd 1 y)))

-- Prints all five Booleans in one line: dn_jordan_all, dn2_jordan_all
-- (both expected true, settling the char-2 question), and the α-derivation
-- triple dn_alphaDeriv/dn_commAlpha/dn_braidedSym (all expected true, the
-- one case in the paper where the inclusion holds).
#eval (dn_jordan_all, dn2_jordan_all, dn_alphaDeriv, dn_commAlpha, dn_braidedSym)

-- explicit-proof-exempt: falsification/verification battery over finite types

end BraidedSymDerivCounterexamples
