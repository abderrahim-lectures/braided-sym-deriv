# Statement-fidelity audit, four own results of braided-sym-deriv v79

Agent `audit-1`, worktree `.loom/m-1bad6a/audit-1`, branch `loom/v79/m-1bad6a/audit-1`,
base commit `da26080`. Read: `paper/braided-sym-deriv.tex` (v79) and the Lean modules
`lean/Research/BraidedSymDeriv/{General,TwistedCommutative,Paper,AntiAutomorphism,Closures,Bresar1988,BraidedSymmetric}.lean`
and `lean/Background/JordanHerstein.lean`. The declarations audited are the ones already in the tree at
`da26080`; branch `loom/v79/m-1bad6a/lean-1` stands at the same commit, so it holds no newer Lean text.

Method: the platform skill `lean-statement-audit` (found at `.skill/lean-statement-audit/SKILL.md`).
For each result I quote the paper's hypotheses and conclusion verbatim, quote the Lean binders and type
from the source line, expand every project predicate that hides a premise, and compare carrier, quantifier
order and conclusion strength. Source correspondence and proof status are reported separately.

What I did not do. I wrote no Lean, edited no `.lean` file and no `BINDINGS.tsv`. I did not build and did
not run Lean, because a `lake build` holds the shared cache. The `#check` and `#print axioms` lines quoted
below come from `.scratch/m-1bad6a/lean-1/check_m1.out`, which the Lean agent produced with its own check
file; I did not reproduce them. Every type is quoted from the source text as well, at the line I name, so
the comparison does not rest on that output.

## Summary

| # | paper label | verdict |
|---|---|---|
| 1 | `prop:defect` (Proposition 3.2) | `stronger` |
| 2 | `cor:twisted-semiprime` (Corollary 3.5) | `stronger` |
| 3 | `thm:twisted-commutative` (Theorem 4.1) | `stronger` |
| 4 | `prop:twisted` (Proposition 4.4) | `weaker` |

Counts: `same statement` 0, `stronger` 3, `weaker` 1, `different statement` 0.
No row is claimed to pass any judge, and this report says nothing about the paper.

## Definitions the four rows share

Checked in the source, not inferred from names:

- `BSD.TwistedAlpha α D` (`Paper.lean:122-124`) is
  `∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x))`.
  For an automorphism `α(y*x) = α y * α x`, so this is the paper's Leibniz rule for
  `x ·_{σ_α} y = xy + α(y)α(x)`. The binder is `α : A →+* A`, a ring
  homomorphism. So the predicate itself asks for neither bijectivity nor involutivity. Those enter at the
  theorem statements, as in the paper, whose `BSDer_{σ_α}(A)` is defined for an involutive `α`.
- `BSD.Der D` (`Paper.lean:63`, alias of `BraidedSymmetric.lean:119`) is
  `∀ x y, D (x * y) = D x * y + x * D y`.
- `BSD.JDer D` (`BraidedSymmetric.lean:69-73`) is
  `∀ x y, D (x * y + y * x) = D x * y + x * D y + D y * x + y * D x`. This is the paper's `∘` form,
  `D(x∘y) = D(x)∘y + x∘D(y)`, with the four summands reordered; addition is commutative, so the two agree.
- `BSD.Comm D α` (`Paper.lean:74`) is `∀ x, D (α x) = α (D x)`, the paper's `Dα = αD`.
- `BSDGeneral.Ed` (`General.lean:45`) and `ncDefect` (`TwistedCommutative.lean:231`) are
  `D (a*b) - D a * b - a * D b`, the paper's `E_D`.
- `Background.JordanHerstein.SemiprimeRing` is `∀ a, (∀ r, a*r*a = 0) → a = 0`.
  `TwoTorsionFree` is `∀ a, a + a = 0 → a = 0`. Both match the definitions in the paper's Section 1
  (semiprime: `aRa = 0 ⇒ a = 0`; 2-torsion-free: `2a = 0 ⇒ a = 0`, and `2a` is `a + a`).
- `IsReduced` (Mathlib `Algebra/GroupWithZero/Basic.lean:191`) is `∀ x, IsNilpotent x → x = 0`, which is
  the paper's "its only nilpotent element is zero". `TwistedCommutative.lean:174` uses it as
  `IsReduced.eq_zero _ ⟨2, _⟩`, so the repo's version reads nilpotent as `∃ n, x^n = 0`. Note that the
  Mathlib source I could read at `/opt/mathlib` is v4.33.1, while `lean/lean-toolchain` pins
  `leanprover/lean4:v4.36.0-rc2`; the in-tree use of `IsReduced.eq_zero` is the version that counts.

## Row 1 — `prop:defect` (paper Proposition 3.2)

**1. Paper, verbatim (`paper/braided-sym-deriv.tex:337-347`).**

> \begin{proposition}\label{prop:defect}
> Let $A$ be a unital associative $K$-algebra, let $\alpha$ be an involutive automorphism or anti-automorphism of $A$, and let $D \colon A \to A$ be a linear map with $D\alpha = \alpha D$.
> \begin{enumerate}[label=(\roman*)]
> \item If $\alpha$ is an automorphism, then $D \in \BSDer_{\sigma_\alpha}(A)$ if and only if $E_D(x,y) + \alpha(E_D(y,x)) = 0$ for all $x, y \in A$.
> \item If $\alpha$ is an anti-automorphism, then $D \in \BSDer_{\sigma_\alpha}(A)$ if and only if $E_D(x,y) + \alpha(E_D(x,y)) = 0$ for all $x, y \in A$.
> \end{enumerate}
> In both cases every derivation that commutes with $\alpha$ lies in $\BSDer_{\sigma_\alpha}(A)^\alpha$.
> \end{proposition}

**2. Lean declarations and exact types (quoted from the source).**

`TwistedCommutative.lean:235-238`, with `{R : Type*} [Ring R]` at line 228:

```
theorem prop_defect_aut (α : R ≃+* R) (D : R →+ R) (hDα : ∀ x, D (α x) = α (D x)) :
    (∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x)))
      ↔ ∀ x y, ncDefect D x y + α (ncDefect D y x) = 0
```

`TwistedCommutative.lean:254-259`:

```
theorem prop_defect_anti (α : R →+ R) (hmul : ∀ x y, α (x * y) = α y * α x)
    (D : R →+ R) (hDα : ∀ x, D (α x) = α (D x)) :
    (∀ x y, D (x * y + α (y) * α (x)) = D x * y + α y * α (D x) + (x * D y + α (D y) * α x))
      ↔ ∀ x y, ncDefect D x y + α (ncDefect D x y) = 0
```

Third sentence of the paper. `General.lean:90-93` (automorphism case):

```
theorem derivation_iff_commutes (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hder : ∀ x y : A, D (x * y) = D x * y + x * D y) :
    (∀ x y : A, D (prodA α x y) = prodA α (D x) y + prodA α x (D y))
      ↔ (∀ x : A, D (α x) = α (D x))
```

`AntiAutomorphism.lean:33-36` (anti-automorphism case):

```
theorem der_twisted_iff_comm_anti (α : R ≃+ R)
    (hmul : ∀ x y : R, α (x * y) = α y * α x) (h1 : α 1 = 1) (D : R →+ R)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    TwistedAlphaAnti (⇑α) D ↔ ∀ z, D (α z) = α (D z)
```

The paper's third sentence is the `←` direction of these two. `BSDGeneral.bsd_iff_automorphism`
(`General.lean:68-71`) and `BSDGeneral.bsd_iff_antiautomorphism` state the same two equivalences with
`α : A →+ A`, through `prodA` and `prodB`. `BSDGeneral.residual_automorphism` and
`residual_antiautomorphism` are the two residual identities the paper displays after the proof.

**3. Differences.**

- Carrier. The paper works over a field `K` with a unital associative `K`-algebra and `K`-linear maps.
  `prop_defect_aut` and `prop_defect_anti` ask only for `[Ring R]` and additive maps `R →+ R`, so no
  `K` remains and no linearity beyond additivity is asked. A `K`-algebra is a ring and a `K`-linear map
  is additive, so every instance of the paper's sentence is an instance of these declarations.
- Hypotheses the Lean drops. Involutivity of `α` is dropped in both declarations. Bijectivity is dropped in
  `prop_defect_anti` (`α : R →+ R`, only the anti-multiplicative law) and in the `BSDGeneral` pair.
  Non-commutativity of `R` needs no separate statement: `[Ring R]` does not assume it.
- Hypotheses the Lean keeps. The paper's `Dα = αD` is `hDα` in both declarations. `prop_defect_aut` uses
  `α : R ≃+* R`, so `α` is bijective and unital; unitality costs nothing, because a surjective
  multiplicative map on a unital ring fixes `1`.
- Hypotheses the paper has that the Lean does not: none.
- One rendering detail. The Lean writes the automorphism product as `x*y + α (y*x)` and the paper writes
  `xy + α(y)α(x)`; they agree by multiplicativity of `α`. The Lean writes the anti-automorphism product as
  `x*y + α y * α x`, which is the paper's term.

**4. Conclusion.** `prop_defect_aut` and `prop_defect_anti` state the paper's biconditionals (i) and (ii)
with the same `E_D`, the same `Dα = αD` and the same two equations. `derivation_iff_commutes` and
`der_twisted_iff_comm_anti` are the paper's third sentence together with its converse.

**5. Verdict: `stronger`.** The Lean implies the paper's proposition by instantiating `R` with the
`K`-algebra and the additive maps with the `K`-linear maps; it asks for strictly less (no `K`, no
involutivity, and in the anti-automorphism case no bijectivity). The paper's third sentence is delivered,
but its anti-automorphism half sits in `AntiAutomorphism.der_twisted_iff_comm_anti`, which the
`prop:defect` row of `BINDINGS.tsv` does not name.

## Row 2 — `cor:twisted-semiprime` (paper Corollary 3.5)

**1. Paper, verbatim (`paper/braided-sym-deriv.tex:436-439`).**

> \begin{corollary}\label{cor:twisted-semiprime}
> Let $A$ be a $2$-torsion-free semiprime $K$-algebra with an involutive $K$-algebra automorphism or anti-automorphism $\alpha$.
> Then $\BSDer_{\sigma_\alpha}(A)^\alpha \cap \JDer(A) = \Der(A)^\alpha$, where $\Der(A)^\alpha$ is the set of derivations commuting with $\alpha$ (not to be confused with the space $\ADer(A)$ of $\alpha$-derivations of Section~\ref{sec:sigma-derivations}, which is the notion the literature calls a twisted derivation).
> \end{corollary}

**2. Lean declarations and exact types.**

`Paper.lean:206-209`, with `{A : Type*} [Ring A]` at line 46:

```
theorem corollary_3_5_unconditional (h2 : Background.JordanHerstein.TwoTorsionFree A)
    (hs : Background.JordanHerstein.SemiprimeRing A) (α : A ≃+* A)
    (hαα : ∀ x, α (α x) = x) (D : A →+ A) (hDα : Comm D α) :
    (TwistedAlpha α D ∧ JDer D) ↔ Der D
```

`AntiAutomorphism.lean:70-74`, the anti-automorphism half, with `{R : Type*} [Ring R]` at line 25:

```
theorem corollary_3_5_anti_unconditional (h2 : Background.JordanHerstein.TwoTorsionFree R)
    (hs : Background.JordanHerstein.SemiprimeRing R) (α : R ≃+ R)
    (hmul : ∀ x y : R, α (x * y) = α y * α x) (h1 : α 1 = 1) (D : R →+ R)
    (hDα : ∀ z, D (α z) = α (D z)) :
    (TwistedAlphaAnti (⇑α) D ∧ BSD.JDer D) ↔ BSD.Der D
```

**3. Differences.**

- Carrier. `[Ring A]`, additive `D`; no `K`, no commutativity, no `K`-linearity. The paper's
  `K`-algebra with `K`-linear maps is an instance.
- The paper's set equality, as a sentence about every element. `hDα : Comm D α` is a standing hypothesis,
  and both sides of the paper's equation consist of maps that commute with `α`: `Der(A)^α` by its
  definition, `BSDer_{σ_α}(A)^α` by the superscript. So `(TwistedAlpha ∧ JDer) ↔ Der` under `Comm D α` is
  the pointwise form of `BSDer_{σ_α}(A)^α ∩ JDer(A) = Der(A)^α`, with neither side weakened.
- Hypotheses kept. `h2` is the paper's 2-torsion-freeness, `hs` its semiprimeness, `hαα` the
  involutivity of `α`. In the automorphism half `α : A ≃+* A` supplies bijectivity, multiplicativity and
  unitality.
- Hypotheses added: none. Hypotheses dropped: `K`-linearity, and in the anti-automorphism half
  involutivity of `α` too (only `hmul` and `α 1 = 1` are asked).
- The paper's sentence covers both kinds of `α` in one declaration. The Lean covers them in two, and the
  binding row names only the automorphism one.

**4. Conclusion.** Both directions of the paper's equality, at every `D` commuting with `α`, from
`(TwistedAlpha ∧ JDer)` to `Der` and back. `Bresar1988.bresar1988Theorem1_holds` discharges the cited
Theorem 1, so no hypothesis about Brešar's theorem remains.

**5. Verdict: `stronger`.** The Lean implies the paper's corollary, both halves taken together, on a wider
class of carriers and maps. A reader has to join two declarations to see the paper's "or", and the second
of them is not named in the `cor:twisted-semiprime` row of `BINDINGS.tsv`.

## Row 3 — `thm:twisted-commutative` (paper Theorem 4.1)

**1. Paper, verbatim (`paper/braided-sym-deriv.tex:453-456`).**

> \begin{theorem}\label{thm:twisted-commutative}
> Let $A$ be a commutative reduced $K$-algebra with $2$ invertible in $K$, and let $\alpha$ be an involutive automorphism of $A$.
> Then $\BSDer_{\sigma_\alpha}(A)^\alpha = \Der(A)^\alpha$.
> \end{theorem}

**2. Lean declarations and exact types.**

`Paper.lean:155-158`:

```
theorem theorem_4_1 {A : Type*} [CommRing A] [IsReduced A]
    (α : A ≃+* A) (hαα : ∀ x, α (α x) = x) (D : A →+ A)
    (h2 : IsUnit (2 : A)) (hDα : Comm D α) :
    TwistedAlpha α D ↔ Der D
```

`TwistedCommutative.lean:179-182` is the one-way form the proof uses:

```
theorem twisted_commutative [IsReduced A] (α : A ≃+* A) (hαα : ∀ x, α (α x) = x)
    (D : A →+ A) (h2 : IsUnit (2 : A)) (hDα : ∀ x, D (α x) = α (D x))
    (h : ∀ x y, D (x * y + α (y * x)) = D x * y + α (y * D x) + (x * D y + α (D y * x))) :
    ∀ x y, D (x * y) = D x * y + x * D y
```

`General.lean:168-176`, which the paper states inside its own proof (the last paragraph of the proof of
Theorem 4.1), not as part of the theorem:

```
theorem thm41_core (α : A →+ A) (D : A →+ A)
    (hα : ∀ x y : A, α (x * y) = α x * α y)
    (hDα : ∀ x : A, D (α x) = α (D x))
    (hE : ∀ x y : A, Ed D x y + α (Ed D y x) = 0)
    (hsym : ∀ x y : A, Ed D x y = Ed D y x)
    (hdec : ∀ x : A, ∃ p q : A, α p = p ∧ α q = -q ∧ x = p + q)
    (h2 : ∀ a : A, a + a = 0 → a = 0)
    (hnil : ∀ z : A, α z = -z → z * z = 0 → z = 0) :
    ∀ x y : A, Ed D x y = 0
```

**3. Differences.**

- Carrier. `[CommRing A]` plus `[IsReduced A]`; no `K`, and `D : A →+ A` is additive rather than
  `K`-linear. The paper's commutative reduced `K`-algebra is an instance, so this is a generalisation.
- `2` invertible. The paper says "2 invertible in K"; the Lean says `IsUnit (2 : A)`. For a `K`-algebra,
  2 invertible in `K` gives an inverse of `2 · 1_A` in `A`, so the paper's hypothesis implies the Lean's.
  The Lean's hypothesis is the one the proof uses, and it is weaker.
- Reduced. `[IsReduced A]` is the paper's reducedness by the definition quoted above. Nothing is added.
- Involutivity. `hαα : ∀ x, α (α x) = x` is the paper's "involutive". `α : A ≃+* A` gives the
  automorphism.
- The `^α` on both sides is `hDα : Comm D α` as a standing hypothesis, so the conclusion
  `TwistedAlpha α D ↔ Der D` is the pointwise form of `BSDer_{σ_α}(A)^α = Der(A)^α`.
- Hypotheses added: none. Hypotheses dropped: `K`-linearity, and "2 invertible in K" in favour of
  `IsUnit (2 : A)`.
- `BSDGeneral.thm41_core` carries a different hypothesis set on purpose: any ring, `hE` in place of the
  twisted rule, `hsym` in place of commutativity, `hdec` in place of the averaging by `1/2`, 2-torsion
  freeness of `A` in place of `IsUnit 2`, and `hnil` in place of reducedness. This is the paper's own
  stated sharpening inside the proof. It is not the theorem's sentence, and I record it as support, not
  as the binding.

**4. Conclusion.** `BSD.theorem_4_1` gives both directions of the paper's equality on the commuting class.
The direction `Der → TwistedAlpha` is proved from `der_twisted_iff_comm`, which needs no reducedness and
no `2`, as in the paper.

**5. Verdict: `stronger`.** It implies the paper's theorem: an instance at a commutative reduced
`K`-algebra with 2 invertible in `K`, an involutive automorphism and a `K`-linear `D`. It asks for less in
two places, the absence of `K` and `IsUnit (2 : A)` for "2 invertible in K".

## Row 4 — `prop:twisted` (paper Proposition 4.4)

**1. Paper, verbatim (`paper/braided-sym-deriv.tex:531-539`).**

> \begin{proposition}\label{prop:twisted}
> Let $A = \mathbb{F}_3[\varepsilon]/(\varepsilon^3)$, and let $\alpha$ be the automorphism with $\alpha(\varepsilon) = -\varepsilon$.
> Then
> \[
> \ADer(A) \not\subseteq \BSDer_{\sigma_\alpha}(A)^\alpha
> \qquad\text{and}\qquad
> \BSDer_{\sigma_\alpha}(A)^\alpha \not\subseteq \ADer(A).
> \]
> \end{proposition}

**2. Lean declarations and exact types.**

`TwistedCommutative.lean:279-314`, namespace `TW`, with `K := ZMod 3`, `V := Fin 3 → K`,
`mul a b k = ∑ i, ∑ j, if i.val + j.val = k.val then a i * b j else 0`,
`alpha a k = if k.val = 1 then -a k else a k`, `D1 a k = if k.val = 0 then 0 else a k`,
`dd a k = (k.val : K) * a k`, `e i k = if k = i then 1 else 0`,
`tmul a b = mul a b + mul (alpha b) (alpha a)`:

```
TW.D1_comm_alpha : ∀ i : Fin 3, D1 (alpha (e i)) = alpha (D1 (e i))
TW.D1_alphader : ∀ i j : Fin 3,
    D1 (mul (e i) (e j)) = mul (D1 (e i)) (alpha (e j)) + mul (alpha (e i)) (D1 (e j))
TW.D1_not_twisted :
    D1 (tmul (e 1) (e 1)) ≠ tmul (D1 (e 1)) (e 1) + tmul (e 1) (D1 (e 1))
TW.dd_comm_alpha : ∀ i : Fin 3, dd (alpha (e i)) = alpha (dd (e i))
TW.dd_der : ∀ i j : Fin 3,
    dd (mul (e i) (e j)) = mul (dd (e i)) (e j) + mul (e i) (dd (e j))
TW.dd_not_alphader :
    dd (mul (e 1) (e 1)) ≠ mul (dd (e 1)) (alpha (e 1)) + mul (alpha (e 1)) (dd (e 1))
```

`Closures.lean:153-166` lifts the four basis statements to all elements of `V`:

```
Closures.TW_D1_comm_alpha_all : ∀ a : TW.V, TW.D1 (TW.alpha a) = TW.alpha (TW.D1 a)
Closures.TW_D1_alphader_all : ∀ a b : TW.V,
    TW.D1 (TW.mul a b) = TW.mul (TW.D1 a) (TW.alpha b) + TW.mul (TW.alpha a) (TW.D1 b)
Closures.TW_dd_comm_alpha_all : ∀ a : TW.V, TW.dd (TW.alpha a) = TW.alpha (TW.dd a)
Closures.TW_dd_der_all : ∀ a b : TW.V,
    TW.dd (TW.mul a b) = TW.mul (TW.dd a) b + TW.mul a (TW.dd b)
```

**3. Differences.**

- Carrier. The paper's `A` is the `K`-algebra `F_3[ε]/(ε^3)`, and `ADer(A)` and
  `BSDer_{σ_α}(A)^α` are sets of `K`-linear maps. The Lean's `TW.V` is the function type `Fin 3 → ZMod 3`
  with a multiplication `TW.mul` given by an explicit formula. There is no `Ring` or `Algebra` instance for
  `(TW.V, TW.mul)` anywhere in the development. There is no proof that `TW.mul` is associative, and none
  that `e 0` is a unit. Nothing shows that `TW.alpha` is multiplicative, or that `TW.D1` and `TW.dd` are
  additive. The `Ring` instance that `Fin 3 → ZMod 3` does have is the pointwise one, which is not
  `TW.mul`. So the Lean checks four identity conditions on coordinate functions. It does not state that
  any of these functions lies in a set of `K`-linear maps.
- Quantifiers. `TW.D1_alphader` and `TW.dd_der` range over pairs of basis vectors, and the file's own
  header says the passage to all pairs is left to a comment. `Closures.TW_D1_alphader_all` and
  `Closures.TW_dd_der_all` close that at all pairs, by `decide`. The two `not_` statements are single
  witnesses at `(ε, ε)`, as in the paper.
- The first non-inclusion. `Closures.TW_D1_alphader_all` gives that `D1` satisfies the `α`-derivation
  rule, and `TW.D1_not_twisted` gives that `D1` fails the `σ_α` rule at `(ε, ε)`. Additivity of `D1` is not
  stated, so "`D1 ∈ ADer(A)`" as a statement about a `K`-linear map is not in the Lean.
- The second non-inclusion. `TW.dd_der_all` and `TW.dd_comm_alpha_all` give that `dd` is a derivation and
  that `dd` commutes with `α`. Nothing states that `dd` satisfies the `σ_α`-Leibniz rule, that is,
  `∀ a b, dd (tmul a b) = tmul (dd a) b + tmul a (dd b)`. The paper reaches that from `E_d = 0` and
  Proposition 3.2. The Lean route would be `der_twisted_iff_comm`, which needs `[Ring R]`, `α : R ≃+* R`
  and additive maps, so it does not apply to `TW.mul`. Direct expansion from `TW.dd_der_all` and
  `TW.dd_comm_alpha_all` needs `dd (u + v) = dd u + dd v` at `u = mul a b` and `v = mul (α b) (α a)`,
  which nothing supplies. So the membership `dd ∈ BSDer_{σ_α}` is missing.
- Neither non-inclusion is stated as a single sentence in the paper's form `S ⊄ T`.

**4. Conclusion.** What is present supports the paper's conclusion and does not state it. The first
non-inclusion is supported by `TW_D1_alphader_all` against `TW.D1_not_twisted`, short of linearity of
`D1`. The second is supported only on the `ADer` side, by `TW.dd_der_all` and `TW.dd_comm_alpha_all`
against `TW.dd_not_alphader`; its twisted-side membership is absent.

**5. Verdict: `weaker`.** The exact missing strength: (a) the statement that `dd` satisfies the
`σ_α`-Leibniz rule, so that `dd` lies in `BSDer_{σ_α}`; (b) the two non-inclusions as sentences; (c) the
algebra structure on `TW.V` (associativity, unit, and additivity of `D1`, `dd`, `alpha`), without which
`ADer` and `BSDer` are not the paper's sets of `K`-linear maps. This row is not a formalization of the
paper's sentence as it stands.

## Against `BINDINGS.tsv`

`git show loom/v79/m-1bad6a/lean-1:loom/m-1bad6a/BINDINGS.tsv` (branch at `da26080`) gives status
`proved` for all four rows. My verdicts agree for rows 1 to 3 only in this sense: a statement that is
stronger than the paper's is not a weakening, and the differences there are generalisations. For row 4 my
verdict is `weaker`, so the status `proved` for `prop:twisted` does not match. That row's note says "both
non-inclusions follow from these facts with no gap"; the second one does not follow from the declarations
in the tree, for the reason given in Row 4 above. I did not edit `BINDINGS.tsv`.

## Names in `lean/RESULTS.md`

`RESULTS.md` writes `TwistedCommutative.prop_defect_aut` and `TwistedCommutative.TW.D1_alphader`.
`TwistedCommutative.lean` declares no namespace `TwistedCommutative`; its only namespaces are `UV` and
`TW`, at lines 40 and 279. So the declarations are `prop_defect_aut`, `prop_defect_anti`,
`twisted_commutative` and `leibnizDefect` at the root, and `TW.D1_alphader` at top level. The `#check` output
in `.scratch/m-1bad6a/lean-1/check_m1.out` prints them without a `TwistedCommutative` prefix, which agrees.
`BINDINGS.tsv` uses the correct names. I did not edit `RESULTS.md`; it is outside my edit list.

## What I could not check

I did not run Lean, so I did not reproduce the `#print axioms` lines; the recorded footprints rest on
`propext`, `Classical.choice` and `Quot.sound` with no `sorryAx` for all twenty declarations I name. I read
Mathlib's `IsReduced` at `/opt/mathlib` (v4.33.1) while the project pins v4.36.0-rc2, so that definition is
the one point where the reading is against a possibly different version; the in-tree use of
`IsReduced.eq_zero` supports it.
