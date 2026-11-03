# Findings — independent re-derivation of every numbered result and displayed computation

Referee: m-1bad6a (proofs-1). Object: `paper/braided-sym-deriv.tex`, v79, 686 lines.
Method: every item below was recomputed from the definitions, by hand and (where the
claim is an identity on an algebra or a dimension) with exact linear algebra.

* Hand computation: expansions of the Leibniz defect, the Hochschild
  cocycle identity, the residual identity in both cases, the proof of Theorem 4.1,
  the parity/splitting arguments, the three-forms equivalence.
* My own exact-arithmetic scripts (independent of `tools/` and of the paper's
  harness): `.ultramath/smw0y94qp/m1/check{1,2,3,4,5,6,7,8,9,10}.py` and `alg.py`,
  over `Q` (Fraction) and `F_p`, solving the linear systems for
  `Der`, `ADer`, `BSDer` and testing membership pair by pair.
* Cross-check of every dimension the paper prints against
  `.skill/bsd-exact-algebra/cases.py` (which I ran: "all cases reproduce", exit 0).
  In every case below my own code and that solver agree.

Counts: **18 VERIFIED, 0 GAP, 0 WRONG.** No mathematical change is required.
Two wording items are listed at the end; neither is an error of substance.

Line numbers are those of `paper/braided-sym-deriv.tex` (v79).

---

## 1. §1, line 168; lines 172–178 (Jordan conditions) — VERIFIED

Line 168: from `D(1) = D(1·1) = D(1)·1 + 1·D(1) = 2D(1)` one gets `0 = D(1)` by
*cancellation in the additive group*, not by division by 2: `a = 2a ⇒ a = 0`
holds in every characteristic. So the sentence is uniform in `char K`, and the
later use in char 2 (line 236: a derivation satisfies `D(1) = 2D(1) = 0`) is sound.

Lines 175–177 (linearization). Write the `x²`-form `D(x²) = D(x)x + xD(x)`.
Substituting `x + y` and subtracting the `x²`- and `y²`-instances:
`D(xy) + D(yx) = D(x)y + D(y)x + xD(y) + yD(x) = D(x)∘y + x∘D(y)`.
So the `x²`-form implies the `∘`-form in every characteristic — as printed.
Conversely, `y = x` in the `∘`-form gives `D(2x²) = 2D(x²) = 2(D(x)x + xD(x))`
(line 176, exactly). Cancelling the factor 2 needs either `2 ∈ K^×` or `2`-torsion-
freeness of the additive group of `A` (line 177). Both are correct as stated; note
that in char 2 neither holds in general and the two forms really differ:
`A = F_2[x]/(x³)` has `9 = dim End` maps satisfying the `∘`-form (`x∘y = 2xy = 0`)
but only `64` of the `512` maps satisfy the `x²`-form (`D(x²) = 2xD(x) = 0`).
Computed by exhaustive enumeration.

Line 178: if `char K = 2` and `A` commutative then `x∘y = xy + yx = 2xy = 0`, so the
`∘`-condition reads `0 = 0`. Verified (`F_2×F_2`, `F_2[x]/(x³)`:
`dim JDer = 4 = dim End`, `9 = dim End`).

## 2. §2, Example `ex:not-associative` (lines 212–223) — VERIFIED

`A = K×K`, `α(a,b) = (b,a)`. For `x = (x_1,x_2)`, `y = (y_1,y_2)`:
`xy = (x_1y_1, x_2y_2)` and `α(xy) = (x_2y_2, x_1y_1)`, so
`x·y = (x_1y_1 + x_2y_2)(1,1)` — the displayed formula, checked. `α² = id`, hence
`σ_α² = id` (also checked directly on the four basis elements of `A⊗A`).
With `p = (1,0)`, `q = (0,1)`: `p·p = (1,1)`, `(p·p)·q = (1·0 + 1·1)(1,1) = (1,1)`,
`p·q = (0)(1,1) = 0`, `p·(p·q) = 0`. So `(p·p)·q ≠ p·(p·q)`: not associative.
For `u = (u_1,u_2)`: `u·p = (u_1·1 + u_2·0)(1,1) = u_1(1,1)`, while `p = (1,0)`;
equality would give `u_1 = 1` and `u_1 = 0`. So no unit. Both claims verified.

## 3. §2, Remark `rem:sigma-derivation-classification` (lines 225–258) — VERIFIED

* `σ = id`: `x·y = 2xy`, the identity is `2D(xy) = 2(D(x)y + xD(y))`; `2 ∈ K^×`
  gives `BSDer_id = Der` (line 234). In char 2, `x·y = 0` and every linear map
  qualifies (line 235). The witness `D(1) = 1`, `D = 0` on a complement: it is not
  a derivation because `D(1) = 1 ≠ 0`; checked explicitly on `A = K` and on
  `F_2[x]/(x³)`. Note the construction is also correct for `dim A = 1`, where the
  complement is `0` and the map is `id`, with `id(1) = 1 ≠ 0`.
* `σ = τ`: `x·_τ y = xy + yx = x∘y`, so `BSDer_τ = JDer` in every characteristic
  (line 238) — this is the definition of `JDer` at line 174.
* `Der ⊆ JDer`: `D(xy) + D(yx) = D(x)y + xD(y) + D(y)x + yD(x)`, verified; hence
  `Der ⊆ JDer` in every characteristic, and in char ≠ 2 `BSDer_id ⊆ BSDer_τ`.
* `σ = -id`: `x·y = xy - xy = 0`; every linear map is a derivation of the zero
  product, so `BSDer_{-id} = End_K(A)`.
* `σ = -τ`: `x·y = xy - yx = [x,y]`, and the identity is exactly
  `D([x,y]) = [D(x),y] + [x,D(y)]`, i.e. the Lie derivations.
* Char 2: `-id = id`, `-τ = τ`; `dim_K A ≤ 1`: `A⊗A` is spanned by `1⊗1` (resp. is
  `0`), so `τ = id` there.
Every product formula above was recomputed from `μ_σ = μ + μ∘σ`.

## 4. §2, Remark `rem:natural-involutions` (lines 261–266) — VERIFIED

(a) Determination on `K²` (line 262): for `v,w ∈ V` pick `j: K² → V` with
`j(e_1) = v`, `j(e_2) = w`; then `v⊗w = (j⊗j)(e_1⊗e_2)`. So `V⊗V` is spanned by
the images of `j⊗j`, and naturality `η_V∘(j⊗j) = (j⊗j)∘η_{K²}` determines `η_V`.
For `dim V ≤ 1`, `V⊗V` is spanned by `v⊗v` and `id = τ`. Correct.

(b) `β⊗β = id ⇒ β = λ id`, `λ² = 1` (line 285). Fix `y` with `β(y) ≠ 0` and a
functional `φ` with `φ(β(y)) = 1`. Applying `id⊗φ` to `β(x)⊗β(y) = x⊗y`:
`β(x) = φ(y)·x`. So `β(x) ∈ Kx` with the scalar `φ(y)` independent of `x`; then
`λ² = 1` from `β⊗β = id` (on a nonzero vector). The parenthetical argument is
complete as stated. For `α` an algebra map, `α²(1) = 1` gives `λ = 1` (line 285).

(c) The 2×2 computation (line 262). Let `M ∈ End(K²⊗K²)` in the basis
`e_1e_1, e_1e_2, e_2e_1, e_2e_2`, and require `M(f⊗f) = (f⊗f)M` as a polynomial
identity in the four entries `a,b,c,d` of `f`. SymPy gives the general solution
`M = x·I + y·(τ - I)`, i.e. `M = (x-y)I + y τ`, a **2-dimensional** space spanned by
`id` and `τ`. Confirmed. (So "those are the linear combinations of id and τ" is right.)

(d) `σ = λ id + μ τ`: `σ² = (λ²+μ²) id + 2λμ τ`. Hence `σ² = id ⇔ λ²+μ² = 1` and
`2λμ = 0`. In char ≠ 2: `λμ = 0`, so `(λ,μ) = (±1,0)` or `(0,±1)` — the four
entries. Correct (line 262).

(e) Char 2 (line 264): the condition is `λ² + μ² = 1` with no constraint on `λμ`;
since `λ²+μ² = (λ+μ)²`, we get `(λ+μ+1)² = 0`, hence `μ = 1 + λ`. So the involutions
among the natural endomorphisms are exactly `λ id + (1+λ)τ`, and `λ = 1` gives `0`.
The product: `x·_σ y = xy + λxy + (1+λ)yx = (1+λ)(xy+yx) = (1+λ)(x∘y)` — the
displayed scalar multiple, checked. Derivations of a nonzero scalar multiple of a
product are the derivations of the product, so for `1+λ ≠ 0` the class is `JDer`,
and for `λ = 1` it is `End_K(A)`; these are the `τ`- and `id`-classes, so the family
"adds no class", as printed.

(f) Lines 265: `A = F_5[ε]/(ε²)`, `T(1) = 1`, `T(ε) = 1+ε`, matrix
`T = [[1,1],[0,1]]`, `T^{-1} = [[1,-1],[0,1]]` (`T^{-1}(ε) = -1+ε`). For
`σ = (T⊗T^{-1})∘τ`, i.e. `σ(x⊗y) = T(y)⊗T^{-1}(x)`, the product
`x·_σ y = xy + T(y)T^{-1}(x)` has, on the basis,
`1·1 = 2`, `1·ε = 1+2ε`, `ε·1 = -1+2ε`, `ε·ε = -1`
(over `F_5`: `2, 1+2ε, 4+2ε, 4`). Solving the 4-dimensional linear system gives
**`dim BSDer_σ(A) = 0`**, i.e. `BSDer_σ(A) = {0}`, as printed. `σ` is an involution:
`σ²(x⊗y) = x⊗y`. Since `σ(1⊗ε) = (1+ε)⊗1` is not a multiple of `1⊗ε` or `ε⊗1`,
`σ` is none of `id, τ, -id, -τ`.

## 5. §3, lines 284–308 — VERIFIED

`σ_α(σ_α(x⊗y)) = σ_α(α(y)⊗α(x)) = α²(x)⊗α²(y)`, so `σ_α² = α²⊗α²` and
`σ_α² = id` iff `α² ⊗ α² = id` iff `α² = λ id`, `λ² = 1` (item 4(b)), iff `λ = 1`
because `α²(1) = 1`. Hence `σ_α` is an involution exactly when `α² = id`. Correct.
The splitting `A = A_+ ⊕ A_-` at line 286–290 with the displayed half-sum is the
standard one and needs `2 ∈ K^×` only for spanning; membership in `A_±` does not.
`(α⊗α)∘τ(x⊗y) = α(y)⊗α(x) = σ_α(x⊗y)` — the composite claim (lines 294–300).
The product `x·_{σ_α}y = xy + α(y)α(x)` (line 304) is `μ + μ∘σ_α` by definition.
`α = id` gives `xy + yx` (Jordan); `α` an automorphism gives
`α(y)α(x) = α(yx)`; `α` an anti-automorphism gives `α(y)α(x) = α(xy)`. Correct.

## 6. §3, lines 320–331 (`E_D = -δD`, cocycle identity) — VERIFIED

With `(δD)(x,y) = xD(y) - D(xy) + D(x)y` (line 325), one has
`-δD(x,y) = D(xy) - D(x)y - xD(y) = E_D(x,y)`. Correct.
Cocycle identity (line 330): expand the four terms with
`E(b,c) = D(bc) - D(b)c - bD(c)`:
`aD(bc) - aD(b)c - abD(c) - D(abc) + D(ab)c + abD(c) + D(abc) - D(a)bc - aD(bc) - D(ab)c + D(a)bc + aD(b)c = 0`,
all six pairs cancelling. So `aE(b,c) - E(ab,c) + E(a,bc) - E(a,b)c = 0` as printed
(this is `δE = 0` for the Hochschild coboundary `(δf)(a,b,c) = af(b,c) - f(ab,c) + f(a,bc) - f(a,b)c`,
which is the standard formula and is `-δ` of `E = -δD` consistently). Also checked
computationally for random `D` on `M_2(F_5)` (64 triples) and `M_3(F_3)`.

## 7. §3, Proposition `prop:defect` and the residual identities (lines 337–387) — VERIFIED

With `x·y := x·_{σ_α}y` and `Φ(x,y) := D(x·y) - D(x)·y - x·D(y)`:

Case (i), `α` an automorphism, `x·y = xy + α(yx)`:
`Φ = D(xy) + D(α(yx)) - D(x)y - α(yD(x)) - xD(y) - α(D(y)x)`
`  = E(x,y) + [D(α(yx)) - α(yD(x) + D(y)x)]`.
Now `yD(x) + D(y)x = D(yx) - E(y,x)`, so
`Φ = E(x,y) + α(E(y,x)) + (Dα - αD)(yx)`. **The printed residual identity is exact.**

Case (ii), `α` an anti-automorphism, `x·y = xy + α(xy)`:
`Φ = E(x,y) + [D(α(xy)) - α(yD(x)) - α(D(y)x)]`, and using
`α(yD(x)) = α(D(x))α(y)`, `α(D(y)x) = α(x)α(D(y))` this is
`E(x,y) + D(α(xy)) - α(D(x))α(y) - α(x)α(D(y)) = E(x,y) + α(E(x,y)) + (Dα - αD)(xy)`.
**The printed case-(ii) form with `α(E(x,y))` and `(Dα-αD)(xy)` is exact.**

With `Dα = αD` the last term drops and the surviving condition is exactly
`E(x,y) + α(E(y,x)) = 0` (resp. `E(x,y) + α(E(x,y)) = 0`), which is the proposition.
Conversely `E = 0 ⇒` both conditions, so every derivation commuting with `α` lies in
the class (line 343). Verified numerically for `M_2(F_5)` (all `D` in the commutant of
`α`, 15 random samples per case, 0 mismatches) and pair-by-pair for the residual
identities in six settings: `M_2(F_5)` with `α = Ad_S` (`S` unipotent, **not**
involutive), with `α = Ad_T` (`T² = 1`), with `α` = transpose, with `α = id`;
`M_3(F_3)` with `α = Ad_S`, `S` of order 3 (**not** involutive); and the **non-unital**
algebra `F_5[u]/(u³)` with `α(u) = 2u` (**not** involutive). All pairs: 0 failures in
both cases. This confirms line 387 ("the computation uses neither the unitality of `A`
nor the involutivity of `α`").

Follow-up sentence (lines 383–385, the one repaired in v78). It is **true in both
directions**: if `E + αE∘τ` vanishes identically, then by the displayed identity
`Φ(x,y) = (Dα - αD)(yx)`; so `D ∈ BSDer_{σ_α}` iff `(Dα-αD)(yx) = 0` for all `x,y`,
iff `Dα = αD` when `A` is unital (the products `yx` span `A`: `y = 1`). For the
anti-automorphism case the same with `xy`. I checked the scope of the conditional:
the "exactly when `Dα = αD`" is asserted *under* "if they vanish", and it is false
without that hypothesis (a derivation with `Dα ≠ αD` is in no class yet has `Dα ≠ αD`),
so the conditional reading is the correct one and the sentence is sound as printed.

## 8. §3, lines 391–402 (`E_s ∈ A_-`, `E_a ∈ A_+`, and `α = id`) — VERIFIED

Case (i) condition: `E(x,y) + α(E(y,x)) = 0` for all `x,y`. Put
`E_s = ½(E(x,y)+E(y,x))`, `E_a = ½(E(x,y)-E(y,x))`. Then `E(y,x) = E_s - E_a`
(pointwise), so the condition is `(E_s + αE_s)(x,y) + (E_a - αE_a)(x,y) = 0`.
Swapping `x,y` gives `(E_s + αE_s)(x,y) - (E_a - αE_a)(x,y) = 0`. Sum and difference
(with `2 ∈ K^×`): `α(E_s) = -E_s` and `α(E_a) = E_a`, i.e. `E_s` takes values in
`A_-` and `E_a` in `A_+`. Conversely such `E_s, E_a` satisfy the condition. So the
"exactly when" is correct. At `α = id`: `A_- = 0`, so the condition is `E_s = 0`,
i.e. `E(x,y) + E(y,x) = 0`, which is precisely the Jordan condition
`D(x∘y) = D(x)∘y + x∘D(y)` (verified by expansion). Confirmed numerically
(`M_2(F_5)`, `α = Ad_T`, 15 random `D`: 0 mismatches between the two conditions;
`α = id`: Jordan condition ⇔ `E_s = 0`, 0 mismatches). Case (ii) at line 391–392:
`α(E_D) = -E_D` ⇔ `E_D` takes values in `A_-`; no hypothesis on 2 needed.

## 9. §3, Remark `rem:inner-twisted` (lines 404–424) — VERIFIED

For `D ∈ Der(A)` the difference of the two sides of the `σ_α`-identity is
`(Dα - αD)(yx)` (case (i)) resp. `(Dα-αD)(xy)` (case (ii)) — the residual identity of
item 7 with `E = 0`, exactly as line 409 prints. Since `A` is unital, `D ∈ BSDer`
iff `Dα = αD` (line 413).
Inner derivations, automorphism case:
`ad_g(α(x)) = gα(x) - α(x)g` and `α(ad_g(x)) = α(g)α(x) - α(x)α(g)`, so
`ad_g α = α ad_g ⇔ [g - α(g), α(x)] = 0` for all `x`, and as `α` is onto, iff
`g - α(g) ∈ Z(A)`. Anti-automorphism case:
`α(ad_g(x)) = α(gx - xg) = α(x)α(g) - α(g)α(x)`, so the condition is
`(g + α(g))α(x) = α(x)(g + α(g))` for all `x`, i.e. `[g + α(g), α(x)] = 0`, iff
`g + α(g) ∈ Z(A)`. Both as printed. Checked exhaustively for all 625 `g ∈ M_2(F_5)`
with `α = Ad_T` (automorphism) and `α` = transpose (anti-automorphism): the bracket
condition, the vanishing of `ad_g`-commutation and the centrality condition agree in
all 625 cases; and `Inn_α(A) = Inn(A) ∩ BSDer_{σ_α}(A)^α` holds in all 625 cases
(the set `{ad_g : g - α(g) ∈ Z(A)}` is a subspace because `g ↦ ad_g` is linear).

## 10. §3, Corollary `cor:twisted-semiprime` (lines 436–451) — VERIFIED

`⊇`: `D ∈ Der(A)^α` ⇒ `D` is a Jordan derivation (`Der ⊆ JDer`, item 3) and
`D ∈ BSDer_{σ_α}(A)^α` (item 7, last line of the proposition). Both inclusions are
stated and used correctly.
`⊆`: `D` in the intersection is a Jordan derivation of a `2`-torsion-free semiprime
ring, hence a derivation (Theorem `thm:bresar`), and commutes with `α` by hypothesis.
The `∘`-form / `x²`-form compatibility invoked at line 449 is exactly item 1 (`2`-
torsion-freeness is assumed). No gap. Consistency check: `M_2(K)`, `α` = transpose,
`K = Q, F_3, F_7`: `dim Der^α = dim BSDer^α = dim(BSDer^α ∩ JDer) = 1` in each case.

## 11. §4, Theorem `thm:twisted-commutative` (lines 453–492) — VERIFIED

Every step re-derived:
1. `⊇` by item 7. 2. `A` commutative ⇒ `E_D` symmetric (each of the three terms is
symmetric in `x,y`). With `D ∈ BSDer^α`, Proposition (i) gives
`E(x,y) + α(E(y,x)) = E(x,y) + α(E(x,y)) = 0`, so `E` takes values in `A_-`.
3. `Dα = αD` ⇒ `D(A_±) ⊆ A_±`; `α` multiplicative ⇒ `A_iA_j ⊆ A_{i+j}` (signs
multiply), for `i,j ∈ {+,-}`.
4. Same part (`x,y ∈ A_+` or both in `A_-`): `xy ∈ A_+`, `D(x)y ∈ A_+` and
`xD(y) ∈ A_+`, so `E(x,y) ∈ A_+`, while `E` has values in `A_-`; `A_+ ∩ A_- = 0`
because `2 ∈ K^×`. So `E` vanishes on both `A_+×A_+` and `A_-×A_-`.
5. Mixed pair: `x ∈ A_+`, `y ∈ A_-`, `z := E(x,y) ∈ A_-`; then
`xy, zx, xz ∈ A_-` and `zy ∈ A_+` (parity). Cocycle at `(z,x,y)`:
`z·E(x,y) - E(zx,y) + E(z,xy) - E(z,x)y = 0`; the pairs `(zx,y)` and `(z,xy)` have
both entries in `A_-`, so those terms vanish and `z² = E(z,x)y`. Cocycle at `(x,z,y)`:
`xE(z,y) - E(xz,y) + E(x,zy) - E(x,z)y = 0`; the pairs `(z,y)`, `(xz,y)` lie in
`A_-×A_-` and `(x,zy) ∈ A_+×A_+`, so all three vanish and `E(x,z)y = 0`. With `E`
symmetric, `z² = E(x,z)y = 0`. Reduced ⇒ `z = 0`.
6. `E` bilinear and symmetric, vanishing on `A_+×A_+`, `A_-×A_-` and `A_+×A_-`
(hence on `A_-×A_+`) and `A = A_+ ⊕ A_-` ⇒ `E = 0` ⇒ `D` is a derivation.
All steps check out; the two cocycle substitutions are at the printed arguments, the
parity claims `A_iA_j ⊆ A_{i+j}` and `E(A_i×A_j) ⊆ A_{i+j}` are correct (the latter
needs `Dα = αD` and `α` multiplicative), and "three parts" suffices because of symmetry.

The two stronger statements (lines 488–492) are indeed what the argument proves:
* "reduced" is used exactly once, to pass from `z ∈ A_-`, `z² = 0` to `z = 0`;
  replacing it by "no nonzero `z ∈ A_-` with `z² = 0`" is legitimate, and the
  condition is vacuous for `α = id` (`A_- = 0`; then the theorem degenerates to
  "commutative + `2 ∈ K^×` ⇒ every Jordan derivation is a derivation", which is true
  by a one-line computation `2D(xy) = D(x∘y) = 2(D(x)y + xD(y))`).
* the second statement is also exactly what the argument gives: after the hypothesis
  "`E_D` symmetric", no step uses commutativity (`A_iA_j ⊆ A_{i+j}` and `D(A_±) ⊆ A_±`
  come from multiplicativity and `Dα = αD` alone). Note only that unitality is *not*
  used anywhere in this argument, so the hypothesis "unital" in the second statement
  is redundant, not wrong.

## 12. §4, non-vacuity paragraph (line 494) — VERIFIED (with a wording note)

`A = K[t]`, `α(t) = -t`. Derivations of `K[t]` are the `f d/dt`. For `D = f d/dt`,
`D(t^n) = n f t^{n-1}`, so
`α(D(t^n)) = n(-1)^{n-1} f(-t) t^{n-1}` and `D(α(t^n)) = n(-1)^n f(t) t^{n-1}`;
the two agree for all `n` iff `f(-t) = -f(t)` (SymPy: the differences are
`±2n t^{n-1}(c_0 + c_2t² + c_4t⁴ + …)`, vanishing identically iff all even
coefficients vanish). Hence `Der(A)^α = {f d/dt : f(-t) = -f(t)}`, and `t d/dt`
(`f = t`, `f(-t) = -t = -f(t)`, `D(t) = t ≠ 0`) lies in it. Correct.
Perfect-field sentence: a finite-dimensional reduced commutative `K`-algebra is a
product of finite field extensions (reduced artinian ⇒ semisimple ⇒ product of
fields), separable when `K` is perfect, and a finite separable extension has no
nonzero `K`-derivation; derivations of a product are the product of the derivations.
So `Der(A) = 0` and the asserted equality is trivially true in finite dimension.
The logic is right; the wording is discussed under "Wording (optional)" below.

## 13. §4, Examples `ex:twisted-nilpotent` (498–514) and `ex:twisted-char-two` (516–529) — VERIFIED

`A = F_5[u,v]/(u²,v²)`, basis `1,u,v,uv`, `α(u) = u`, `α(v) = -v` (involutive
automorphism, checked on all 16 basis pairs), `D(uv) = uv`, `D` zero on `1,u,v`.
`Dα = αD` holds. The `σ_α`-Leibniz rule holds on all 16 basis pairs (checked by
computer, both sides, all components). `D` is not a derivation: `D(uv) = uv` but
`D(u)v + u D(v) = 0`. `E_D(u,v) = uv`, and `(uv)² = u²v² = 0`, so `z = uv ∈ A_-`
(nonzero, `α(uv) = -uv`) with `z² = 0` — exactly the obstruction isolated in item 11.
(For the record: `dim BSDer^α = 5`, `dim Der^α = 3`, not printed in the paper.)
`A = F_2×F_2`, `α` the swap, `p = (1,0)`, `q = (0,1)`, `e = (1,1)`, `D(p) = D(q) = e`
hence `D(e) = 2e = 0`. Products: `p·p = q·q = e`, `p·q = 0`. Pairs `(p,p)`, `(q,q)`,
`(p,q)`: both sides are `0` (left side `D(e) = 0`, right side `D(p)·p + p·D(p) = e·e + e·e = 2e = 0`
and `D(p)·q + p·D(q) = e·q + p·e = e + e = 0`). Pair with `e`: `x·e = x + α(x) ∈ {0,e}`;
left side `D(e) = 0`, right side `D(x)·e`, and `D(x) ∈ {0,e}`, `e·e = 2e = 0`. So
`D ∈ BSDer_{σ_α}(A)^α` (verified by computer on all 4 basis pairs), and `D` is not a
derivation because `D(p) = e ≠ 0 = 2pD(p)`. Every stated number is right
(`dim BSDer^α = 1`, `dim Der^α = 0`).

## 14. §4, Proposition `prop:twisted` (lines 531–575) — VERIFIED

`A = F_3[ε]/(ε³)`, `α(ε) = -ε` (involutive automorphism; `A_+ = F_3·1 + F_3ε²`,
`A_- = F_3ε`).
First map `D(a + bε + cε²) = bε + cε²`: `Dα = αD` (diagonal on the basis); it is an
`α`-derivation on all 9 basis pairs (`(ε,ε)`: `D(ε²) = ε²` and
`D(ε)α(ε) + α(ε)D(ε) = -2ε² = ε²`; other pairs as printed). But
`E_D(ε,ε) = ε² - 2ε² = 2ε² = -ε²  ≠ 0` lies in `A_+`, so `D ∉ BSDer_{σ_α}^α`.
Second map `d(a+bε+cε²) = bε + 2cε²`: `d(ε^i) = i ε^i`, a derivation (checked on all
9 pairs), so `E_d = 0` and `d ∈ BSDer_{σ_α}^α`; and
`d(ε²) - d(ε)α(ε) - α(ε)d(ε) = 2ε² + ε² + ε² = 4ε² = ε² ≠ 0` in `F_3`, so
`d ∉ ADer(A)`. Both non-memberships confirmed by solving both systems:
`dim ADer = 3`, `dim BSDer_{σ_α}^α = 1`, `dim Der^α = 1`, and `D, d` are as claimed.

## 15. §4, Example `ex:twisted-meet` (lines 579–588) — VERIFIED

(a) `A = M_2(F_3)`, `α` = transpose (involutive anti-automorphism),
`g = [[0,1],[-1,0]] = [[0,1],[2,0]]`: `α(g) = -g ≠ g`, so `g ≠ 0` and `g + α(g) = 0`,
hence `ad_g` commutes with `α` (item 9) and lies in `BSDer_{σ_α}(A)^α` since
`E_{ad_g} = 0` (item 7). `ad_g ≠ 0`: `ad_g(E_{11}) = gE_{11} - E_{11}g = [[0,1],[1,0]] ≠ 0`
(computed). `ADer` needs an automorphism, so it is undefined here — correct.
(For the record: `dim Der(M_2(F_3)) = 3`, `dim BSDer_{σ_α}(A)^α = 1`.)
(b) `A = K[ε]/(ε²)`, `α(ε) = -ε`, `D(a+bε) = bε`: derivation, `α`-derivation,
`Dα = αD` — all checked. Computed dimensions:
`char K ≠ 2` (`Q`, `F_3`, `F_5`): `dim Der = dim ADer = dim BSDer^α = 1`, all
spanned by `ε ↦ ε`, so the classes coincide; `char K = 2`: `α = id`,
`dim BSDer_{σ_α} = 4 = dim End_K(A)` (the product `x∘y = 2xy` vanishes) and
`dim ADer = dim Der = 2` (spanned by `ε↦1`, `ε↦ε`). The printed pair `(4,2)` is right.

## 16. §4, Remark `rem:commutativity-needed` (lines 591–609) — VERIFIED

`A` four-dimensional over `F_3` with `1` a unit, `t² = tv = vt = tw = wt = 0`,
`v² = w² = wv = t`, `vw = 0`.
* Associativity: checked all 64 triples of basis elements (computer, and by hand:
  every product involving `t` vanishes and the eight triples over `v,w` give `0` on
  both sides). So `A` is associative.
* `α(t) = t`, `α(v) = -v`, `α(w) = -w`: multiplicative on all 16 basis pairs
  (`α(wv) = t = (-w)(-v)`, `α(vw) = 0 = (-v)(-w)`), `α² = id`. Involutive automorphism.
* `D(v) = v+w`, `D(1) = D(t) = D(w) = 0`: `Dα = αD`; the `σ_α`-Leibniz rule holds on
  all 16 basis pairs (computer: no failing pair). `D` is not a derivation:
  `D(vw) = D(0) = 0` while `D(v)w + vD(w) = (v+w)w = vw + w² = t ≠ 0`.
* Solving the linear systems: `dim BSDer_{σ_α}(A)^α = 3`, `dim Der(A)^α = 2`
  (also `dim BSDer = 3`, `dim Der = 4` without the commutation condition). Matches.
* `E_D(v,w) = D(vw) - D(v)w - vD(w) = -(vw + w²) = -t`, and
  `E_D(w,v) = D(wv) - wD(v) - D(w)v = -(wv + w²) = -2t = t` in `F_3`: antisymmetric at
  `(v,w)`, as printed.
* `(v+w)² = v² + vw + wv + w² = t + 0 + t + t = 3t = 0`, and `v + w ∈ A_-` is nonzero:
  a nonzero square-zero skew element. Consistent with the symmetric-defect statement.
* "neither commutative (`vw = 0` while `wv = t`) nor reduced (`t² = 0`, `t ≠ 0`)" — correct.
* Finite-field paragraph: reduced ⇒ radical (nilpotent, finite dimension) zero ⇒
  semisimple ⇒ (Wedderburn) `∏ M_{n_i}(D_i)`; `e_{12}² = e_{11}δ_{22} = 0` kills `n_i ≥ 2`;
  over a finite field each `D_i` is finite hence a field, so `A` is commutative and no
  witness exists. Logic correct.
* Quaternions: `H` over `Q` (rational structure constants), `dim Der(H) = 3`,
  and for `α` = conjugation by `i` (and by `j`, by `k`): `dim Der(H)^α = 1`,
  `dim BSDer_{σ_α}(H)^α = 1`, and `dim BSDer_{σ_α}(H) = 1 < 3` without the commutation
  condition; for `α = id`, `dim BSDer_τ(H) = dim Der(H) = 3`. All printed numbers right.
  Involutive automorphisms of `H`: identity and `x ↦ qxq^{-1}` for pure imaginary unit
  `q` (inner automorphisms are `SO(3)`, involutions are rotations by `π`). Transitivity:
  `u = 1 - q'q` satisfies `u q = q + q' = q' u`, so if `u ≠ 0` then `u q u^{-1} = q'`;
  `u = 0` iff `q' = -q` (the real part of `q'q` is `-q'·q`), and then the two
  conjugations coincide. Checked numerically for `q = i`, `q' = j` and
  `q = i`, `q' = (3i+4j)/5`: `u q u^{-1} = q'` exactly (rational arithmetic).
* Three-forms sentence (lines 619–635): see item 17.

## 17. §4, three-forms sentence (lines 619–635) — VERIFIED

(i) `D ∈ Der(A)`, (ii) `E = 0` on `A_+×A_-`, (iii) `E = 0` on `A_-×A_-`; in the
context of this part of the remark `A` is reduced with `2 ∈ K^×` and
`D ∈ BSDer_{σ_α}(A)^α`.
* (i) ⇒ (ii),(iii): `E = 0` trivially.
* (iii) ⇒ (i): `E` vanishes on `A_+×A_+` (the restricted map is a Jordan derivation of
  the reduced, `2`-torsion-free ring `A_+`, hence a derivation by Theorem `thm:bresar`)
  and on `A_-×A_-` by hypothesis. Mixed pairs: `E(x,y), E(y,x) ∈ A_-` by parity, so
  `E(x,y) - E(y,x) ∈ A_-`, and it equals `E_a(x,y) ∈ A_+` (item 8), hence `0`: `E` is
  symmetric. Then the argument of Theorem 4.1 (which uses only symmetry of `E`,
  `E` taking values in `A_-`, and reducedness) gives `E = 0`.
* (ii) ⇒ (i): `E` vanishes on `A_+×A_+` and on mixed pairs; on `A_-×A_-` it is
  alternating (`E(x,x) ∈ A_+` by parity and `∈ A_-` by Proposition (i) at `(x,x)`),
  hence antisymmetric. So `E` is antisymmetric, `D` is a Jordan derivation of `A`, and
  `A` reduced ⇒ semiprime and `2`-torsion-free ⇒ `D` is a derivation (Bresar; the
  `∘`/`x²` forms agree by item 1).
All three implications are valid, so the equivalence holds, and the consequence
("a counterexample has a nonzero defect on the mixed pairs as well as on `A_-×A_-`")
is the contrapositive. Also correct: `E_a(x,y) = D([x,y]) - [D(x),y] - [x,D(y)]`
(expand `E(x,y) - E(y,x)`), so `E_a = 0` says `D` is a derivation for the bracket.

## 18. The abstract (lines 61–72) against the body — VERIFIED

Ten sentences, each checked against the body:
1. "We study braided-symmetric derivations…" — §2. 2. "Leibniz rule for the product
symmetrized by an involution of `A⊗A`" — Definition `def:sigma-derivation`.
3. "The identity involution gives the ordinary derivations when 2 is invertible" —
line 234. 4. "The swap gives the Jordan derivations" — line 238. 5. "negative of the
identity gives all linear endomorphisms, negative of the swap the Lie derivations" —
lines 249–253. 6. "twist the swap by an involutive automorphism or anti-automorphism"
— §3. 7. "The Leibniz defect of a map that commutes with `α` decides when it is a
twisted derivation" — `prop:defect`. 8. "commutative reduced + 2 invertible: the
twisted maps are exactly the derivations commuting with `α`" — Theorem 4.1; "on
2-torsion-free semiprime algebras the Jordan maps among them are exactly those
derivations" — Corollary 3.5. 9. "On `F_3[ε]/(ε³)` the two classes do not contain
each other" — Proposition 4.3. 10. "Nilpotent elements show reducedness is needed,
characteristic 2 that invertibility of 2 is needed, and a four-dimensional example
that reducedness and commutativity cannot both be dropped" — Examples 4.2, 4.4 and
Remark 4.6; note the abstract's careful phrasing ("cannot both be dropped") matches
the body's explicit disclaimer at line 603.
No clause overstates what is proved. The abstract omits two results of the body — the
completeness of the classification of natural involutions (Remark 2.5) and the
three-forms equivalence (Remark 4.6) — but both are remarks rather than main results
and no sentence of the abstract is false on that account.

---

## Must change

**Nothing.** No statement of the paper is false, and I found no step that does not
follow. In particular the two places earlier reviews repaired are correct as printed
in v79: the residual-identity sentence (lines 383–385) is true in both directions
under its conditional, and the second "stronger statement" of Theorem 4.1 is exactly
what the argument proves.

## Wording (optional, not errors)

1. Line 494: "Over a perfect field no finite-dimensional instance exists" can be read
   as denying that finite-dimensional reduced commutative algebras exist over a
   perfect field, which is false (`F_2[t]/(t²+t+1)` is one). Minimal repair: *"Over a
   perfect field every finite-dimensional instance is trivial: … and a separable
   extension has no nonzero `K`-derivation, so `Der(A) = 0`."*
2. Line 168: the inference is cancellation, not division by `2`; since §2 later relies
   on `D(1) = 0` in characteristic 2 (line 236), *"since `D(1) = D(1·1) = 2D(1)`, which
   forces `D(1) = 0` in every characteristic"* would forestall the natural objection.

## What rests on computation, and what on hand algebra

* Hand only: items 1 (linearization), 3 (the four products and the char-2 witness),
  4(a),(b),(d),(e), 5, 6, 7 (the two expansions), 8 (sum/difference), 9, 10, 11 (the
  whole proof and the two stronger statements), 12 (the perfect-field sentence),
  17, 18.
* Hand plus exact computation (mine, and independently `.skill/bsd-exact-algebra`,
  which reproduces every printed dimension and exits 0): the dimension and
  membership claims of items 4(c),(f), 13, 14, 15, 16, and the pair-by-pair
  verifications quoted in items 7 (six settings, including non-involutive `α` and a
  non-unital algebra), 8, 9 (625 elements of `M_2(F_5)`), 10.
