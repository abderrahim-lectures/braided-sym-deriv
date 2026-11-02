# Baseline — every number of the paper, and what is already closed

Use this before writing any review of the paper. It is the state of play at
**v73** (669 lines, `\paperversion` 73, 12 pages, `60138de`). Line numbers are
v73's; they move, so grep for the statement, not the number.

## 1. The numbers

`python3 cases.py` reproduces all of these. "Lean" is the declaration that
`lean/RESULTS.md` claims proves the same thing; the gate audits its axioms, not
its statement, so treat the column as a pointer.

| paper | object | value | Lean |
|---|---|---|---|
| Rem 2.4 (225–257) | `F_5[ε]/ε²`, `id, τ, −id, −τ` | 1, 1, 4, 4 | `BSDGeneral.bsd_id_iff_der`, `bsd_neg_id_all`, `bsd_neg_tau_is_lie` |
| Rem 2.4 (262) | `σ=(T⊗T⁻¹)τ`, `T(1)=1, T(ε)=1+ε` | `BSDer_σ = {0}` | — (computation only) |
| Ex 2.3 (212) | `K × K`, swap product | not associative, no unit | `BSD.Example23.not_assoc`, `no_unit` (F₅) |
| Ex 4.2 (492) | `F_5[u,v]/(u²,v²)`, `D(uv)=uv` | in `BSDer^α`, not a derivation; `E(u,v)=uv`, `(uv)²=0` | `TwistedCommutative.UV.*`, `Closures.UV_*_all` (625 pairs) |
| Ex 4.3 (510) | `F_2 × F_2`, `D(p)=D(q)=e` | in `BSDer^α`, not a derivation; `dim BSDer^α=1`, `dim Der=0` | `BSD.Example43.*` |
| Prop 4.4 (525) | `F_3[ε]/ε³`, `α(ε)=−ε` | `dim Der=3`, `dim ADer^α=1`, `dim BSDer^α=1`; the two witnesses cross as printed | `TwistedCommutative.TW.*`, `Closures.TW_*_all` (81 pairs) |
| Ex 4.5(b) (579) | `K[ε]/ε²`, char ≠ 2 | `ADer^α = Der = BSDer^α`, dim 1 (F₃, F₅) | `Example45b.*` (arbitrary field) |
| Ex 4.5(b) (582) | `K[ε]/ε²`, char 2 | `BSDer = End` (4), `ADer = Der` (2) | `Example45b.bsderSub_eq_top`, `derSub_eq_span_of_char_two` |
| Rem 4.6 (595) | 4-dim `F_3` algebra | `dim BSDer^α = 3`, `dim Der^α = 2`, `dim Der = 4`, `dim BSDer = 3` | `Dimensions.lean`, `Remark46.lean` |
| Rem 4.6 (596) | same | `E(v,w) = −t`, `(v+w)² = 0`, `E(v,v)=E(w,w)=0` | `Remark46.lean` |
| Rem 4.6 (601) | `ℍ`, `α = conj` | `dim Der = 3`, `dim Der^α = dim BSDer^α = 1`, `dim BSDer = 1` | `QuaternionConjug.class_is_line`, `QuaternionCase.jder_eq_der_quaternion` |
| Rem 4.6 (601) | `ℍ`, `α = id` | all 3 (Theorem 3.4) | `QuaternionCase` |

### One number the paper does not have

`A = ℍ ⊗_Q ℚ(√2)`, `α = id ⊗ conj`. Then `A` is the quaternion algebra `(−1,−1)`
over `ℚ(√2)`, a division algebra because `ℚ(√2)` is formally real; it is
8-dimensional over ℚ, reduced, not commutative, and **`A_+ = ℍ` is not
commutative** — outside every class the paper or the removed appendix covers
(the appendix's rank-one proposition assumes `A_+` commutative).

```
dim Der = 6,   dim Der^α = 3,   dim BSDer = 3,   dim BSDer^α = 3
```

So the conclusion of Theorem 4.1 holds there. This is evidence for the open
question, not a proof, and `cases.py` reproduces it. If the paper is ever
revised, this belongs in Remark 4.6 as one sentence.

## 2. Findings that are CLOSED — do not re-report them

These cost earlier sessions real time. Each was checked against the file, not
against a changelog.

* Remark 2.4's completeness claim is stated for the functor `V ↦ V⊗V` on
  `K`-vector spaces (v63), which is true; the algebra reading was the false one
  and is gone. Completeness, the char-2 family `λ·id+(1+λ)τ`, and the idempotent
  correspondence are all proved (`Remark24.lean`).
* "Commutativity is needed" is gone: Remark 4.6 is titled "Reducedness and
  commutativity cannot both be dropped" and explicitly makes no claim about
  commutativity alone. The proof of Theorem 4.1 no longer says otherwise.
* Line 260's `id − 2P` example carries `2 ≠ 0` and `dim_K A ≥ 2`.
* Herstein's definition is the `∘` form (§1, p. 1104), with the square form as
  his char ≠ 2 equivalent.
* Corollary 3.5 says `K`-algebras, not rings.
* The char-2 family is the *whole* list of natural involutions, not "as well".
* The residual identity without `Dα = αD` is printed, with the `(Dα−αD)(yx)` term.
* The `ad_g` criteria for anti-automorphisms (`g + α(g) ∈ Z(A)`) and Cor 3.5 for
  anti-automorphisms are in (v62).
* Example 4.5(a) takes a nonzero skew `g`; its witnesses are structural
  (`ex45a_*`), not `#eval`-only; Example 4.5(b) is kernel-checked over an
  arbitrary field.
* The binary-`σ` encoding cannot express `−id`/`−τ` over `F₃` — documented in
  `Paper.lean`'s header, with the pair encoding in `Background/Nonassoc.lean`.
  This is a ledger row, not a defect.
* The released PDFs are not stale (v60–v73 each print their own label; "0
  overfull" is a v62+ property).
* `Remark46.lean`'s docstring parametrisation, the `LieDerivation` clash, the
  toolchain pin and the missing manifest are all fixed; `lake build` is green
  under `v4.36.0-rc2` with a committed manifest.
* Herstein's theorem *is* numbered 3.1 (the JSTOR OCR splits "3.1." from
  "THEOREM" — see §3).
* Hochschild "§§2 and 4" is not over-broad: §2 defines the cocycle and §4
  identifies derivations with `(1,C)`-cocycles.
* Martindale p. 183 was read from the page image and matches.
* The referencelist has 17 entries, of which 16 are in `results/refs/`
  (Pierce 1982 is not).
* Line 610's "`E` is alternating on `A_− × A_−`" is true: `E(x,x) ∈ A_+` by the
  direct computation and `∈ A_−` by Prop 3.2(i) at `(x,x)`.

## 3. Traps that produced false findings before

* **OCR splits of theorem numbers.** A grep for `THEOREM 3.1` in the Herstein
  scan finds nothing; the page reads `3.1. … THEOREM` over a line break. Read the
  block before declaring a locator wrong.
* **A claimed fix applied in one place only.** The v73 changelog says
  `lean/BACKGROUND.md` "no longer pins v63"; the header was fixed and §2 still
  says "at v63", with locators 5–10 lines stale. Check the whole file, not the
  diff hunk.
* **A vector equation collapsed to one row, or a transposed unknown index**, in
  any hand-written linear-algebra check. Validate against brute force.
* **A stale cross-review ledger.** `results/reviews-timeline.md` still says
  "(v62)" and still has the phantom "completeness pinned in v62" row.
* **Search may be unavailable.** The platform's web-search endpoint returned
  `service_error` throughout the v73 review, so novelty could not be checked
  externally. Say so; do not imply a literature check that did not happen.

## 4. The open question: exact state

Remark 4.6 reduces the question to: `E_D = 0` on `A_− × A_−`, where `E_D` is
alternating with values in `A_+` and `A` is reduced with `2` invertible.

What is settled:

* `A_+ × A_+`: `D|_{A_+}` is a Jordan derivation of `A_+`, hence a derivation by
  Brešar — `E = 0`.
* mixed pairs: `E_a = 0` by parity.
* fixed-point-free factor permutations: settled (swarm `smvy6m9bh`, m6's
  Theorem 7′).
* division rings with `A_+` commutative: the rank-one proposition (removed
  appendix A.4).
* quaternion division algebras over any field: removed appendix A.1.
* `ℍ ⊗_Q ℚ(√2)`: this review, §1 above — the first case with `A_+`
  non-commutative.

What is not settled:

> `A` a division ring (finite-dimensional over a field), `α` an involutive
> automorphism, `A_+` not commutative. Then `A = A_+ ⊕ A_+y` with `y² ∈ Z(A)`,
> a degree-2 cyclic extension of a division ring; is every `D ∈ BSDer_{σ_α}(A)^α`
> a derivation?

In finite dimension this is the *only* remaining case: a reduced finite-
dimensional algebra is a product of division rings (Wedderburn), `α` permutes
the factors in 1- or 2-cycles, and for a division ring `A_− = A_+y` always (for
`0 ≠ y ∈ A_−`, `x y⁻¹ ∈ A_+`).

Conjecture worth stating in the paper: the conclusion of Theorem 4.1 holds for
every reduced `A` with `2` invertible and `α` an involutive automorphism.

## 5. Cost of the checks

| check | wall time | needs |
|---|---|---|
| `python3 cases.py` | 0.3 s | python3 only |
| `python3 tools/papercheck.py` | ~35 s warm, ~4 min cold | latexmk, elan toolchain, built Mathlib |
| the whole paper read once | 1–2 h | — |
