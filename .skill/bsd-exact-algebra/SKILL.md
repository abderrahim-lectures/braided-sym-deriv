---
name: bsd-exact-algebra
description: "Recompute, extend or check any finite-dimensional claim of the braided-symmetric derivations paper: dimensions of Der, JDer, BSDer_sigma, BSDer_{sigma_alpha}^alpha, ADer, and the algebras of Section 4. Ships a validated exact solver over F_p and Q and a battery that reproduces every number in the paper (and two beyond it) in under a second. Use instead of writing a new solver, and before reporting any dimension."
---

# Exact algebra for the BSD paper

One command, from this directory:

```bash
python3 cases.py
```

It prints one line per case and exits 0 iff every number reproduces. A green run
in ~0.3 s means: the dimensions of Remark 2.4, Example 4.2, Example 4.3,
Proposition 4.4, Example 4.5(b) and Remark 4.6 all still hold, the harness still
agrees with brute-force enumeration where that is possible, and the two
quaternion computations are unchanged. **Run it before you recompute anything by
hand and before you report a dimension.**

`BASELINE.md` holds the number table with the paper line and the Lean
declaration each row corresponds to, plus the list of findings that are
**closed** — read it before writing a review, so you do not re-report them.

## What is here

| file | what it is |
|---|---|
| `harness.py` | the solver: structure constants → linear system → dimension; `F_p` and `Q`; brute-force checker |
| `cases.py` | the battery, with expected values; exits 1 on any mismatch |
| `BASELINE.md` | every number, its source, the closed findings, the open question's state |

No dependency beyond the standard library. No network. No Lean.

## Conventions (get these wrong and the answer is wrong silently)

* D is an `n × n` matrix with `D[a][b]` = the `a`-th coordinate of `D(e_b)`;
  the unknown vector index is `a·n + b`.
* A product `P` is `P[i][j] = e_i·e_j`.
* The solved condition is `D(P(x,y)) = Q1(Dx,y) + Q2(x,Dy)` on every basis pair.
  * braided-symmetric derivation: `P = Q1 = Q2`
  * derivation: `P = Q1 = Q2 = mul`
  * α-derivation: `P = mul`, `Q1(u,y) = u·α(y)`, `Q2(x,v) = α(x)·v`
  * twisted product: `P[i][j] = e_i e_j + α(e_j)α(e_i)` (this is `σ_α`)
* `alpha` is the matrix `alpha[k][i]` = `k`-th coordinate of `α(e_i)`.

## The two bugs this file exists to stop

1. **A vector equation collapsed to one scalar row.** Each component `k` is a
   separate equation; summing over `k` weakens the system. The first harness
   written for the v73 review did this and got `dim Der(M_2(F_5)) = 5` instead
   of 3.
2. **A transposed unknown index in the commutation rows.** The coefficient of
   `D[t][i]` is `α[k][t]` and the unknown sits at `t·n + i`; writing `k·n + t`
   leaves the constraint inactive and inflates every dimension.

Both were caught only because the harness was validated against brute force on a
case small enough to enumerate (`F_5[ε]/ε²`, 625 maps) and against a table with
known values (`M_2(F_5)`). **Never add a case without at least one of those two
checks.**

## Adding a case

1. Write the structure constants (`mk(n, terms, p)`), the product, and the
   α-matrix if any.
2. Compute the dimension with `dim` (F_p) or `dim_q` (Q).
3. Put the expected value you can defend — from the paper, from Lean, or from a
   direct derivation — in `check(...)`.
4. If the case is small enough (`n ≤ 2`, `p ≤ 5`), also assert `brute(...)`.

**Never edit an expected value to make the run green.** If a value moved, either
the paper changed or the harness broke; the difference is the finding.

## What this is not

It is evidence, not a kernel check. Where the Lean development proves the same
statement (`Dimensions.lean`, `QuaternionCase.lean`, `Example45b.lean`,
`Closures.lean`), the kernel is the stronger evidence and this script is the
independent cross-check. Where Lean cannot go cheaply (the 8-dimensional
`ℍ ⊗_Q ℚ(√2)` case), this is the only evidence, and it should be reported as a
computation.
