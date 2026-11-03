# Review of branch `review/v79-paper-fixes` at 04c3eed

- reviewer: `deepseek-v4-1-flash` — I wrote `review/v79-word-level`, one of the two branches
  this one merges; I did not write its own eight precision fixes, its merge commit, or its two
  reviews. Where I check my own text below I say so.
- branch: `review/v79-paper-fixes`, tip `04c3eed`
- verdict: **ok**

## Claims the branch makes

- it merges `review/v79-word-level` (my prose repairs) and `review/v80-citations` (two located
  citations), and adds its own eight precision fixes from the v79 deep review;
- the joint result passes the repository gate on both legs (13 pp, 0 overfull, 0 undefined, text
  identical to the released PDF);
- it answers the open finding on `review/v80-citations` by correcting the Weibel locators.

## Findings

(or: none)

## What I checked, and what I did not

- **The merge is clean, and it is what it says.** `git diff review/v79-word-level:paper/braided-sym-deriv.tex
  04c3eed:paper/braided-sym-deriv.tex` returns exactly the seven text changes of the precision fixes
  and nothing else, so my repairs are carried verbatim and none was lost in the merge. The
  `494` rewrite survives, and the second sentence I added ("the instances with a nonzero derivation
  are infinite-dimensional") is still there.
- **The four substantive precision fixes are right, and I re-derived each:**
  - `paper/…:391` — the case-(ii) form of the residual difference is `(Dα − αD)(xy)`, not `(yx)`;
    the branch now prints both cases, and "the products `yx`, and likewise `xy`, span a unital `A`"
    is true (`y·1` and `1·y` give every element).
  - `paper/…:625` — `E_a` takes values in `A_+`, and the old printed reason (the bracket formula) does
    not give it: on a mixed pair the bracket formula gives `A_-`. The new reason is correct:
    applying Proposition 3.2(i) at `(x,y)` and at `(y,x)` gives `U = −α(V)`, `V = −α(U)`, hence
    `α(U − V) = U − V`, so `E_a ∈ A_+`. **This was a real gap in v79 that my own proof referee passed**;
    the conclusion was right and the printed reason was not.
  - `paper/…:618` — `u = 1 − q'q` is used as an inverse and v79 never showed `u ≠ 0`. The new argument
    is right: `uū = 2 − (qq' + q'q)`, and `qq' + q'q = 2` would give `(q+q')² = 0`, hence `q' = −q`,
    which the sentence excludes.
  - `paper/…:641` — the "a counterexample has a nonzero defect on the mixed pairs" sentence was false
    without a scope: the paper's own Remark 4.6 example has `E = 0` on every mixed pair (I checked
    `E(1,v)`, `E(t,v)`, `E(v,1)`), and it is a counterexample. The branch pins the sentence to reduced
    `A` and says why the example escapes. Correct.
- **The two smaller ones are right too.** `paper/…:619` now says the computation gives `3` and that
  the two classes agree by Theorem 3.4 — v79 attributed the value to Bresar's theorem, which gives
  only the equality. `paper/…:154` adds the `dim_K A ≤ 1` case to the roadmap, which Remark 2.5
  already had.
- **My finding on `review/v80-citations` is answered as it asked:** the `Lemma 9.2.1 / Theorem 9.2.11`
  locators are gone, replaced by `\citep[Proposition 9.2.2 and Corollary 9.2.9]{Weibel1994}`. Those are
  the quotable items: Corollary 9.2.9 is "a finite-dimensional commutative algebra over a field is
  separable if and only if it is a product of separable field extensions", and Proposition 9.2.2 is
  `H¹(R,M) ≅ M ⊗_R Ω_{R/k}`, which gives `Der = 0` once `Ω = 0`. `grep` finds no occurrence of the
  old locators left.
- **The gate, run by me on this tip** (read-only detached worktree, `tools/papercheck.py --skip-lean`):
  `pdf: fresh 13 pp vs released 13 pp, 0 overfull, 0 undefined, text identical, released label ok` —
  PASS. I did not run the Lean leg; the branch's Lean changes are docstrings only.
- **not checked:** the branch's own `lake build` and axiom audit (docstring edits only, so the risk is
  a parse error, and the files are unchanged from the tree the gate passed on); and the step
  "a separable field extension has `Ω = 0`", which is classical and sits in Weibel §9.2/§9.3 in a page
  the scan has lost — the two locators named are the right ones, but that link is not readable on disk.
- **on my own content:** the review of my branch that this one carries is right that mine "should not
  merge alone" — the four fixes above are not in mine, and two of them repair statements that were
  wrong as printed. I agree with its conclusion.

## Note on the toolchain, not on the branch

`loom agree` cannot gate this branch: it is `review/*`, and the tool reads reviews only for
`loom/v<N>/<model>/<role>-<k>` branches. So this review is a file for the owner to read, not a row
the gate will count. Filed in `loom/deepseek-v4-1-flash/ISSUES.md`.
