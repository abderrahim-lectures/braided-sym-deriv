# Review of branch `review/v79-paper-fixes` (the joint v80), tip `04c3eed`

- reviewer: `kimi-k3` (did not write this branch; I wrote one of the three branches it merges,
  `review/v80-citations`, and both of the reviews whose findings it answers)
- author: `m-1bad6a'`s joint release (PR #11), at tip `04c3eed`
- written: 2026-11-03

`loom review` refuses non-`loom/*` branch names, so no skeleton was used; the format follows it.

## What this branch is

The joint v80: merges `review/v79-word-level` (deepseek's prose and locator repairs) and
`review/v80-citations` (my two citation repairs), on top of m-1bad6a's own v79 review with its
eight precision fixes, answering both findings on my branch. 15 files; the paper, its v80 PDF,
the README (version line, the Pierce entry, the joint changelog), `lean/RESULTS.md` (the root-level
names), `lean/BACKGROUND.md` (v80 map), docstring pins.

## Findings

1. `paper/braided-sym-deriv.tex`, the non-vacuity paragraph, the citation
   `\citep[Proposition 9.2.2 and Corollary 9.2.9]{Weibel1994}` — **does not quite carry the
   sentence's second half** ("a separable extension has no nonzero $K$-derivation"). Both items
   are real and quotable from the full text (Prop 9.2.2 at scan line 12460: `H₁(R,M) ≅ M ⊗_R Ω_{R/k}`;
   Cor 9.2.9 at line 12571: separable ⇔ product of separable field extensions). But the chain needs
   `Ω_{L/K} = 0` for a finite separable field extension, and **no item in the pack's Weibel text
   states that** (`unramified` and `formally smooth` do not occur in it at all; 9.2.4 is
   "Alternate Calculation"). The theorem that closes the gap is Theorem 9.2.11 — which the pack
   holds as an *excerpt* (`loom-pack/references/excerpts/Weibel1994_Theorem_9_2_11.txt`,
   "p. 310, transcribed from the scan": separable ⇔ `Hⁿ(R,M) = 0`, `n > 0`), even though the
   full-text file drops that page. What would settle it: cite
   `[Proposition 9.2.2, Corollary 9.2.9 and Theorem 9.2.11]`, or use the excerpt pair
   `[Lemma 9.2.1 and Theorem 9.2.11]` my branch had (H¹=0 by 9.2.11, `Der/PDer = 0` by 9.2.1,
   `PDer = 0` over a commutative ring). Either is complete; both are on the pack's record.

   For the record, on the finding both other reviewers filed against my branch: the absence of
   Theorem 9.2.11's statement from the pack's full-text file is **confirmed** (I checked lines
   13628, 13894, and Corollary 9.2.9's neighbourhood), and so their locator proposal survives as
   far as the on-disk text goes; the excerpt is what they did not use, and it is the pack's own
   mechanism for exactly this case. Both readings are now on the record for the owner.

## Checked here, found right (each verified, not trusted)

- The false-sentence repair at the non-vacuity paragraph is right, and needed: `F₅ × F₅` with the
  swap satisfies every hypothesis of Theorem 4.1 and has `Der = 0` (perfect field ⇒ separable
  factors ⇒ no derivations), so v79's "no finite-dimensional instance exists" was false as
  printed, and "every finite-dimensional instance has `Der(A)^α = 0` … so the instances with a
  nonzero derivation are infinite-dimensional" is the true sentence. (`F₂ × F₂` in the battery is
  the char-2 sibling; the battery's `Ex4.3` sums agree.)
- The 494 sentence now carries all of: the F-5-style counterexample reality, the Pierce line
  (UNCHANGED, as the UNVERIFIED status demands), and the Weibel pair.
- The eight precision fixes, each re-derived: the case-(i)/(ii) residual display with the
  products-span argument (the `y = 1` argument, correct and stated now); the "2 is used for the
  splitting" clause (correct: spanning and `A₊ ∩ A₋ = 0`); the dim-≤-1 clause in the roadmap
  (consistent with Remark 2.4's own last paragraph); the `Eₐ ∈ A₊` justification by Prop 3.2(i)
  at `(x,y)` and `(y,x)` (correct: `α(E(x,y)) = −E(y,x)`, `α(E(y,x)) = −E(x,y)`); the nonzero-`u`
  proof `uū = 2 − (qq' + q'q)` and `(q+q')² = 0` (correct, both recomputed); the α = id values-3
  attribution; the closing sentence's new scope "for reduced `A`", with the printed example's
  escape checked by hand (`E ≡ 0` on every mixed pair there — `(1,·)` by `D(1) = 0`, `(t,v)` by
  `tv = tw = 0` — and the algebra is not reduced); the Weibel `§§1.1 and 9.1` / `§1.1` locators
  (vocabulary lives in Chapter 1 as the review says, the complex in §9.1).
- My Chambert-Loir citation is carried over verbatim (both other reviewers verified it against
  scan lines 9669–9670), and the README gains the Pierce entry I added and the joint version line.
- `RESULTS.md`'s prop:defect row now spells the names as the kernel does (`prop_defect_aut`,
  root level) — matches my `lake env lean` check above.
- The joint PDF: 13 pages, 0 Type 3 fonts, page 1 prints `Preprint version 80` (checked from the
  released artefact in the branch).
- Their claims about the two conflict sites (quaternion paragraph intertwined with its `u ≠ 0`
  proof) match the diff as I read it.

## Not checked

- Their gate line (`lake build` green with 7 modules rebuilt). I did not rebuild the joint tree;
  the docstring-only Lean edits make the risk low, and their elaboration-of-four-files fallback is
  recorded in PR #10.
- `BACKGROUND.md`'s row-by-row v80 remap (spot-checked two rows; no error seen).

## Verdict

**ok with findings** — finding 1 above is the one open item. Everything else is verified. The
branch supersedes my `review/v80-citations` (PR #9): I endorse it as the v80 release candidate
once finding 1 is answered (one locator line — either citation pair above completes it at the
pack's own record).
