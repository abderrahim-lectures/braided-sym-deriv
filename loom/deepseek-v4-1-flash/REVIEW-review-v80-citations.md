# Review of branch `review/v80-citations`

Reviewer: `deepseek-v4-1-flash` (wrote none of this branch). Author: another model, id unknown to me —
the branch carries no `loom/` directory and no report.
Branch tip reviewed: `69ab980` (`v80: the README reference list matches the seventeen-entry
bibliography`).
Verdict: **ok with findings**. One finding is positive (a citation that is right), one is negative (a
citation that does not carry its sentence), and one is not mine to settle (a version collision with my own
branch, raised for the owner).

What I read: `git diff main...review/v80-citations` (4 files, +10/−7), the two source texts it cites
(`loom-pack/references/text/weibel-homological-algebra.txt`, `(Mostly) Commutative Algebra-Springer Nature
Switzerland (2021).txt`), the release PDF out of the branch (`pdfinfo`, `pdftotext` on page 1), and the
README diff. I did not build the branch; the PDF claims 13 pages and page 1 prints `Preprint version 80`.

## Findings

1. `paper/braided-sym-deriv.tex:601` — **correct, and a real improvement**. The sentence now says "each of
   which is a field by Wedderburn's little theorem when the base field is finite
   \citep[Exercise 4.9.19]{ChambertLoir2021}". The source says, at scan lines 9669–9670: "Exercise (4.9.19).
   — In this exercise, we give a proof of the following theorem of Wedderburn: Any finite division ring is a
   field." The named theorem now carries a located citation, which it lacked in v79. Nothing to fix.

2. `paper/braided-sym-deriv.tex:494` — **the added locators do not carry the sentence**. The sentence needs
   "a separable extension has no nonzero `K`-derivation", and it now cites
   `\citep[Lemma 9.2.1 and Theorem 9.2.11]{Weibel1994}`.
   - Lemma 9.2.1 is quotable from the scan and is a different statement: "Lemma 9.2.1 `H¹(R, M) =
     Der_k(R,M)/PDer_k(R,M)`" (Weibel §9.2, the part of the scan numbered 306–307).
   - Theorem 9.2.11's own statement is **not in the scan**: the page that would hold it is missing after
     Corollary 9.2.9, and the text resumes mid-proof. Its two internal cross-references (scan lines 13628
     and 13894: "In 9.2.11 we saw that this … implies `H_n(R,R) = 0` for all `n ≠ 0`") identify it as the
     separability-and-vanishing theorem, not as the derivation statement.
   - What does support the sentence, quotably: **Corollary 9.2.9** ("a finite-dimensional commutative
     algebra over a field is separable if and only if it is a product of separable field extensions") for
     the first half, and **Proposition 9.2.2** ("`H¹(R,M) ≅ M ⊗_R Ω_{R/k}`") for the second, which gives
     `Der = 0` once `Ω_{L/K} = 0`.
   - What would fix it: cite `[Proposition 9.2.2 and Corollary 9.2.9]`, or leave the sentence with the
     Pierce locator only, as v79 had it. A citation that names an item the source does not print is worse
     than none, because a reader who looks it up finds a different theorem.

3. **Two releases numbered v80.** This branch sets `\paperversion` 80, the jobname to `…-v80`, and
   `pdf/braided-sym-deriv-v80.pdf` (13 pages, 393 729 bytes). My branch `review/v79-word-level` also
   releases v80 (13 pages, 393 526 bytes) with different content: a rewritten sentence at 494, two Weibel
   locators moved from §9.1 to §1.1, two antithesis pairs removed, three long sentences split and fourteen
   smaller repairs. The two cannot both merge as v80; whichever merges second must be renumbered, and its
   changelog entry edited. This is **one question for the owner**, not something I settle here: which of the
   two v80s is the release, and is the other one to be re-derived on top of it? They are complementary —
   this branch adds citations, mine repairs prose and locators — so the cheapest resolution is to merge one
   and re-apply the other's two citation edits (or my prose repairs) on the new tip.

4. `README.md` — the numbered reference list now matches the seventeen-entry bibliography, with Pierce as 15
   and the two old entries shifted to 16 and 17. That is right, and it is the same repair I made on my
   branch; the collision in point 3 covers it.

5. `paper/latexmkrc` — jobname `braided-sym-deriv-v80`. Consistent with the version macro. Nothing to fix.

## What I could not check

- I did not rebuild this branch, so I cannot say whether its PDF is text-identical to a fresh build; I
  checked only that it is 13 pages and prints version 80 on page 1.
- I have not read Theorem 9.2.11's statement anywhere, because the copy on disk has lost the page. My
  finding 2 rests on Lemma 9.2.1 being a different statement and on the two cross-references, not on a
  quotation of 9.2.11 itself. If the author has the page, the finding is settled by quoting it.

## Note on the toolchain

`loom review review/v80-citations` refuses: the tool writes a skeleton only for
`loom/v<N>/<model>/<role>-<k>` branches. So this review is hand-written in the protocol's file layout, and
`loom agree` cannot gate a `review/*` branch at all. Filed in `loom/deepseek-v4-1-flash/ISSUES.md`.
