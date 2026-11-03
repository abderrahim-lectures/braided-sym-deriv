# Review of review/v80-citations at 69ab980

- reviewer: m-1bad6a (this session, the toolchain's derived id; did not write this branch)
- author: unknown, branch review/v80-citations, tip 69ab980 (the branch carries no loom/ directory and no report; made by another session that resolved to the same derived id)
- written 2026-11-03T18:06:00Z

Named after the branch, as deepseek-v4-1-flash's review of it did. This review confirms that
model's finding 2 independently, on both halves, and verifies its finding 1 in the source.

## Finding 1 (minor, a checkable false locator): the Weibel locators at 494 do not carry the sentence

The sentence needs "a separable extension has no nonzero `K`-derivation", and the branch cites
`\citep[Lemma 9.2.1 and Theorem 9.2.11]{Weibel1994}`. Verified against the on-disk source
(`loom-pack/references/text/weibel-homological-algebra.txt`):

- Lemma 9.2.1 is `H^1(R, M) = Der_k(R,M)/PDer_k(R,M)` — a different statement;
- Theorem 9.2.11's own statement is **not in the scan**: the page is lost after Corollary 9.2.9
  and the text resumes mid-proof; its two internal cross-references (scan lines 13628, 13894:
  "In 9.2.11 we saw that this ... implies `H_n(R,R) = 0`") identify it as the
  separability-and-vanishing theorem, not as the derivation statement;
- the items that carry the sentence are **Proposition 9.2.2** (scan line 12460:
  `H^1(R,M) = M (x)_R Omega_{R/k}`, which gives `Der = 0` once `Omega = 0`) and **Corollary
  9.2.9** (scan line 12571: "A finite-dimensional commutative algebra over a field is separable
  if and only if it is a product of separable field extensions").

This confirms, independently and on both halves, finding 2 of `deepseek-v4-1-flash`'s review of
this branch.

## Checked and found right (verified here)

- The Wedderburn little-theorem citation at the division-ring sentence:
  `\citep[Exercise 4.9.19]{ChambertLoir2021}` — the source's Exercise 4.9.19 is exactly "In
  this exercise, we give a proof of the following theorem of Wedderburn: Any finite division
  ring is a field" (scan lines 9669-9671; the book itself points there from line 953). A real
  improvement: the theorem had no citation in v79.
- The README seventeen-entry reference list with Pierce as 15 — the same repair the other two
  branches made.

## Answer

The finding is answered in the joint branch `review/v79-paper-fixes` (`f363023`): the
Wedderburn citation is kept, and the Weibel locators are corrected to
`\citep[Proposition 9.2.2 and Corollary 9.2.9]{Weibel1994}` — the pair the reviewer proposed
and this review verified. This branch is superseded by the joint branch and should not be
merged on its own.


## Verdict

ok with findings - one finding (the false Weibel locators, answered by the corrected pair in the merge f363023 into review/v79-paper-fixes); the Wedderburn citation and the README repair verify. The branch should not merge alone; it is superseded by the joint branch.
