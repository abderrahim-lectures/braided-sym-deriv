# Review of branch `review/v80-citations` at 69ab980 — CORRECTED

- reviewer: `deepseek-v4-1-flash` (did not write this branch)
- verdict: **ok** — this review replaces my earlier one on the same branch, which made a finding that
  was **wrong**. The file is kept at the same path so the record shows both.

## What I got wrong, and why

My first review said the added citation `\citep[Lemma 9.2.1 and Theorem 9.2.11]{Weibel1994}` at line
494 did not carry the sentence "a separable extension has no nonzero `K`-derivation", because I could
not read Theorem 9.2.11 in `loom-pack/references/text/weibel-homological-algebra.txt` — the page is
missing from that OCR — and because Lemma 9.2.1 alone is `H¹(R,M) = Der_k(R,M)/PDer_k(R,M)`.

The pack carries a transcribed excerpt of the theorem, which I had not read:
`loom-pack/references/excerpts/Weibel1994_Theorem_9_2_11.txt`:

> Theorem 9.2.11 Let R be an algebra over a field k. The following are equivalent:
> 1. R is a finite-dimensional separable k-algebra. … 3. H_*(R,M) = 0 for all * ≠ 0 and all
> bimodules M. 4. **H^*(R,M) = 0 for all * ≠ 0 and all bimodules M.** (p. 310, from the scan)

With item 4 and Lemma 9.2.1 the claim follows in two steps: a finite separable field extension `L/K`
is a finite-dimensional separable `K`-algebra (Lemma 9.2.8 equates the two definitions), so
`H¹(L, L) = 0`; and `H¹(L,L) = Der_K(L)/PDer_K(L)` with `PDer = 0` because `L` is commutative, so
`Der_K(L) = 0`. **The branch's citation was right, and my finding was a false one.** I should have read
`references/excerpts/` before the raw scan: the excerpts are transcriptions checked against the image.

## Findings

(or: none)

## What I checked

- `\citep[Exercise 4.9.19]{ChambertLoir2021}` at line 601 — right: "we give a proof of the following
  theorem of Wedderburn: Any finite division ring is a field" (`Chambert-Loir` text, lines 9669–9670).
- `\citep[Lemma 9.2.1 and Theorem 9.2.11]{Weibel1994}` at line 494 — right, by the excerpt and the two
  steps above.
- the README change (the numbered list matching the seventeen-entry bibliography) — right.
- the release: 13 pages, page 1 prints `Preprint version 80`. I did not rebuild it.

## Consequence for the joint branch

`review/v79-paper-fixes` at `04c3eed` **acted on my wrong finding** and replaced that locator with
`\citep[Proposition 9.2.2 and Corollary 9.2.9]{Weibel1994}`. That pair is not false — Proposition 9.2.2
gives `H¹ ≅ M ⊗_R Ω` and Corollary 9.2.9 gives the product-of-separable-extensions form — but it is
**weaker and indirect**: the direct vanishing is Theorem 9.2.11(4). My review of that branch asks for
the locator to be restored; the error is mine, not its author's.
