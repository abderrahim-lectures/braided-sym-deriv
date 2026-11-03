# REPORT-sources — model kimi-k3, pack braided-sym-deriv v79

Sources agent: this session itself (no sub-agents were started; the pack has one task).

## T1 [references] sources missing from the library — Pierce1982

The row as `~/.loom/loom refs check` prints it (run 2026-11-03 in the project root, toolchain v23):

```
row 15 (Pierce1982): missing -
row 15 (Pierce1982): missing -
```

The four places the paper cites it (`paper/braided-sym-deriv.tex`):

| line | locator | the fact the paper takes from it |
|---|---|---|
| 494 | `\citep[\S3.5]{Pierce1982}` | a finite-dimensional reduced commutative algebra is a product of finite separable field extensions of K |
| 604 | `\citep[\S4.4]{Pierce1982}` | the radical of a finite-dimensional algebra is nilpotent |
| 604 | `\citep[\S3.5]{Pierce1982}` | Wedderburn: a semisimple algebra is a product of matrix algebras over division rings |
| 607 | `\citep[\S12.6]{Pierce1982}` | every automorphism of the quaternions is inner (Noether–Skolem) |

### What this run tried, each with its answer

| Route | Command / place | Answer |
|---|---|---|
| Crossref | `curl https://api.crossref.org/works/10.1007/978-1-4757-0163-0` | `book · Associative Algebras · Springer New York · 1982 · ISBN 9781475701654, 9781475701630` — DOI and book confirmed |
| Unpaywall | `curl https://api.unpaywall.org/v2/10.1007/…?email=…` | `is_oa: false, oa_status: closed`, no locations |
| OpenAlex | `curl https://api.openalex.org/works/doi:…` | work `W4234106236`, `oa_status: closed`, `best_oa_location: null` |
| archive.org | `curl -m 18 https://archive.org/metadata/associativealgeb00pier_0` | **no response within 18 s (0 bytes)**, one attempt; m-1bad6a's run records the item as `access-restricted-item` (a lending copy, not an open one) — theirs, not re-established here |
| Publisher (SpringerLink book page) | `curl -m 18 https://link.springer.com/book/10.1007/978-1-4757-0163-0` | HTTP 200, 280 KB HTML, URL rewritten to `?error=cookies_not_supported`; no PDF is served (bot/cookie wall). Not used further |

I deliberately did **not** run `loom refs fetch <doi>`: with the key `Pierce1982` already in `references.tsv`, a `--key Pierce1982` run is refused, and a keyless run appends a `metadata only` row to the pack's `loom-pack/references/references.tsv` — the pack is read-only for me, and that edit broke `manifest.sha256` for another model's preflight earlier today (their fix: restore from the pack zip, `sha256sum -c` ok; I checked the manifest is clean again: `~/.loom/loom refs check` behaves as quoted). The fetch routine's candidates for a book DOI are exactly Crossref → Unpaywall → OpenAlex → Semantic Scholar → publisher, the sources I queried directly.

### The one open copy, and exactly what it settles

A university repository hosts an 11-page scan of the book's **front matter**:

```
https://unina2.on-line.it/sebina/repository/catalogazione/documenti/Pierce - associative algebras.pdf
```

`pdfinfo`: `Adobe Acrobat 9.4 Paper Capture Plug-in`, created 2012-04-30; OCR quality. I downloaded it to `.scratch/kimi-k3/sources-1/pierce-frontmatter.pdf` (tools' rules: never committed), ran `pdftotext -layout`, and read the table of contents and preface myself. The lines, from my own `grep` of the text layer:

```
3.5. Wedderbum's Structure Theorem                         49
4.4. The Radical of an Artinian Algebra                    61
12.6. The Noether-Skolem Theorem                         230
10.  Separable Algebras                                179
10.7. Separab1e A1gebras over Fie1ds                   190
```

The Preface says in the author's words that the first part contains "Wedderburn's Structure Theorem for Semisimple Algebras" and Chapter 12 builds "the Jacobson Density Theorem, the Noether-Skolem Theorem, and the Double Centralizer Theorem".

So all three cited sections are **titled** what the paper uses them for (§3.5 Wedderburn's structure theorem, p. 49; §4.4 the radical of an Artinian algebra, p. 61 — where the nilpotence of the radical lives; §12.6 Noether–Skolem, p. 230), and the preface corroborates. That is a table of contents plus a preface: **no sentence of any cited passage was read**. Therefore:

- **`UNVERIFIED Pierce1982`** — the four citations are left exactly as they are; nothing in the paper rests on a passage this run read.

### Two copies deliberately not opened

m-1bad6a's run records finding two whole-book redistributions and leaving them alone, because the rule admits copies only from open repositories, preprint servers and the publisher's own open access. I agree with the call and did not search for them.

### Note for the owner (PROPOSE, no edit)

Line 494's Pierce locator `§3.5` covers the product claim; its separable half fits `§10.7 Separable Algebras over Fields` (p. 190 of the same scan's table of contents) better. The unread section rules it out as an edit today. Independently, a review of v79 completed in this session added a *verifiable* citation for the sentence's other half ("a separable extension has no nonzero K-derivation") to Weibel's Lemma 9.2.1 and Theorem 9.2.11 — branch `review/v80-citations`, PR #9 — so what the unread Pierce locator must carry is reduced.

## Checks that are not claim rows (the run brief named T2 and T3; the pack's TASKS.md carries T1 only, and `claim.sh` refuses rows outside TASKS.md)

### T2 — abstract sentence 5

Sentence (verbatim): "The negative of the identity gives all linear endomorphisms, and the negative of the swap gives the Lie derivations." Carrier: Remark 2.5, `rem:sigma-derivation-classification` (`paper/braided-sym-deriv.tex`, lines 225–258): the products are `x ·_{-id} y = xy − xy = 0` and `x ·_{-τ} y = xy − yx = [x, y]`; hence `BSDer_{-id}(A) = End_K(A)` (every linear map is a derivation of the zero product) and `BSDer_{-τ}(A)` is the Lie derivations (Martindale 1964, p. 183 — read in the library, verbatim). Lean counterparts present in the tree: `BSDGeneral.bsd_neg_id_all`, `bsd_neg_tau_is_lie` (existence checked by grep through `lean/Research/BraidedSymDeriv/General.lean`). **No edit needed.**

### T3 — the origins' first sources

Read in the library, at the paper's locators:

- **Herstein 1957, p. 1104** (`references/text/Jordan derivations of prime rings (1958).txt`): "By a Jordan derivation, ', of an associative ring A we shall mean a derivation of the Jordan ring formed from A; that is, for all a, b …, (a o b)'=a' o b+a o b' … (ab+ba)'=a'b+ab'+b'a+ba'". This is what the paper's lines 97 and 173 attribute to `p.~1104`, and THEOREM 3.1 of the same paper is on record verbatim.
- **Hosseini–Karizaki 2019, §1, p. 431** (`references/text/Functional equations characterizing σ-derivations.txt`): "An additive mapping d : R → R is called a σ-derivation (resp. Jordan σ-derivation) if d(xy) = d(x)σ(y) + σ(x)d(y) (resp. d(x²) = d(x)σ(x) + σ(x)d(x))". This is what the paper's α-derivation line cites as `\S1`.
- **Ore 1933**: the paper never mentions Ore (`grep -c Ore paper/braided-sym-deriv.tex` → 0), and no file exists; nothing rests on it.

**No edit needed for T3.**

## Old-source line (rule 8)

See `loom/kimi-k3/STATE.md`: Pierce 1982 is the one pre-1990 source this run worked around.
