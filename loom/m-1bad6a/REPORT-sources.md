# Report: braided-sym-deriv v79, agent sources-1

## 1. Summary
- Platform skills used: `loom-rules` (read first, binding rules), `loom-source-check` (read each source before relying on it, locate the passage), `loom-report` (this file and `claims.tsv`), `loom-git-delivery` (commit only in my worktree, no push), `loom-origins-intersections` (read; no origins or intersections row was asked for by T1, so no row was written).
- Tasks done: T1.
- BLOCKED: none.
- UNVERIFIED sources: Pierce1982 (see section 2c).
- Extra work: one report-only item from the orchestrator's brief (section 3: the first sources of old notions named in `verdicts.md` §4). It takes no claim row, as the brief says.
- Lean, Mathlib, TauCeti: not used by this task.

## 2. T1 [references] row 15 Pierce1982 has no file in the pack

### 2.0 The row
`~/.loom/loom refs check`, run from the project root, prints:

```
row 15 (Pierce1982): missing -
row 15 (Pierce1982): missing -
```

The paper cites the row four times, all page-free: `paper/braided-sym-deriv.tex` line 494 `\citep[\S3.5]{Pierce1982}` (a finite-dimensional reduced commutative algebra is a product of finite separable field extensions), line 604 `\citep[\S4.4]{Pierce1982}` (the radical of a finite-dimensional algebra is nilpotent), line 604 `\citep[\S3.5]{Pierce1982}` (Wedderburn: a product of matrix algebras over division rings), line 607 `\citep[\S12.6]{Pierce1982}` (every automorphism of the quaternions is inner).

### 2a. `loom refs fetch`
The tool writes into `<repo>/loom-pack/references/`, which is outside every worktree and must not be written, so I ran it in a sandbox copy of the pack table at
`.scratch/m-1bad6a/sources-1/sandbox/` (outside the worktree, git-ignored). The sandbox held a copy of `references.tsv` with row 15 in it.

| Attempt | Argument | What the tool did |
|---|---|---|
| 1 | `10.1007/978-1-4757-0163-0` (the book DOI, confirmed against Crossref, section 2b) | Resolved the DOI, then printed `metadata only for 10-1007-978-1-4757-0163-0: no free copy at` followed by the only two candidates it tried: `https://www.ams.org/tran/1986-296-02/S0002-9947-1986-0846601-5/...pdf` (a Crossref `link` field that points to an unrelated 1986 AMS paper) and `https://doi.org/10.1007/978-1-4757-0163-0` (the publisher landing page, not a PDF). It also printed `# Semantic Scholar answered 429; OpenAlex title search instead`. No PDF was written. |
| 2 | `"Pierce, R.S.: Associative Algebras. GTM 88, Springer (1982)"` | Refused: `loom refs fetch: give an arXiv id, a DOI (10.…), or an http(s) URL of a PDF` (exit 2). The tool accepts no title and no author. |
| 3 | `0-387-90693-2` (the book ISBN) | Same refusal, exit 2. |
| 4 | `978-1-4757-0163-0` (the eBook ISBN) | Same refusal, exit 2. The tool accepts no ISBN. |

### 2b. Open web, in the order tried
- Crossref, `https://api.crossref.org/works?query.bibliographic=Associative+Algebras+Pierce`: the book is `10.1007/978-1-4757-0163-0`, "Associative Algebras", Springer New York, 1982, type `book`, with 20 chapter records that carry page ranges. This gives the publisher's own chapter table and it is the evidence used in section 2c.
- Unpaywall, `https://api.unpaywall.org/v2/10.1007/978-1-4757-0163-0`: `"is_oa":false`, `"oa_status":"closed"`, `"oa_locations":[]`, `"has_repository_copy":false`.
- OpenAlex, `https://api.openalex.org/works/doi:10.1007/978-1-4757-0163-0`: work `W4234106236`, `"oa_status":"closed"`, `"best_oa_location":null`; its only locations are the doi.org landing page and a CERN record `http://cds.cern.ch/record/1614818` with `pdf_url: null`.
- archive.org, `https://archive.org/advancedsearch.php?q="associative algebras" Pierce`: `numFound 0`. Open Library (`https://openlibrary.org/search.json?q=associative+algebras+pierce`) points to the Internet Archive item `associativealgeb00pier_0`; its metadata (`https://archive.org/metadata/associativealgeb00pier_0`) gives `access-restricted-item = true` and `collection = [internetarchivebooks, printdisabled]`, so that is a lending copy and not an open one. I did not try to read it or to download its files.
- Springer, `https://link.springer.com/book/10.1007/978-1-4757-0163-0`, and the front-matter PDF path `https://link.springer.com/content/pdf/bfm:978-1-4757-0163-0/1`: both answered 200 with a JavaScript "Client Challenge" page ("A required part of this site couldn't load"). That is a bot challenge, so I stopped using the site.
- Google Books, `https://www.googleapis.com/books/v1/volumes?q=...`: HTTP 429. I stopped after the one call.
- A search for a university-hosted scan returned `https://unina2.on-line.it/sebina/repository/catalogazione/documenti/Pierce%20-%20associative%20algebras.pdf`. It is a real 11-page PDF of this book, and it is the only open copy I found. It holds the front matter and the complete table of contents (pp. i–xii), and nothing else. Downloaded to `.scratch/m-1bad6a/sources-1/pierce1982.pdf`, text extracted there with `pdftotext -layout`, and not committed (the guard would quarantine it inside the worktree).
- Titles offered by the same search at `epdf.tips`, `vdoc.pub` and `scribd.com` are pirate mirrors; I opened none of them.
- A second search returned two more whole-book files: `https://ebooks.karbust.me/Mathematics/Richard%20S.%20Pierce%20-%20Associative%20Algebras%20(1982)%20[978-1-4757-0163-0].pdf` and `http://free.downloads.tuxfamily.net/openmathdep/algebra_abstract/Associative_Algebras-RPierce.pdf`. I opened neither. Both are redistributions of the 1982 Springer book by hosts that are neither the publisher nor a preprint server nor an open repository, so they fall under the ban on pirate mirrors and the like, and the cited sections stayed unread. If the owner decides such a copy may be used, these two URLs are the ones to try.

### 2c. What I established for each locator, and what I did not
The table of contents in that front-matter scan gives the section title and the starting page of every section. Quoted from the scan:

- Chapter 3 "The Structure of Semisimple Algebras" 40: `3.3. Simple Algebras 44`, `3.4. Matrices of Homomorphisms 47`, **`3.5. Wedderbum's Structure Theorem 49`** (the OCR reads `Wedderbum` for `Wedderburn`), `3.6. Maschke's Theorem 51`. So **§3.5 is "Wedderburn's Structure Theorem", starting p. 49**, and §3.6 starts p. 51.
  - Line 604 uses §3.5 for Wedderburn's structure theorem (a product of matrix algebras over division rings). The section title names exactly that theorem, so the locator is apt at the level of the table of contents.
  - Line 494 uses §3.5 for "a finite-dimensional reduced commutative algebra is a product of finite separable field extensions". Separability is the subject of Chapter 10 "Separable Algebras" 179, whose `10.2. Separability` starts p. 181 and `10.7. Separable Algebras over Fields` starts p. 190. So that citation points at the Wedderburn section for a fact whose natural home in this book is Chapter 10. Recorded as an observation for the owner; I cannot edit the paper and I did not read either section's text.
- Chapter 4 "The Radical" 55: `4.3. The Jacobson Radical 58`, **`4.4. The Radical of an Artinian Algebra 61`**, `4.5. Artinian Algebras Are Noetherian 63`, `4.6. Nilpotent Algebras 65`. So **§4.4 is "The Radical of an Artinian Algebra", starting p. 61**, and §4.5 starts p. 63. Nilpotence of the radical of a finite-dimensional (artinian) algebra is what such a section proves, but I did not read it, so I cannot quote the theorem.
- Chapter 12 "Simple Algebras" 218: `12.4. Central Simple Algebras 224`, `12.5. The Brauer Group 227`, **`12.6. The Noether-Skolem Theorem 230`**, `12.7. The Double Centralizer Theorem 231`. So **§12.6 is "The Noether–Skolem Theorem", starting p. 230**. "Every automorphism of the quaternions is inner" is the Noether–Skolem statement for the finite-dimensional central simple algebra ℍ over ℝ, so the locator is apt at the level of the table of contents. I did not read the theorem or any corollary in it.
The Preface in the same scan (front matter) states the plan in the author's words: "This first part contains the basic structure and representation theorems for associative algebras: Wedderburn's Structure Theorem for Semisimple Algebras, Wedderburn's Principal Theorem, ...", and "Chapter 12 builds the tools that are needed to construct the edifice of central simple algebras: the Jacobson Density Theorem, the Noether-Skolem Theorem, and the Double Centralizer Theorem." Both fit the section titles above and neither quotes the statements the paper uses.

- Chapter 1 has `1.6. Quaternion Algebras 13` and `1.7. Isomorphism of Quaternion Algebras 16`, so the automorphism fact could also sit there; I did not read either section.

**Conclusion for T1: `UNVERIFIED Pierce1982`.** I read the book's front matter and table of contents and no section body, so no sentence of §§3.5, 4.4, 12.6 is quoted anywhere in this report. The four citations stay as they are, and no result is taken from this source.

Rule 8 (`Old source vN: <key>: <search done>` in `loom/<model>/STATE.md`): `STATE.md` is not in the list of files I may edit, so the line lives here instead. `Old source v79: Pierce1982: loom refs fetch by DOI/ISBN/title; Crossref, Unpaywall, OpenAlex, archive.org, Open Library, Springer, Google Books; one open front-matter scan read (TOC only), no readable copy of any cited section found.`

## 3. Report-only item (`verdicts.md` §4 first sources of old notions; no claim row)

### 3.1 Herstein1957, p. 1104
Read in `loom-pack/references/text/Jordan derivations of prime rings (1958).txt`, which is the JSTOR scan of I. N. Herstein, "Jordan Derivations of Prime Rings", Proc. Amer. Math. Soc. 8(6) (Dec. 1957), pp. 1104–1110, `Stable URL: http://www.jstor.org/stable/2032688`. The page break in the text file falls after the printed page number `1104`, so the sentences below are on p. 1104. §1, p. 1104:

- "Given any associative ring A one can construct from its operations and elements a new ring, the Jordan ring of A, by defining the product in this ring to be a o b=ab+ba for all a, bEA". (The scan’s OCR writes ∈ as `E` and the ring-product sign as `o`; I quote it as it stands.)
  The paper, line 97: "`\citet[p.~1104]{Herstein1957}` takes the sum $ab + ba$ without the half." **The passage says that.**
- "By a Jordan derivation, ', of an associative ring A we shall mean a derivation of the Jordan ring formed from A; that is, for all a, b ∈ A, (a o b)'=a' o b+a o b'."
  The paper, line 173: "`\citet[p.~1104]{Herstein1957}` defines a *Jordan derivation* as a derivation of the Jordan ring of $A$, that is by $D(x \circ y) = D(x) \circ y + x \circ D(y)$". **The passage says that.**
- "for such rings A a Jordan derivation, ', can be defined by (1) (a+b)' = a'+b', (2) (a^2)' = aa' + a'a", introduced by "for most of this paper all rings considered will be of characteristic not 2".
  The paper, line 173: "and records that for rings of characteristic different from $2$ it can be defined by the square identity $D(x^2) = D(x)x + xD(x)$". **The passage says that**, with additivity (1) stated as part of the same definition.

### 3.2 HosseiniKarizaki2019, §1
Read in `loom-pack/references/text/Functional equations characterizing σ-derivations.txt`: A. Hosseini and M. Mohammadzadeh Karizaki, "Functional equations characterizing σ-derivations", Acta Sci. Math. (Szeged) 85 (2019), 431–440, `doi: 10.14232/actasm-018-594-6`. §1 "Introduction and preliminaries", p. 431:

> "Let σ : R → R be an additive mapping. An additive mapping d : R → R is called a σ-derivation (resp. Jordan σ-derivation) if d(xy) = d(x)σ(y) + σ(x)d(y) (resp. d(x2 ) = d(x)σ(x) + σ(x)d(x)) holds for all x, y ∈ R." (the scan prints `d(x2 )` for d(x²): the superscript is lost in OCR)

The paper, line 180: "For an automorphism $\alpha$ of $A$, an *$\alpha$-derivation* satisfies $D(xy) = D(x)\alpha(y) + \alpha(x)D(y)$ `\citep[\S1]{HosseiniKarizaki2019}`." **The passage says that identity on p. 431, §1.** Two differences to note: the source's σ is an additive monomorphism with σ(e) = e (abstract, p. 431), and an automorphism is a special case of that, so the paper's α is a specialization; and the source names the notion σ-derivation, while the paper names it α-derivation.

### 3.3 Ore 1933
`paper/braided-sym-deriv.tex` contains no occurrence of `Ore` (grep over the whole file), and `The Annals of Mathematics` has no file in `loom-pack/references/`. One search, as the brief asked, and no more: Crossref `https://api.crossref.org/works?query.bibliographic=Ore+Theory+of+non-commutative+polynomials` returns `10.2307/1968173`, O. Ore, "Theory of Non-Commutative Polynomials", The Annals of Mathematics 34, p. 480, issued 1933-07. That matches the entry in `verdicts.md` §4 ("Ore 1933, Annals of Math. 34, pp. 481-482, rules (4)-(5)"). I read nothing of it and do not rely on it.

## 4. Sources opened
| Key | Opened where | What I found | Read fully? |
|---|---|---|---|
| Pierce1982 | `.scratch/m-1bad6a/sources-1/pierce1982.pdf` from `https://unina2.on-line.it/sebina/repository/catalogazione/documenti/Pierce%20-%20associative%20algebras.pdf` | Front matter and table of contents, pp. i–xii, with every section title and starting page | No: 11 pages of 436; no section body |
| Pierce1982 (metadata) | Crossref, Unpaywall, OpenAlex, archive.org, Open Library, Springer | Closed access; no repository copy; one lending-only Internet Archive scan | n/a |
| Herstein1957 | `loom-pack/references/text/Jordan derivations of prime rings (1958).txt` | p. 1104 of Proc. AMS 8(6), 1957: Jordan ring product ab+ba, the definition of a Jordan derivation, the characteristic-not-2 form | Yes, the §1 passages quoted above |
| HosseiniKarizaki2019 | `loom-pack/references/text/Functional equations characterizing σ-derivations.txt` | p. 431, §1: the σ-derivation identity quoted above | Yes, the §1 definitions paragraph |
| Ore1933 | Crossref only | Bibliographic record only | No |

## 5. Files changed
- `loom/m-1bad6a/REPORT-sources.md` (this file)
- `loom/m-1bad6a/claims.tsv` (one row for T1)

## 6. Friction
- `loom refs fetch` writes into the pack directory, so it had to be run on a sandbox copy of `references.tsv`; its DOI attempt also wasted one candidate on a Crossref `link` field that points at an unrelated 1986 AMS paper.
- Springer answers with a JavaScript challenge, Google Books with 429, and Semantic Scholar with 429, so three of the routes the brief names could not be used at all.
- The one open copy is a scan of the front matter only, so the cited sections themselves stayed out of reach.

## 7. Doubts
- §3.5 at line 494: the table of contents puts separability in Chapter 10, so the citation looks misplaced for that sentence. I did not read §3.5, so I do not assert that it fails to contain the statement in some form.
- Whether §4.4 states nilpotence of the radical as a proposition, a theorem or a corollary, and with which number: unread.
- Whether §12.6 states the quaternion corollary, and on which page: unread.
- No PASS is claimed anywhere in this report.
