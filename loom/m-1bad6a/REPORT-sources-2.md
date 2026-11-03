# REPORT — sources, second independent pass (fresh worktree sources-2)

Agent: m-1bad6a, worktree `.loom/m-1bad6a/sources-2`, branch `loom/v79/m-1bad6a/sources-2`.
This is the second, independent pass over the same tasks, run at the owner's request with the
caveat that it re-derives answers already on the record. Every route below was run fresh by
this pass; nothing is copied from the earlier reports (PR #7, PR #13, PR #11's audit).

## T1 [references] Pierce 1982 — UNVERIFIED, fourth independent route table

`~/.loom/loom refs check`: `row 15 (Pierce1982): missing -` twice (pdf and text).

| Route, run by this pass | Answer |
|---|---|
| `loom refs fetch 10.1007/978-1-4757-0163-0` (21:14 UTC) | "metadata only ... no free copy"; Semantic Scholar answered 429; the two candidates it tried are the DOI landing page and an AMS Transactions PDF that is an unrelated 1986 paper (the Crossref `link` field of this book is wrong — the third run to observe this) |
| Unpaywall `api.unpaywall.org/v2/10.1007/978-1-4757-0163-0` (21:15:46 UTC) | `is_oa: false`, `oa_status: "closed"`, `best_oa_location: null`, `oa_locations: []`, `has_repository_copy: false` |
| OpenAlex `api.openalex.org/works/doi:...` (21:15:47 UTC) | W4234106236, `is_oa: false`, `oa_status: "closed"`, `any_repository_has_fulltext: false`, `pdf_url: null` |
| **New this pass**: OpenAlex lists a second location, `pmh:oai:cds.cern.ch:1614818` (CERN Document Server) | the record page answers an anti-bot proof-of-work challenge to automated clients, so the site was not used further; OpenAlex's own metadata for that location says `is_oa: false`, `pdf_url: null`, a "submittedVersion" that is neither published nor accepted — no open copy |
| archive.org item `associativealgeb00pier_0` (metadata API, 21:16 UTC) | `access-restricted-item: true`, collection `printdisabled`; every derivative (PDF, EPUB, DjVu, hOCR) is `"private": true`; the only borrowable forms are ACS/LCP-encrypted lending PDFs — a controlled loan, not an open copy. (An `advancedsearch.php` query returns 0 hits: the item is `noindex`'d and not text-searchable; the metadata API works by identifier.) |
| SpringerLink (the publisher's own page, via a search result) | "This is a preview of subscription content, log in via an institution to check access"; only the Front Matter chapter (i–xii) is freely downloadable |
| Web search (exa) | three whole-book copies on document-sharing sites — scribd.com/document/368794892, vdoc.pub (`p03n5ab6t0s0`), epdf.tips — all refused as unauthorised redistributions; and the one open copy: the 11-page front-matter scan at `unina2.on-line.it`, downloaded and read by this pass |

**The open scan, read by this pass** (`.scratch/m-1bad6a/sources-2/pierce-frontmatter.pdf`, 11
pages): the table of contents prints, with the OCR's errors kept,

```
3.5. Wedderbum's Structure Theorem                         49
4.4. The Radical of an Artinian Algebra                    61
10.7. Separab1e A1gebras over Fie1ds                       190
12.6. The Noether-Skolem Theorem                           230
```

(the OCR reads `Wedderbum` for Wedderburn, `1` for `i`.) All four section titles fit the uses
the paper makes of them — §3.5 = Wedderburn's structure theorem, §4.4 = the radical of an
artinian algebra, §12.6 = Noether–Skolem — and §10.7 corroborates the earlier runs' note that
"separable" is Chapter 10 material. That is a table of contents; no sentence of §§3.5, 4.4 or
12.6 was read, so **`UNVERIFIED Pierce1982`** stands and the four citations are untouched.

## T3 [origins] the first sources — verified with fresh quotations

- **Herstein 1957, p. 1104** (pack library, read this pass): "By a Jordan derivation, ', of an
  associative ring A we shall mean a derivation of the Jordan ring formed from A; that is, for
  all a, b ∈ A, (a∘b)' = a'∘b + a∘b'." And the characteristic-not-2 form: "(1) (a+b)' = a'+b',
  (2) (a²)' = aa' + a'a". Both exactly as the paper's lines 97 and 173 quote them.
- **Hosseini–Karizaki 2019, §1, p. 431** (pack library, read this pass): "Let σ : R → R be an
  additive mapping. An additive mapping d : R → R is called a σ-derivation (resp. Jordan
  σ-derivation) if d(xy) = d(x)σ(y) + σ(x)d(y) (resp. d(x²) = d(x)σ(x) + σ(x)d(x)) holds for
  all x, y ∈ R." Exactly the identity the paper's line 180 cites §1 for. The source's σ is an
  additive mapping (a monomorphism in its theorems); the paper specialises to automorphisms —
  its setting, not a claim about the source.
- **Ore 1933**: `rg -c "Ore" paper/braided-sym-deriv.tex` = 0 and `rg -c "1933"` = 0 — the
  paper never cites Ore; nothing rests on it.

## Friction (this pass)

1. `loom refs fetch` still appends a row to the pack's read-only `references/references.tsv`
   (v23; the same bug the morning run filed). The manifest file itself was unchanged, but the
   tsv gained a row; this pass restored the tsv from the pack zip and verified
   `diff` → identical. The bug persists.
2. The brief's step-0 id mechanism (`loom whoami`) does not exist in v23 (it prints the usage
   text, exit 2); the worktrees for this pass were created with the explicit id
   `m-1bad6a` (this session's id in `.loom/sessions.tsv`).
3. The `loom status` at the project root reports the model of whichever session wrote
   `.loom/sessions.tsv` last (currently kimi-k3's session); the file holds both mappings and
   neither is wrong — a fresh run must name its id explicitly.
