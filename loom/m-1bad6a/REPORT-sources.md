# Report: braided-sym-deriv v79, agent sources-a (m-1bad6a)

## 1. Summary
- Platform skills used: loom-source-check (citation verification attempt)
- Tasks done: T1 checked
- BLOCKED: none
- UNVERIFIED sources: Pierce1982
- Extra work: none
- Lean n/a, Mathlib n/a, TauCeti n/a

## 2. Tasks
### T1 [references] Pierce1982 missing from library
- Row: N=15, Key Pierce1982, cited as \citep[\S3.5]{Pierce1982} (lines 494, 604), \citep[\S4.4]{Pierce1982} (line 604), \citep[\S12.6]{Pierce1982} (line 607)
- Action: Attempted to locate open copy; none found. Left citation as is, marked UNVERIFIED.
- Source: Pierce1982, Graduate Texts in Mathematics 88, Springer (1982) — book, DOI 10.1007/978-1-4757-0163-0, not openly accessible. Searched open repositories, preprint servers, publisher open access, Archive.org, OpenLibrary.
- Commands: checks of crossref/unpaywall/openalex/semantic scholar/publisher/arXiv by title (via loom refs fetch with DOI and archive.org URL) returned no open PDF; link.springer.com redirects to paywall; archive.org/details/associativealgebr0000pier returns 404; openlibrary search returns 0 hits. Preflight PASS.
- Commit: (to be filled, see claims.tsv)

UNVERIFIED Pierce1982

## 3. Lean
n/a

## 4. Sources opened
| Key | Opened where | What I found | Read fully? |
|---|---|---|---|
| Pierce1982 | open web, publisher, archive.org, openlibrary | Book GTM 88 is paywalled; no open PDF in references/pdfs, no text in references/text, no excerpt in references/excerpts. Springer link redirects to idp.springer.com authorize. Archive.org has no scanned copy at associativealgebr0000pier. OpenLibrary search returns 0. | No — UNVERIFIED |

## 5. Files changed
None (citation left as is per instructions).

## 6. Friction
- Pierce1982 is a textbook (GTM), not an arXiv/DOI paper. loom refs fetch expects arXiv id, DOI, or PDF URL; the DOI 10.1007/978-1-4757-0163-0 resolves to paywalled Springer page. No open copy available through allowed sources (open repositories, preprint servers, publisher open access). The task's instruction explicitly allows UNVERIFIED in this case.
- The pack's references/pdfs contains 16 of 17 entries; Pierce1982 is the only missing, as expected.

## 7. Doubts
- Cannot verify the four locators: \S3.5 (finite-dimensional reduced commutative = product of finite separable extensions), \S4.4 (radical nilpotent), \S3.5 (Wedderburn structure), \S12.6 (automorphisms of H inner). These are standard facts; alternative open sources could be cited but no task asks to replace the citation.
