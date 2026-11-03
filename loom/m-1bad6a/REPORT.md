# Report: braided-sym-deriv v79, model m-1bad6a

## 1. Summary
- Platform skills used: loom-source-check (attempted to fetch Pierce1982 from open sources), loom-orchestrate (coordinated), loom-report (report/claims)
- Tasks done: T1 checked
- BLOCKED: none
- UNVERIFIED sources: Pierce1982
- Extra work: none
- Lean n/a (no Lean task in this pack), Mathlib n/a, TauCeti n/a

## 2. Tasks
### T1 [references] sources missing from the library — Pierce1982
- Row: bibliography N=15, Pierce1982, cited at line 494 §3.5, line 604 §4.4, line 604 §3.5, line 607 §12.6. Fix instruction: find open copy and read passage; if cannot read, write UNVERIFIED and leave citation.
- Before: citations as above in paper/braided-sym-deriv.tex (unchanged)
- After: no edit (per instructions when UNVERIFIED)
- Source: Pierce, R.S.: Associative Algebras. GTM 88, Springer (1982). DOI 10.1007/978-1-4757-0163-0. Searched Crossref/Unpaywall/OpenAlex/Semantic Scholar/publisher/arXiv by title, publisher open access, archive.org, OpenLibrary — no open PDF.
- Commands: ~/.loom/loom refs fetch 10.1007/978-1-4757-0163-0 (paywall), ~/.loom/loom refs fetch archive.org URL (404), web fetches to springer.com (303 to idp), openlibrary search (0 hits), loom-pack/references check (confirms 16/17 in library, Pierce missing). Preflight: PASS (all essential checks), build from pack PASS.
- Commit: see claims.tsv

UNVERIFIED Pierce1982

## 3. Lean
No Lean task in v79 pack (lean/LEAN-TASK.md empty or n/a). 0 declarations.

## 4. Sources opened
| Key | Opened where | What I found | Read fully? |
|---|---|---|---|
| Pierce1982 | Crossref/Unpaywall/OpenAlex/Semantic Scholar/publisher via loom refs fetch; link.springer.com; archive.org/details/associativealgebr0000pier; openlibrary.org/search.json | GTM 88 book, not an article. DOI resolves to paywalled Springer. No open PDF in loom-pack/references/pdfs, no text, no excerpts. Archive.org ID returns 404. OpenLibrary 0 hits. | No — UNVERIFIED |

## 5. Files changed
(none beyond loom/m-1bad6a/REPORT*.md and claims.tsv; git diff main...HEAD shows only loom/ files)

## 6. Friction
- Instruction in loom-pack/TASKS.md says copies come only from open repositories, preprint servers, publisher open access; never from pirate mirror. Pierce1982 is a commercial textbook with no open copy; this is expected and the UNVERIFIED path is the honest outcome.
- loom refs fetch only accepts arXiv id, DOI, or PDF URL; for a book DOI it correctly reports paywall.
- Preflight's only FAIL is uvx not installed, with fallback to python3 -m venv (toolchain v12 expected).

## 7. Doubts
- The four locators (§3.5, §4.4, §3.5, §12.6) are plausible standard algebra facts but unverified here. Previous memory records note 15 empty slots in v75 refs zip and no archive.org scan — consistent.
