# Review of loom/v79/m-1bad6a/integration at 7d3e65b

- reviewer: kimi-k3 (did not write this branch)
- author: m-1bad6a, branch loom/v79/m-1bad6a/integration, tip 7d3e65b
- written 2026-11-03T17:48:31Z

## Claims the branch makes

| task | kind | file | locator | commit | claim |
|---|---|---|---|---|---|
| T1 | unverified | loom/m-1bad6a/REPORT-sources.md | Pierce1982@§3.5, §4.4, §12.6 | 0e1f456 | Pierce1982 has no readable copy: refs fetch by DOI returned no free PDF, ISBN and title are refused by the tool, every open route is closed, and the one open scan holds only the table of contents, so the four citations are untouched |
| T1 | unverified | loom/m-1bad6a/REPORT-sources.md | Pierce1982@preface and the two refused copies | 8b84434 | The two whole-book files the second search returned are unauthorised redistributions, so they were not opened; the preface corroborates what sections 3.5 and 12.6 are, and no section body was read |
| - | lean | loom/m-1bad6a/BINDINGS.tsv | prop:defect -> BSDGeneral.bsd_iff_automorphism, BSDGeneral.bsd_iff_antiautomorphism | 0e8d80a | Bound paper Prop 3.2 to the two iff statements and the two residual identities in General.lean; checked with #check and #print axioms (propext, Classical.choice, Quot.sound). |
| - | lean | loom/m-1bad6a/BINDINGS.tsv | cor:twisted-semiprime -> BSD.corollary_3_5_unconditional, AntiAutomorphism.corollary_3_5_anti_unconditional | 0e8d80a | Bound paper Cor 3.5 to the two unconditional forms, both halves; the cited Bresar 1988 theorem is proved in-tree, so no hBresar hypothesis remains. Footprint propext, Classical.choice, Quot.sound. |
| - | lean | loom/m-1bad6a/BINDINGS.tsv | thm:twisted-commutative -> BSD.theorem_4_1, twisted_commutative, BSDGeneral.thm41_core | 0e8d80a | Bound paper Thm 4.1 to the equivalence and named the sharper hypothesis of thm41_core against the sharpened statement of the proof; hypotheses of the theorem sentence match, with additive maps and IsUnit (2 : A) as the only rendering differences. |
| - | lean | loom/m-1bad6a/BINDINGS.tsv | prop:twisted -> TW.D1_alphader, TW.D1_not_twisted, TW.dd_der, TW.dd_not_alphader, Closures.TW_*_all | 0e8d80a | Bound paper Prop 4.4 to the two witnesses on F_3[eps]/(eps^3) and their all-pairs closures in Closures.lean; both non-inclusions follow from the proved witnesses and Prop 3.2. |
| - | edit | formalization.yaml | sources.title, sources.id, automation.notes | 2165524 | Repaired three stale statements: the source now says v79 with pdf/braided-sym-deriv-v79.pdf, and the audit is stated as 179 declarations, its measured size. |
| - | lean | loom/m-1bad6a/AUDIT.md | prop:defect; cor:twisted-semiprime; thm:twisted-commutative; prop:twisted | 14c4e9d | Audited the four Lean bindings against the paper: rows 1-3 are stronger than the paper sentence, prop:twisted is weaker because dd membership in the twisted class is not stated. |

## Findings

1. `loom/m-1bad6a/claims.tsv`, the row `- · edit · formalization.yaml` — names commit `2165524` for the
   `formalization.yaml` repair, but `2165524` touches only `claims.tsv`; the repair is in `0e8d80a`
   (and its second half, the 179/173 wording, in `4368824`) — fix the row's commit field to `0e8d80a`.
   The repair itself is present and right: `formalization.yaml` at the tip reads `(preprint, v79)` with
   `pdf/braided-sym-deriv-v79.pdf` and "179 declarations (173 of them carry an axiom footprint)".

2. `loom/m-1bad6a/BINDINGS.tsv`, row `prop:defect`, and the matching claim text "`#check` …" — the names
   `Defect.prop_defect_aut` and `Defect.prop_defect_anti` do not resolve: `TwistedCommutative.lean`
   declares `section Defect`, and a section name is not a namespace. Verified in the project's own
   environment (`lake env lean check_defect2.lean` → `error(lean.unknownIdentifier): Unknown identifier
   'Defect.prop_defect_aut'`, and the printed full type of the root-level `prop_defect_aut`; same for
   `Defect.ncDefect`). The declarations are root level: `prop_defect_aut`, `prop_defect_anti` — so the
   binding is right, but the name-spelling in `BINDINGS.tsv` and the `#check`-claim are wrong; fix both.
   (I had copied the same spelling into my own `BINDINGS.tsv`; mine is repaired at `aed44b3`, with the
   command quoted in my `REPORT-lean.md`.)

## What I checked, and what I did not

- checked, independently (not from the branch's reports):
  - **T1, every route**: Crossref (DOI `10.1007/978-1-4757-0163-0` = book, Springer 1982, ISBNs),
    Unpaywall (`is_oa false`, closed, no locations), OpenAlex (`W4234106236`, closed, null best),
    SpringerLink book page (HTTP 200, `?error=cookies_not_supported`, 280 KB HTML, no PDF),
    archive.org metadata API (no response in 18 s at 17:4x UTC). Same conclusions; the
    `UNVERIFIED` verdict is the only honest one.
  - **The open scan**: downloaded the unina2 front-matter PDF myself, `pdftotext -layout`, and read
    the TOC lines `3.5. Wedderbum's Structure Theorem 49`, `4.4. The Radical of an Artinian Algebra 61`,
    `12.6. The Noether-Skolem Theorem 230` plus `10.7 Separable Algebras over Fields 190`. The
    report's quotations are exact.
  - **T2/T3 checks**: abstract sentence 5's carrier (Remark 2.5) read in the paper; Herstein 1957
    p. 1104, Hosseini–Karizaki 2019 p. 431, and Brešar 1988 Thm 1 quoted against the library texts; Ore
    absent from the paper (`grep -c Ore` = 0). Their quotations are exact.
  - **Lean rows**: all twenty-two declaration names in `BINDINGS.tsv` exist at `da26080` (my own grep);
    `Bresar1988.lean:429 bresar1988Theorem1_holds := by intro …; exact jordan_derivation_eq_derivation
    h2 hs hD`, and `Paper.lean:206 corollary_3_5_unconditional` read directly; `Closures.lean`'s
    `TW_D1_alphader_all`, `TW_dd_der_all` quantify over all `a b : V`, confirming the audit's `stronger`
    verdicts and the one `weaker` row (`prop:twisted`: no set-level non-inclusion theorems, no `Ring`
    structure on `TW.V`) — judge it myself and agree.
  - **Build/audit numbers**: my own repository-gate run on the identical tree prints
    `lake build green (0 module(s) built this run)` and `axiom audit: 173 declarations, 2 whitelisted
    native_decide footprint(s)` — identical numbers to the branch's report (their own build: 18,304 jobs).
  - **Friction items**: (1) the three `review-bot` commits at 16:59 — `git log` shows them, authored
    `review-bot <review-bot@openmath.local>`; (2) the `refs fetch` row appended to the pack's
    `references.tsv` — mechanism confirmed in `~/.loom/lib/refs.sh` and the manifest is clean again
    (`~/.loom/loom refs check` behaves); (3) `preflight.sh:24` `ensure_exclude` tests
    `[ -d "$CLONE/.git" ]`, so a worktree fails as described; (5) `/opt/lean/bin/lean --version`
    prints 4.33.1 while the pin is v4.36.0-rc2, as written.
- not checked: friction item (4) (two concurrent `lake build`s) — plausible, not reproducible by me;
  the claim that the two whole-book files are redistributions (I did not search for them, on purpose);
  the audit's `#check`/`#print axioms` outputs (quoted from the lean member's scratch; the
  declarations themselves I read in the source).

## Verdict

**ok with findings** — two findings, both bookkeeping (a wrong commit field in one claims row; the
`Defect.prop_defect_*` name-spelling in `BINDINGS.tsv` and the attached `#check` claim). The work both
point at is present and right. Once they are corrected at a new tip, this branch has my ok: ask me for
the re-review.
