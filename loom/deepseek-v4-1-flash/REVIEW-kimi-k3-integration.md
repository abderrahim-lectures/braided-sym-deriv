# Review of loom/v79/kimi-k3/integration at 09b1d3c

- reviewer: deepseek-v4-1-flash (did not write this branch)
- author: kimi-k3, branch loom/v79/kimi-k3/integration, tip 09b1d3c
- written 2026-11-03T17:52:58Z

## Claims the branch makes

| task | kind | file | locator | commit | claim |
|---|---|---|---|---|---|
| T1 | unverified | loom/kimi-k3/REPORT-sources.md | Pierce1982@§3.5,§4.4,§12.6 (paper lines 494, 604, 607) | 9a50a32 | No open copy of Pierce 1982 exists at Crossref, Unpaywall, OpenAlex, or the publisher; the open 11-page front-matter scan settles the section titles but no passage, so the row is UNVERIFIED and the citations are untouched. |
| - | lean | loom/kimi-k3/BINDINGS.tsv | prop:defect -> BSDGeneral.bsd_iff_* + Defect.prop_defect_* | 6f5b827 | Bound Prop 3.2 to the two iff statements and the residual identities already in the tree; existence of names checked; agrees with the independent audit verdict stronger. |
| - | lean | loom/kimi-k3/BINDINGS.tsv | cor:twisted-semiprime -> BSD.corollary_3_5_unconditional + AntiAutomorphism.corollary_3_5_anti_unconditional | 6f5b827 | Bound Cor 3.5 to the two unconditional forms; Bresar1988.bresar1988Theorem1_holds is proved in-tree, so no hBresar remains. |
| - | lean | loom/kimi-k3/BINDINGS.tsv | thm:twisted-commutative -> BSD.theorem_4_1 + twisted_commutative + BSDGeneral.thm41_core | 6f5b827 | Bound Thm 4.1 to the equivalence and the sharpened core; hypotheses match with the two rendering differences named. |
| - | lean | loom/kimi-k3/BINDINGS.tsv | prop:twisted -> TW.D1_*, TW.dd_* and Closures.TW_*_all | 6f5b827 | Bound Prop 4.4 to the two witnesses and their all-elements closures; the set-level non-inclusions as standalone theorems are named as not formalized (weaker row, agreed with the audit). |

## Findings

loom/kimi-k3/BINDINGS.tsv, row `prop:defect`, `lean_decl` field — it names `Defect.prop_defect_aut` and `Defect.prop_defect_anti`, and neither exists: `Defect` in `lean/Research/BraidedSymDeriv/TwistedCommutative.lean` is a `section` (line 228 to 272), and a section creates no namespace. What would fix it: write the two names without the prefix, `prop_defect_aut` and `prop_defect_anti`, in `BINDINGS.tsv` and in the `prop:defect` row of `claims.tsv`, which repeats them. This is the same mistake the branch's own `ISSUES.md` reports in `lean/RESULTS.md`, so fix the two together.

## Since my first review at 810fd4b

The branch moved to `09b1d3c` (`kimi-k3: paste the guard, preflight and agree outputs; STATE at delivery`).
The whole delta is `REPORT.md` (+24) and `STATE.md`, both documentation: `BINDINGS.tsv` and `claims.tsv`
are untouched, so the finding below still stands at the new tip. That is why this review is re-issued
here rather than left at the old one.

## A second review of this branch exists, and the gate cannot read it

`loom agree loom/v79/kimi-k3/integration` prints two rows: mine (`ok with findings`, at `09b1d3c`)
and one from `m-1bad6a` (`none | none | stale+open`). The second row exists because
`review/v79-paper-fixes` carries `loom/m-1bad6a/REVIEW-kimi-k3-integration.md`, which makes **the same
finding as mine** (I read it: `Defect.prop_defect_aut`, `Defect.prop_defect_anti`, `Defect.ncDefect`
do not exist; `prop_defect_aut`, `prop_defect_anti`, `ncDefect` are root level) but states its verdict as
`**Verdict: ok with findings.**` with no `## Verdict` section. The parser reads the first line after a
`## Verdict` heading, so that file counts as `verdict none` and stays open for ever.

Consequence for the author: fixing the two names makes my row `ok`, but the gate will still report
`NOT AGREED` while that other file is unparsed. The file's author needs a `tip 09b1d3c` line, a
`## Verdict` section whose first line is `ok`, and `## Findings` holding `(or: none)` once the names are
fixed. I cannot edit another model's file, so this is a note for that author and for the owner.

## What I checked, and what I did not

- checked: the five claims' commit fields against `git show --stat` — `9a50a32` carries `REPORT-sources.md`, `STATE.md`, `claims.tsv`, `new-references.tsv`; `6f5b827` carries `BINDINGS.tsv`, `REPORT-lean.md`, `ISSUES.md`, `claims.tsv`; and `c792fbf` is the commit that re-pointed the rows at their own commits, which is the finding kimi-k3 raised against my branch and I have applied on mine.
- checked: every declaration name in the other three rows exists, with `#check` in `lean/` under the project's environment — `BSD.corollary_3_5_unconditional`, `AntiAutomorphism.corollary_3_5_anti_unconditional`, `BSD.theorem_4_1`, `twisted_commutative`, `BSDGeneral.thm41_core`, the six `TW.*` witnesses and the four `Closures.TW_*_all` closures.
- checked: the branch's `ISSUES.md` line — `#check @TwistedCommutative.prop_defect_aut` fails, as it says — and its `REPORT.md` toolchain claim, v23 with ten `loom check` rows PASS, which I reproduced.
- checked: the review of `loom/v79/m-1bad6a/integration` that this branch carries is right on its one point: `2165524` touches only `claims.tsv`, and the `formalization.yaml` repair is in `0e8d80a`.
- not checked: the branch's own build numbers (18,304 jobs, 173 audited footprints, 6 without) — mine on the same tree agree, but I did not rerun theirs; and I did not search for the two whole-book redistributions the source report refuses to open, on purpose.
- note, not a finding: `new-references.tsv` adds `Pierce1982FrontMatter` for the 11-page scan, and both its entry and its `page_or_item_read` column say it is front matter only, so no reader is misled; the cited sections are still not on disk.

## Verdict

ok with findings
