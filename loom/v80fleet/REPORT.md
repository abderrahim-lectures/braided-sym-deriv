# REPORT — model v80fleet, full-width review of v81

Run of 2026-11-04, requested as "review again and load loom skills".

## 1. Summary

**Platform and pack skills used.** `loom-rules` (the binding rules; §19 governs the width of a review),
`loom-review-fleet` (the sixteen perspectives), `loom-orchestrate` (the swarm instead of sixteen worktrees),
`loom-health` (session start and brief), `loom-report` (this file), `loom-git-delivery` (the branches),
`loom-guard` (loaded, deliberately not armed — see §6). Repository skills used by the review itself:
`paper-lean-sync-review` and `bsd-exact-algebra` (loaded in the earlier pass this session and reused for
the judge's own recomputation).

**Artifact reviewed.** Branch `fix/v81-paper-fixes`, tip `338c593`, `\paperversion` 81, 699 lines, released
`pdf/braided-sym-deriv-v81.pdf`. Baseline `main` @ `6919724` (v80).

**Method.** One Ultramath swarm, `smw1yoi3w`, sixteen members, one perspective each, as `loom fleet
--runbook fix/v81-paper-fixes` prescribes. Members registered their perspective as their direction (the
board refuses duplicates), wrote one file each to `.scratch/review/v81/<perspective>.md`, and were barred
from reading `results/review-*` or another member's file before writing their own findings. The judge
re-derived every accepted finding from the source before accepting it, and rejected one submission
(p15, first pass) and corrected two others (p5's F2, p2's F1) rather than passing them on.

**Outcome.** Fifteen accepted, one abandoned for budget, **0 CRITICAL findings**. The joined table is
`loom/v80fleet/REVIEW-paper-v81.md` (52 deduplicated rows, R-01…R-54).

**BLOCKED.** None. **UNVERIFIED.** p6 (citations) ended without a report; that lane is covered by the
judge's own citation pass this session — sixteen sources read at every cited place and Pierce 1982 read
from the owner's scan — and by p15's second pass.

**Versions.** Lean `v4.36.0-rc2`, Mathlib `bf20166d` (both exercised by p13: 42/42 modules elaborate,
214 footprints, all inside `{propext, Classical.choice, Quot.sound}`).

## 2. Per perspective

Each row: the perspective, its verdict, its accepted findings, and the file it wrote. Details, quotes and
locators are in `REVIEW-paper-v81.md`; the member files are in `.scratch/review/v81/`.

| p | verdict | accepted findings |
|---|---|---|
| p1 statement-truth | ok | none — sixteen results re-derived and recomputed; three earlier "defects" cleared |
| p2 proofs | ok | R-36, R-37, R-38 |
| p3 compute | ok | R-50, R-51, R-52 |
| p4 paper-lean | ok | R-08 … R-15 |
| p5 lean-audit | ok | R-16 … R-19 (F2 corrected by the judge) |
| p6 citations | abandoned | — |
| p7 abstract-intro | ok | R-30, R-31, R-32 |
| p8 definitions | ok | R-44 … R-49 |
| p9 edge-cases | ok | R-33, R-34, R-35 |
| p10 examples | ok | R-53, R-54 |
| p11 remarks | ok | R-24, R-25, R-26 |
| p12 release | ok | R-01 … R-07 |
| p13 open-backlog | ok | R-39, R-40 (working tree only — see the caveat there) |
| p14 open-lean | ok | R-41, R-42, R-43 |
| p15 open-sources | ok | R-27, R-28, R-29; four own findings withdrawn on the second pass |
| p16 open-sweep | ok | R-20, R-21, R-22, R-23 |

## 3. Files changed

None. This run reviewed; it did not edit `paper/`, `lean/` or `tools/`. The only files it created are
`loom/v80fleet/STATE.md`, `loom/v80fleet/REVIEW-paper-v81.md` and this report, plus the members' files under
`.scratch/review/v81/`.

The fixes the review recommends are **not applied**: the sixteen verdicts are at tip `338c593`, and a new
commit would make all of them stale under rule 17. The fix list is §4; applying it is one commit plus a
delta re-check of the changed lines.

## 4. The fix list, in the order I would do it

**Gate (do first — it is what let the other record defects through).**
1. `tools/papercheck.py`: compare `$jobname` with `braided-sym-deriv-v<paperversion>` (R-04).
2. `tools/papercheck.py:208–210`: add `\badmit\b` and indented `axiom` to the trust scan (R-16).
3. `lean/check_axioms.lean`: add a coverage anchor — a list of the declarations the ledger cites, with a
   refusal when the printed count is below it (R-17, R-18).

**Record.**
4. Three pins to v81: `lean/BACKGROUND.md:3`, `Paper.lean:2`, `Remark46.lean:5` (R-01–R-03).
5. `lean/RESULTS.md`: resolve the quaternion-transport contradiction with the backlog (R-39), after deciding
   which tree is authoritative — the modules are untracked at HEAD.
6. `FORMALIZATION_BACKLOG.md` B3/B5: bodies to match their "done" status (R-40).
7. README: the v81 entry says "no theorem, hypothesis, proof or example changes", which N5/N7/N10 contradict
   (R-05); the `pdf/` row says "the PDF of the latest release" while it holds one per version (R-06).
   `.gitignore`: `paper/build.log` (R-07).

**Paper, one-line each.**
8. R-20 line 393: "later" → "the splitting `A = A_+ ⊕ A_-` of Section 2" (defect in my own repair).
9. R-49 line 154: "in characteristic 2" appears twice (also mine).
10. R-21/R-31 line 151: "the questions below" → "the problems below" (no question is posed).
11. R-44: label the `·_σ` display (tex 111–113) and repoint line 307, which says "as in Section 2" and points
    into the Introduction.
12. R-24 line 270: add the step — for `c = 1+λ ≠ 0` the Leibniz rule is the Jordan rule scaled by a unit, so the
    class is `JDer`; for `c = 0` every map qualifies.
13. R-33 line 443 and abstract line 69: say `char K ≠ 2`, since 2-torsion-freeness is not a condition on `A`.
14. R-30 line 154: the gloss "those that use nothing of `A` beyond its `K`-vector space" does not pick out four
    maps in characteristic 2.
15. R-54 line 271: "on the basis pairs", not "on the two basis elements" (three sightings).
16. R-36 line 527: say why the `e`-pairs may be checked, since `e = p + q` is not a basis element.
17. R-37 lines 483, 488: "both entries lie in `A_-`", not "the pairs lie in `A_-`".
18. R-45: `μ` as a scalar in `λ² + μ² = 1` collides with the multiplication.
19. R-47: `\bar u`, the quaternion norm, `semisimple` and `radical` are used undefined.
20. R-34, R-35: "unital" is decorative in Theorem 4.1 and Proposition 3.2; `A_+ = A_-` in characteristic 2 is
    unstated.

**Not recommended for a fix.** R-25 (Remark 2.2 states a distinction without stating the other definition) —
the fix is to quote a definition from Huru or Różański, which is content I have not read and rule 14's
neighbour, so it belongs to the author's decision, not to this list.

## 5. Friction

* Two members' numbering slips (the paper has Proposition 3.2, Proposition 4.4, Remark 4.6 — one wrote
  "Cor 3.2", "Prop 3.4", "Rem 4.7"). Harmless, corrected in the verdicts.
* p15's first pass searched the open web and skipped `loom-pack/references/`, and filed four findings that the
  on-disk archive refutes. The task text I gave it said "the open-access chain only", so the first pass was
  following its brief; the fault was in the brief, and the second pass fixed it. Worth changing in the
  perspective list: "open sources — the on-disk archive first, then the open-access chain".
* p6 (citations) ran out of budget with no report. The lane is the one where a reviewer must read books, and
  sixteen lanes at 90 steps is not enough for it. Either give that lane two members or a longer budget.
* `paper/build.log` exists in the v81 worktree because I redirected a `latexmk` run; `paper/build/` is ignored
  and the log beside it is not.

## 6. Why the guard was not armed

`loom-guard` points the watcher at `<repo>/.loom/<model>/orch` and starts it on worktrees, and it says the
project root stays on `main` and is never edited by it. This run wrote only under `.scratch/` and
`loom/v80fleet/`, and the project root carries two other sessions' uncommitted work; arming a watcher that
takes a baseline over that tree would have quarantined changes that are not mine. The owner can ask for it to
be armed for a run that edits `paper/`.

## 7. Doubts

* The sixteen verdicts are against `338c593`. Any commit applying §4 makes them stale by rule 17; the changed
  lines would need a delta re-check, and I have not done that.
* R-39 and R-40 are true of the working tree, which carries another session's uncommitted Lean work; they may
  not be true of any committed branch.
* p6's lane is the one place where "no finding" means "no reviewer", not "nothing wrong": the citations were
  covered by my own pass and by p15, not by a dedicated member.

## 8. Addendum — the fix list was applied after all (owner's instruction, 2026-11-04)

Branch `fix/v82-paper-fixes` (renamed from `fix/v81-paper-fixes`), commits `f3a8002` (v81),
`338c593` (.djvu ignore) and `03226ca` (v82).

**Applied — gate.** `tools/papercheck.py` now refuses a `$jobname` that disagrees with
`\paperversion` (R-04) and its trust scan matches `admit` and an indented `axiom` (R-16).
Mutation-tested, not merely asserted: with the jobname set back to v81 the gate prints
`FAIL latexmkrc jobname 'braided-sym-deriv-v81' does not match \paperversion 82` and `GATE: FAIL`;
the scan, unit-tested on a mixed probe through the tool's own `strip_lean_comments`, fires on
`:= by admit` and `private axiom` and does not fire on a comment, a docstring, `axiomFoo` or `decide`.
The end-to-end trust-scan path lives in the Lean leg, which I did not run in the worktree (no
`.lake` there, and building Mathlib would have taken the box); the predicate is tested, the leg is not.

**Applied — paper, thirteen lines.** R-21, R-30, R-49, R-44 (the product is now `eq:sigma-product`
and line 307 points at it), R-24, R-35, R-54, R-33 (with the abstract), R-36, R-37, R-34.

**Applied — record.** R-01–R-03 (three pins to v82), R-06, R-07.

**Not applied, with reasons.** R-25 — the fix is to quote a definition from Huru or Różański, which is
the author's content decision and a source I have not read. R-45 — renaming the scalar `μ` would break
the paper's notation (loom-rules 5). R-17 and R-18 — the `check_axioms.lean` coverage anchor needs Lean
work in a tree that carries another session's uncommitted modules. R-39 and R-40 — the `RESULTS.md`
versus backlog contradiction cannot be resolved while the quaternion modules are untracked at HEAD;
the authority is undecided.

**Release.** `\paperversion` 82, `latexmkrc`, `formalization.yaml`, README changelog, `pdf/braided-sym-deriv-v82.pdf`.
14 pages (the additions run past the previous last page), 0 overfull, 0 underfull, 0 undefined, 0 Type 3
fonts; `tools/papercheck.py --skip-lean` → **GATE PASS** at the committed tip (fresh 14 pp vs released
14 pp, text identical, label ok).

**Staleness, stated plainly.** The sixteen verdicts are against `338c593`. The v82 commit changes lines
these reviewers examined, so under rule 17 those verdicts do not vouch for the new tip. The changed lines
were re-built and re-gated, and the two gate fixes were mutation-tested, but no reviewer has read v82.

### Branch reorganisation (after the fixes were applied)

The owner asked for the unrelated work to come off the paper branch. The paper branch now carries
only the paper, its release metadata, the three version pins and the released PDFs; the `.gitignore`
rules and the two `tools/papercheck.py` repairs moved to `fix/housekeeping`. No rebase was used: the
tip of the paper branch restores those two files to `main`'s version, and the history says so.
My own scratch — the DjVu extraction, `paper/build.log`, the `/tmp` copies — was removed. Other
sessions' untracked files and the root archives were left alone.
