---
name: paper-lean-sync-review
description: "Deep-review a mathematics paper together with its Lean 4 formalization: word-by-word text review, claim-by-claim independent verification, paper↔Lean sync ledger, citation audit, and a blind-spot checklist distilled from reviewing work other AI reviewers had already passed. Use for a requested deep review of a paper-plus-Lean repository, not for routine proof editing."
---

# Paper + Lean deep review

Method for reviewing a mathematics preprint and its Lean 4 formalization as one
artifact, in a repository that also has a previous AI review. The goal is not
only "is it correct" but "what did the author *and the previous reviewers* miss".

## Order of work

1. **Read the history before the files.** `git log --oneline`, the README
   change-log, and the latest full diff. The diff between the last-reviewed
   version and the current one is the highest-value attack surface: every
   inserted sentence is un-reviewed by anyone.
2. **Read the whole paper text once, sentence by sentence.** Keep a numbered
   ledger of every claim (definition, remark, example, proof step), with line
   numbers. Check every forward reference resolves and every "as in
   Section/Theorem N" points to the right item.
3. **Re-derive every proof independently.** Do not audit a step by agreeing
   with it; redo it, with signs. Most paper errors are sign-of-one-term or a
   tacit division by 2.
4. **Recompute every example exactly.** Over finite algebras compute exact
   solution *spaces* (conditions are usually linear in the map `D`; Gaussian
   elimination over `F_p`), and validate the harness by brute-force count on at
   least three algebra/condition pairs before trusting a dimension. Where
   feasible enumerate **all** maps.
5. **Build both artifacts fresh.** Clean LaTeX rebuild; `pdftotext`-diff the
   released PDF against the fresh one. Elaborate every Lean file with the
   toolchain the repository actually used (not the pinned-but-different one);
   `#print axioms` on the load-bearing declarations (expect `propext`,
   `Classical.choice`, `Quot.sound`; flag anything else and any `sorryAx`).
6. **Build the two-sided sync ledger.** Every paper claim → Lean status
   (proved/partial/absent/approximate + declaration name); every Lean
   declaration → paper status (current/stale/docstring-number wrong). Distrust
   docstrings and README tables: resolve them against the current text.
7. **Verify citations against sources.** First look for the source **on disk**: projects that ship a
   reference archive (a `*-references.zip` at the root, an `attachments/` or `refs/` folder) usually
   already contain the cited PDFs, and a publisher's bot wall or 403 is not evidence that the source is
   unavailable — an OCR'd full text on disk beats a paraphrase every time. Then web-fetch each remaining
   locator; record verified / wrong locator / claim stronger than source / unverifiable. Do not assert a
   locator you could not reach; say "unverified".
   **When the web-search tool fails, search the bibliographic APIs directly** with `web_curl`:
   `https://api.zbmath.org/v1/document/_search?search_string=…` (reviews, MSC codes, Zbl numbers) and
   `https://api.crossref.org/works?query.bibliographic=…` (volume, pages, DOI). Both answer without a
   key, and a zbMATH title/MSC search is real — if weak — novelty evidence: say which query you ran and
   that it was bibliographic, not full-text.
8. **Write the report**: verdict first; new findings with evidence; claim
   ledger; residual word-level items with line numbers; recommendations. Keep
   "could not verify" as an explicit section.

## Blind-spot checklist (things prior AI reviewers repeatedly missed)

- **#eval-only witnesses.** A `def isFoo : Bool := decide (∀ …)` plus
  `#eval isFoo` prints `true` at build time but proves *nothing*: there is no
  `example : isFoo = true := by decide`. Compare blocks side by side in the
  same file — if some blocks have checked `example`s and others don't, the
  others are unverified. (`#eval` output goes to the build log; a wrong value
  does not fail the build.)
- **Encoding expressibility.** When a paper's definition is encoded in Lean by
  a simplified gadget (e.g. a braiding as a binary map `σ : A → A → A` with
  product `x*y + σ x y * σ y x`), compute what the gadget yields on the
  paper's latest instances *before* claiming coverage: sign flips
  (`x ↦ -x`, `y ↦ -y`) often collapse the intended product to a different one.
  Prove the obstruction with one tiny kernel-checked example.
- **Version drift in three directions.** Paper claims the README/Lean
  docstrings assert; README change-log entries the git diff does not contain
  (check each "fixed X" against the actual diff — claimed fixes that were
  never applied do happen); toolchain pins that moved while the prose said
  nothing (`lean-toolchain` vs the version the files were checked with).
- **Characteristic edge cases.** Re-test every v-diff sentence at
  characteristic 2 and 3 specifically: "the two classes coincide", "the two
  conditions agree", "collapses to two". Then re-test over *non-prime* fields
  (e.g. F4): choices that are unique over F2 are not unique in general.
- **Numbers in prior reports.** Recompute at least the dimensions/spaces a
  previous review printed: a wrong dimension in a "verified" table is common
  and harmless only by luck.
- **Quantifier and hypothesis seams in new sentences.** A proof sentence of
  the form "X, which uses hypothesis H here" where the cited section proves X
  only under a *different* hypothesis H′ (e.g. invertibility vs torsion-freeness).
- **Lead-in prose around correct examples.** The example checks out; its
  framing sentence ("the next example shows both cases", "coincide") does not.
- **Hidden axiom footprints.** `native_decide` theorems carry the native-eval
  axiom; kernel `decide` ones don't. Distinguish them per declaration, not per
  file.
- **A theorem cited as a hypothesis may be a paper-shaped hole.** When a paper cites a deep theorem and the
  Lean development carries it as a `Prop` parameter, the interesting question is what its *proof* needs:
  OCR of an old scan renders notation ambiguously (an overlined defect `ab` reads as the product `ab`),
  and the wrong reading turns a true lemma into a false one. Check a contested identity numerically in a
  concrete example before building anything on it.
- **Basis-pairs-only machine checks.** A witness theorem quantifying over
  basis pairs of a finite algebra leaves the bilinearity reduction in a
  comment; that is a stated-versus-proved gap unless the reduction is
  formalized or the comment is explicit everywhere the theorem is cited.

- **Asserted one-line implications.** A proof can be complete except for a
  lemma hidden in "so" or "hence" — e.g. "if `α² ⊗ α² = id` then `α² = λ id`"
  (true, but unproved and load-bearing). Check every implication that is not a
  substitution or a ring axiom; reproduce it or flag it.
- **OCR splits in scanned sources.** A theorem number can be separated from its
  word by a column or line break: Herstein 1957 reads "3.1. … THEOREM" across a
  break, so `grep "THEOREM 3.1"` finds nothing and a reviewer reports a locator
  that does not exist. Read the block (or the page image) before declaring a
  citation wrong, and before declaring a theorem absent.
- **A reference archive can be incomplete.** Count the PDFs against the
  bibliography: this project ships 16 for 17 entries (Pierce 1982 is not there).
  "Not found on disk" is not "not cited".
- **A claimed fix applied in exactly one place.** A changelog entry can be
  satisfied in the header of a file and false fifty lines below it (v73:
  `lean/BACKGROUND.md`'s header was updated, §2 still pinned v63 with stale line
  numbers). Check the whole file the claim is about, not the diff hunk.
- **Hand-rolled linear algebra is where silent wrong answers live.** If you write
  a solver for a system on maps: every component of a vector equation is a
  separate equation (collapsing them gives a weaker system), and an unknown
  index `t*n+i` written as `k*n+t` leaves a constraint inactive. Validate against
  brute-force enumeration on the smallest case and against a table with known
  values on a larger one, and keep the two bug patterns in the skill that ships
  the solver (`bsd-exact-algebra`).
- **Search may be unavailable.** If the search endpoint errors, say "no external
  search was possible" — never let a local bibliography absence stand in for a
  novelty check.

## Anti-patterns

- Accepting a previous review's "verified" without re-running one of its
  computations (spot-recompute at least the headline numbers).
- Reporting a Lean file's successful build as evidence of what its `#eval`s
  printed.
- Closing the review without a section on what could not be checked.
