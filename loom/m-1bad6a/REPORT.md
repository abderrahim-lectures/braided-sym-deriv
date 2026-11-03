# Report: braided-sym-deriv v79, model m-1bad6a

Status: draft in progress. Sections marked WRITING are filled when the member agents commit.

## 1. Summary

- **Model id**: `m-1bad6a` (from `~/.loom/loom whoami`; no id typed by hand).
- **Pack**: installed from `loom-pack-braided-sym-deriv-v79.zip` with `~/.loom/loom pack install`; VERSION v79 =
  repository `\paperversion` 79 (preflight PASS).
- **Tasks**: the pack's `TASKS.md` carries **one** task, T1 (reference row 15, Pierce 1982). The brief that
  started this run also named T2 (abstract sentence 5) and T3 (the origins first sources); this v79 pack flags
  neither (both verdicts are PASS), so they are answered here as checks with the evidence, without claim rows.
- **BLOCKED**: none.
- **UNVERIFIED**: `Pierce1982` — see section 2.
- **Lean**: nothing to bump. `lean/lean-toolchain` is `leanprover/lean4:v4.36.0-rc2`, which is exactly what
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` answers today;
  `lake-manifest.json` pins Mathlib `bf20166d9391`; `lean --version` = 4.36.0-rc2, `Lake 5.0.0-src`.
- **Platform skills used**: `paper-lean-sync-review`'s statement-audit method (the paper↔Lean row-by-row
  comparison behind section 3), `lean-statement-audit` (given to the audit member), `paper-review-gate` (the
  repository's own gate, run in section 5). The `loom-*` skills of the toolchain were read by every agent as
  its prompt requires.

### The pack preflight's five questions

1. **Is the paper repository connected?** Yes. `github_status`: `abderrahim-lectures/braided-sym-deriv`,
   default branch `main` at `da26080` (= v79), `read_only: false`. Local `main` is at the same commit.
2. **Can you start sub-agents, how many at once?** Yes: `ultramath_start` accepts a swarm; each member of a
   swarm needs its own swarm (one direction per swarm), and the machine is the real limit (4 CPUs, 15 GB).
   This run used three one-member swarms: sources, Lean, audit.
3. **Did the platform load the `.skill/` skills?** `skills_list` sees the repository's own skills
   (`bsd-exact-algebra`, `paper-lean-sync-review`, `paper-review-gate`, `agent-toolkit`, `loom-*` ×14,
   `connect-mcp-server`, `lean-*`). `.skill/loom-*/` is git-excluded, as the preflight sets it.
4. **Can `plugin_start` and `mcp_connect` run, which servers connected?** `plugin_start` ran four times: the
   guard with its 9 tools, the guard watcher, health with its 6 tools, the health watcher. No `mcp_connect`
   was needed for the work; the two MCP servers of the project are the two loom plugins.
5. **Can you push a branch, and does a push wait for an approval?** WRITING — answered after the push.

## 2. Tasks

### T1 [references] sources missing from the library — Pierce 1982

The row as `~/.loom/loom refs check` prints it:

```
row 15 (Pierce1982): missing -
```

The four places the paper cites it (`paper/braided-sym-deriv.tex`):

| line | locator | the fact the paper takes from it |
|---|---|---|
| 494 | `\citep[\S3.5]{Pierce1982}` | a finite-dimensional reduced commutative algebra is a product of finite separable field extensions |
| 604 | `\citep[\S4.4]{Pierce1982}` | the radical of a finite-dimensional algebra is nilpotent |
| 604 | `\citep[\S3.5]{Pierce1982}` | Wedderburn: a semisimple algebra is a product of matrix algebras over division rings |
| 607 | `\citep[\S12.6]{Pierce1982}` | every automorphism of the quaternions is inner (Noether–Skolem) |

**What was tried, in order, with the answer each gave** (the sources member's record; I re-opened the scan and
checked the three table-of-contents lines myself):

| Route | Answer |
|---|---|
| `~/.loom/loom refs fetch 10.1007/978-1-4757-0163-0` (the book's DOI, confirmed at Crossref) | `metadata only … no free copy`; the two candidates it tried are a Crossref `link` field pointing at an unrelated 1986 AMS paper and the publisher landing page |
| `~/.loom/loom refs fetch "Pierce, R.S.: Associative Algebras. GTM 88, Springer (1982)"` | refused, exit 2: the tool takes an arXiv id, a DOI or a PDF URL, and has no title search |
| `~/.loom/loom refs fetch 0-387-90693-2` and `978-1-4757-0163-0` | refused the same way: the tool takes no ISBN |
| Unpaywall `api.unpaywall.org/v2/10.1007/978-1-4757-0163-0` | `"is_oa": false`, `"oa_status": "closed"`, `"oa_locations": []` |
| OpenAlex `api.openalex.org/works/doi:…` | work `W4234106236`, `"oa_status": "closed"`, `"best_oa_location": null` |
| archive.org and Open Library | the item `associativealgeb00pier_0` has `access-restricted-item = true`, collection `printdisabled`: a lending copy, not an open one |
| Springer `link.springer.com/book/10.1007/978-1-4757-0163-0` and its front-matter PDF | HTTP 200 with a JavaScript bot challenge; the site was not used further |
| Google Books `googleapis.com/books/v1/volumes` | HTTP 429; one call, then stopped |

**The one open copy that exists**, and what it settles. A university repository hosts an 11-page scan of the
book's front matter (`unina2.on-line.it/sebina/repository/catalogazione/documenti/Pierce - associative
algebras.pdf`, `Adobe Acrobat 9.4 Paper Capture` OCR, created 2012-04-30). I opened it and checked the lines
below myself (`pdftotext -layout`, then `grep`):

```
3.5. Wedderbum's Structure Theorem                         49
4.4. The Radical of an Artinian Algebra                    61
12.6. The Noether-Skolem Theorem                          230
```

(the OCR reads `Wedderbum` for `Wedderburn`.) Its Preface also says in the author's words that the first part
contains "Wedderburn's Structure Theorem for Semisimple Algebras" and that Chapter 12 builds "the Jacobson
Density Theorem, the Noether-Skolem Theorem, and the Double Centralizer Theorem".

So all four citations point at sections whose titles are what the paper uses them for:
`§3.5` = Wedderburn's Structure Theorem (p. 49), `§4.4` = The Radical of an Artinian Algebra (p. 61),
`§12.6` = The Noether–Skolem Theorem (p. 230). That is a table of contents and a preface, not the text of any
cited passage: no sentence of §§3.5, 4.4, 12.6 was read, so **`UNVERIFIED Pierce1982`** stands, the four
citations are untouched, and no claim of the paper rests on a passage this run read.

`~/.loom/loom refs unverified` prints:

```
UNVERIFIED Pierce1982   # no library file
UNVERIFIED 10-1007-978-1-4757-0163-0   # metadata only: no PDF served; tried …
```

**Two copies were found and deliberately not opened.** The member's second search returned two whole-book
files (a `.djvu`-style scan and a second redistribution). It reports them as unauthorised redistributions and
did not open them; the rule "copies come only from open repositories, preprint servers and the publisher's own
open access" leaves them out even though they would have settled the text.

**Two observations for the owner, not edits** (no task asked for a paper change, and neither can be acted on
without reading the sections):

- `PROPOSE:` the citation at line 494 uses `§3.5` for "a finite-dimensional reduced commutative algebra is a
  product of *finite separable* field extensions". Wedderburn's structure theorem supplies the product of
  fields; separability is the subject of Pierce's Chapter 10, "Separable Algebras" (p. 179), with
  `10.2. Separability` at p. 181 and `10.7. Separable Algebras over Fields` at p. 190. A locator that also
  names `§10.7` would match the sentence better. I did not change it: the passage was not read, and the task's
  instruction for an unreadable source is to leave the citation as it is.
- The repository's own record (`results/reviews-timeline.md`, the v66 entry) quotes §12.6, p. 230 with the
  Noether–Skolem statement as read from a third-party scan in an earlier session. This run did not re-read it,
  so the honest label for the row stays `UNVERIFIED`; a later session that has the scan again should say so
  with its own quotation.

### T2 [abstract] sentence 5 — checked, no edit needed

Abstract sentence 5 (verbatim): "The negative of the identity gives all linear endomorphisms, and the negative
of the swap gives the Lie derivations."

Where the paper proves it: Remark 2.5, `\label{rem:sigma-derivation-classification}`
(`paper/braided-sym-deriv.tex`, lines 225–258). Its two paragraphs read

> The involution $-\mathrm{id}$ gives all linear endomorphisms, and $-\tau$ gives the Lie derivations.
> Their products are $x \cdot_{-\mathrm{id}} y = xy - xy = 0$, $x \cdot_{-\tau} y = xy - yx = [x, y]$.
> So $\BSDer_{-\mathrm{id}}(A) = \mathrm{End}_K(A)$, since every linear map is a derivation of the zero product,
> and $\BSDer_{-\tau}(A)$ is the space of Lie derivations of $A$ \citep[p.~183]{Martindale1964}.

This is exactly the abstract's sentence, and it is unconditional in the characteristic (the zero product and
the commutator are the products $x \cdot_\sigma y = \mu(x \otimes y) + \mu(\sigma(x \otimes y))$ at $\sigma = -\mathrm{id}$
and $\sigma = -\tau$). Lean counterparts, already in the tree: `BSDGeneral.bsd_neg_id_all` and
`BSDGeneral.bsd_neg_tau_is_lie` (`lean/RESULTS.md`, row "Rem 2.4, 2.5"). So T2 needs no edit; an edit would be
work no task asked for.

### T3 [origins] the first sources of the old notions — checked

`loom-pack/verdicts.md` §4 lists three notions whose origin has no key in the library:

- **braided-symmetric derivation** — no older source of the notion; the nearest old source is Herstein 1957,
  p. 1104 (the Jordan derivation, the case of the swap).
- **twisted jordan derivation** — no older source of the notion; the nearest old sources are Herstein 1957,
  p. 1104 and Hosseini–Karizaki 2019, §1.
- **twisted derivation** — the name is older for other notions: Ore 1933, Ann. of Math. 34, pp. 481–482,
  rules (4)–(5), and Davydov 2013, J. Pure Appl. Algebra 217, introduction, pp. 567–568.

Two of these keys are in the library (Herstein 1957, Hosseini–Karizaki 2019), so the paper's use of them can be
checked by reading; Ore 1933 is not cited in the paper and has no file. I read both passages myself, in
`loom-pack/references/text/`.

**Herstein 1957, p. 1104** (`Jordan derivations of prime rings (1958).txt`, the JSTOR scan of Proc. AMS 8(6),
pp. 1104–1110; the printed page number `1104` falls at the end of this passage):

> By a Jordan derivation, ', of an associative ring A we shall mean a derivation of the Jordan ring formed from A;
> that is, for all a, b EA, (a o b)'=a' o b+a o b'. Writing this out in terms of the associative operations of A,
> a Jordan derivation, ', of A is an additive mapping which satisfies (ab+ba)'=a'b+ab'+b'a+ba' for all a, b ∈ A.
>
> … for such rings A [of characteristic not 2] a Jordan derivation, ', can be defined by (1) (a + b)' = a' + b',
> (2) (a2)' = aa' + a'a.

The paper (line ~97) says Herstein "takes the sum $ab + ba$ without the half", and (line ~173) that he "defines
a *Jordan derivation* as a derivation of the Jordan ring of $A$ … and records that for rings of characteristic
different from $2$ it can be defined by the square identity $D(x^2) = D(x)x + xD(x)$". Both sentences say what
the page says; the locator `p.~1104` is where the passage is.

**Hosseini–Karizaki 2019, §1** (`Functional equations characterizing σ-derivations.txt`, Acta Sci. Math.
(Szeged) 85, 431–440, `doi:10.14232/actasm-018-594-6`), p. 431, "1. Introduction and preliminaries":

> Let σ : R → R be an additive mapping. An additive mapping d : R → R is called a σ-derivation (resp. Jordan
> σ-derivation) if d(xy) = d(x)σ(y) + σ(x)d(y) (resp. d(x²) = d(x)σ(x) + σ(x)d(x)) holds for all x, y ∈ R.

The paper (line ~180) defines an α-derivation by `D(xy) = D(x)α(y) + α(x)D(y)` and cites `\S1`. The identity is
there, on the first page of §1. Two differences are worth naming: the source's σ is an additive monomorphism with
σ(e) = e, of which the paper's automorphism is the special case it needs; and the source calls the notion
σ-derivation, while the paper writes α-derivation.

**Ore 1933**: `paper/braided-sym-deriv.tex` never mentions Ore (grep over the whole file), and no Annals of
Mathematics volume is in the library. One Crossref search returns `10.2307/1968173`, O. Ore, "Theory of
Non-Commutative Polynomials", Ann. of Math. 34, p. 480 (1933), which matches the entry in `verdicts.md` §4. It
was not read and nothing rests on it.

So T3 needs no edit either: the two first sources the origins table leans on say what the paper says they say,
and the third is named only as a different, older use of the word.

### The Lean task of `loom-pack/lean/LEAN-TASK.md`

WRITING — section 3.

## 3. Lean

**Step 0 of `lean-pack/lean/LEAN-TASK.md` (the latest Lean and Mathlib) is already satisfied.** Checked three
ways: `lean/lean-toolchain` reads `leanprover/lean4:v4.36.0-rc2`; `lean --version` answers
`Lean (version 4.36.0-rc2, … commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)` and `Lake 5.0.0-src+b35cb10`;
and `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` answers exactly the
same string, with `lake-manifest.json` pinning Mathlib at `bf20166d9391`. So the pair is Mathlib's current pair,
nothing was bumped, nothing was downgraded, and no `lake update` or `lake clean` was run.

**The four own results are bound.** `loom/m-1bad6a/BINDINGS.tsv` has one row per result, all `proved`, each
declaration named, and each difference of hypothesis named in the `notes` column:

| label | paper | Lean declaration(s) | what differs, in one line |
|---|---|---|---|
| `prop:defect` | Prop 3.2 | `BSDGeneral.bsd_iff_automorphism`, `bsd_iff_antiautomorphism`, `residual_automorphism`, `residual_antiautomorphism`, `Defect.prop_defect_aut`, `Defect.prop_defect_anti` | maps are additive (`A →+ A`), α additive and multiplicative or anti-multiplicative; stronger than the paper, which works over a field |
| `cor:twisted-semiprime` | Cor 3.5 | `BSD.corollary_3_5_unconditional`, `AntiAutomorphism.corollary_3_5_anti_unconditional` | the paper's set equality read inside the α-commuting class; Brešar 1988 Thm 1 is proved in-tree, so no `hBresar` hypothesis remains |
| `thm:twisted-commutative` | Thm 4.1 | `BSD.theorem_4_1`, `twisted_commutative`, `BSDGeneral.thm41_core` | hypotheses match the paper's sentence; `2` invertible is `IsUnit (2 : A)`; the sharpened statement in the proof is `thm41_core` |
| `prop:twisted` | Prop 4.4 | `TW.D1_alphader`, `TW.D1_not_twisted`, `TW.dd_der`, `TW.dd_not_alphader`, `TW.D1_comm_alpha`, `TW.dd_comm_alpha`, and the all-pairs closures `Closures.TW_*_all` | the two witnesses are formalized, not a set-level non-inclusion sentence; both non-inclusions follow with no gap |

**What I checked myself, rather than taking the ledger's word.** The repository's `lean/RESULTS.md` names
`TwistedCommutative.prop_defect_aut` and `TwistedCommutative.TW.D1_alphader`; no namespace `TwistedCommutative`
exists, and `#check` of those names fails with `unknown identifier`. The real names are the ones above (root
namespaces `Defect`, `TW`, and the `BSD`/`BSDGeneral` namespaces). I ran a referee file of my own and got, among
others:

```
@BSD.corollary_3_5_unconditional : ∀ {A} [Ring A], TwoTorsionFree A → SemiprimeRing A →
  ∀ (α : A ≃+* A), (∀ x, α (α x) = x) → ∀ (D : A →+ A), BSD.Comm D ⇑α →
    (BSD.TwistedAlpha (↑α) D ∧ BSD.JDer D ↔ BSD.Der D)
@BSD.theorem_4_1 : ∀ {A} [CommRing A] [IsReduced A] (α : A ≃+* A), (∀ x, α (α x) = x) →
  ∀ (D : A →+ A), IsUnit 2 → BSD.Comm D ⇑α → (BSD.TwistedAlpha (↑α) D ↔ BSD.Der D)
'BSDGeneral.residual_automorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSD.corollary_3_5_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'BSD.theorem_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Build and audit.** `bash ~/.loom/checks/lake-build.sh <lean dir>` answers
`Build completed successfully (18304 jobs).` A scan of `Research/` and `Background/` finds no `sorry`, no
`admit` and no `axiom` declaration (the matches are docstrings that say so). `lake env lean check_axioms.lean`
exits 0 with 187 lines: 173 declarations carry an axiom footprint, all inside
`{propext, Classical.choice, Quot.sound}`, and 6 depend on no axiom. Four rows of `BINDINGS.tsv` bind
declarations that `check_axioms.lean` does not cover (`BSDGeneral.*`, `Closures.TW_*`); their footprints were
taken from a scratch `#print axioms` run and are in the three standard axioms. `formalization.yaml` now says
"a 179-declaration axiom audit (173 of them carry an axiom footprint, the number the gate prints)" — the two
numbers are the 179 declarations the audit file names and the 173 the gate counts.

**The independent statement audit** is `loom/m-1bad6a/AUDIT.md`, written by an agent that wrote none of the
Lean. It quotes each paper statement verbatim, expands every project predicate that hides a premise
(`BSD.TwistedAlpha`, `BSD.Der`, `BSD.JDer`, `BSD.Comm`, `SemiprimeRing`, `TwoTorsionFree`, `IsReduced`), and
rates the four rows `stronger`, `stronger`, `stronger`, `weaker`:

| row | audit verdict | why |
|---|---|---|
| `prop:defect` | stronger | additive maps on an arbitrary ring, no involution and no bijectivity of α required |
| `cor:twisted-semiprime` | stronger | the anti-automorphism half needs no involution, only α multiplicative, α anti-multiplicative and α1 = 1 |
| `thm:twisted-commutative` | stronger | additive maps where the paper asks K-linear; the hypotheses themselves match |
| `prop:twisted` | weaker | the Lean states the six witness facts, not the paper's set-level non-inclusion |

The last row is the one to read carefully. Every fact the paper's Proposition 4.4 needs is kernel-checked (`dd` is
a derivation, `D1` is an α-derivation, both commute with α, and each fails the other rule at `(ε,ε)`), and the
step from those facts to "the two classes do not contain each other" is one line using the proved
`der_twisted_iff_comm`. What is missing is a Lean declaration of that line. `BINDINGS.tsv` says `proved` and
`AUDIT.md` says `weaker`; both are right about different things, the `BINDINGS.tsv` row now points at the audit,
and a later run can close it with one declaration that the pack's task did not name.

The audit also found one thing worth keeping in the record: `lean/lean-toolchain` pins v4.36.0-rc2, while the
Mathlib *source* installed on this machine for reading (`/opt/mathlib`) is v4.33.1. The audit therefore checked
`IsReduced` against the tree's own use of `IsReduced.eq_zero` rather than against the source it could read —
the right call, and the reason the gate builds against the manifest-pinned Mathlib instead.

## 4. Sources opened

| Key | Opened where | What I found | Read fully? |
|---|---|---|---|
| Pierce1982 | WRITING | | no |

## 5. Commands and their last lines

| Command | Where | Last lines |
|---|---|---|
| `~/.loom/loom status` | project root | worktree, branch and model printed; `(no TASKS.md: look in loom-pack/, loom/ or the project root)` before the pack was installed |
| `~/.loom/loom pack install loom-pack-braided-sym-deriv-v79.zip` | project root | `version v79, 1 task(s), 17 reference row(s), 16 PDF(s)`; `row 15 (Pierce1982): missing -` twice; `project braided-sym-deriv v79 (scope in .loom/scope.json)` |
| `~/.loom/loom refs check` | project root | `row 15 (Pierce1982): missing -` twice, exit 1 |
| `bash loom-pack/preflight.sh braided-sym-deriv <repo> m-1bad6a` | project root | 25 rows, 24 PASS, one FAIL (optional `uvx`), exit 0; full table in `loom/m-1bad6a/PREFLIGHT.md` |
| `bash ~/.loom/checks/lake-build.sh <repo>/lean` | project root | `Build completed successfully (18304 jobs).` (about 7 s, cache warm) |
| `lake env lean check_axioms.lean` | `<repo>/lean` | exit 0, 187 lines, 173 footprints inside the three standard axioms and 6 declarations with none |
| `python3 tools/papercheck.py` | integration worktree | see section 3 and the gate line below |
| `git diff --name-only main...HEAD` | integration worktree | the eight files of section 6 |

The repository's own gate, run in the integration worktree with `lean/.lake` linked to the project cache and
after merging both member branches:

```
note  legs run: pdf, lean (lake build + axiom audit + trust scan)
note  pdf: fresh 13 pp vs released 13 pp, 0 overfull, 0 undefined, text identical, released label ok
note  lean: lake build green (0 module(s) built this run)
note  axiom audit: 173 declarations, 2 whitelisted native_decide footprint(s)
note  trust scan: 5 sorry/native_decide/axiom use(s) outside comments, 5 whitelisted, 0 new
GATE: PASS
```

That is the repository's own PASS line for its own repository, not a judgement of the paper: it says the tree
builds, the PDF is identical to the released one, and the axiom footprint has not grown. It says nothing about
whether the paper is true, and no Jev run was made.

## 6. Files changed

`git diff --name-only main...HEAD` in the integration worktree, and nothing else:

```
formalization.yaml
loom/m-1bad6a/BINDINGS.tsv
loom/m-1bad6a/PREFLIGHT.md
loom/m-1bad6a/REPORT-lean.md
loom/m-1bad6a/REPORT-sources.md
loom/m-1bad6a/REPORT.md
loom/m-1bad6a/STATE.md
loom/m-1bad6a/claims.tsv
```

Eight files, 827 insertions, 4 deletions. **No file of `paper/` and no `.lean` file changed**: the run's honest
outcome is that T1 stays `UNVERIFIED`, T2 and T3 needed no edit, and the four own results were already
formalized. `formalization.yaml` is the one repository file changed, three stale lines to v79 plus the audit
count.

## 7. Friction

1. **The pack's `TASKS.md` and the brief that started the run disagree.** The brief names T1, T2, T3; the
   pack's `TASKS.md` (generated from the flagged rows of these verdicts) names T1 only, and its header says
   "1 task(s) from 0 flagged row(s)". `bash <LOOM>/checks/claim.sh -t T2 …` refuses T2 and T3 because they are
   not in `TASKS.md`. This run therefore answers T2 and T3 in the report and writes claim rows only for T1 and
   for the Lean task (which carries `-`).
2. **Three commits on this branch were not made by this session.** At 16:59:22–30, between this session's
   worktree creation (16:58) and its first read of the pack, `0fe235d`, `dfec595` and `1b2f7d2` appeared on
   `loom/v79/m-1bad6a/integration`, authored `review-bot`, carrying a finished-looking `REPORT.md`,
   `REPORT-sources.md`, `claims.tsv` (T1 settled as UNVERIFIED) and a `PREFLIGHT.md` produced by running the
   pack preflight with the worktree as the clone argument. Their REPORT.md also states "Lean n/a (no Lean task
   in this pack)", which is false: `loom-pack/lean/LEAN-TASK.md` has four rows. This session did not adopt that
   content; the files were rewritten from evidence, and the history keeps the three commits.
3. **A worktree's `.git` is a file, and `preflight.sh` refuses it.** The preflight's `ensure_exclude` tests
   `[ -d "$CLONE/.git" ]`, so run with a worktree as the clone argument it answers
   `FAIL no repository at …/.loom/m-1bad6a/integration`, which is what the 16:59 `PREFLIGHT.md` records. The
   check needs `-f` as well. Reported, not patched (`loom-pack/` is read-only for this run).
4. **Two `lake build`s ran at once on the shared `.lake`.** This session's Lean member builds in its worktree
   with `.lake` linked to the project root's cache, and a second session of this project ran
   `cd lean && lake build` in the project root at the same time; the shared build directory briefly lost
   `Research/BraidedSymDeriv/Paper.olean` and one `lean` call of mine failed with
   `object file … does not exist`. Both later recovered. `checks/lake-build.sh` locks per `.lake` directory and
   cannot see a plain `lake build` started by another session.
5. **`lean/RESULTS.md` names declarations that do not exist under those names.** It writes
   `TwistedCommutative.prop_defect_aut` and `TwistedCommutative.TW.D1_alphader`; the source has no namespace
   `TwistedCommutative` at all — the declarations are `Defect.prop_defect_aut`, `Defect.prop_defect_anti`,
   `TW.D1_alphader`, `TW.D1_not_twisted`, `TW.dd_der`, `TW.dd_not_alphader`, and the root-level
   `twisted_commutative` and `leibnizDefect`. A `#check` of the ledger's names fails with
   `unknown identifier`.
6. **`uvx` is absent** (preflight, optional): the fallback is `python3 -m venv`, and nothing in this run
   needed `lean-lsp-mcp`.
7. **The platform skill `lean-statement-audit` is not in the shared toolchain.** `~/.loom/skills/` lists the
   fourteen `loom-*` skills only; `lean-statement-audit` (and `lean-workflow`, `lean-elaboration`,
   `lean-project-architecture`) are read from `.skill/` inside the repository. A member told to `cat` its skills
   from `<LOOM>/skills/` does not find them, and this run's audit member had to be given the repository path.
8. **The Mathlib source on the machine is not the pinned one.** `/opt/mathlib` is v4.33.1 while
   `lean/lean-toolchain` pins v4.36.0-rc2. The build is fine — it uses the manifest checkout under
   `lean/.lake/packages` — but a reader of Mathlib's source (the audit, or any statement comparison against
   Mathlib's definitions) gets a different version from the one the build uses. This run's audit noticed and
   cross-checked `IsReduced` against the tree's own use of it.
9. **The shared project root is not stable.** While this run worked, another session of the same project
   checked out a branch `fix/v79-metadata` (commit `afe2a26`, "fix metadata version pins v73/v74/v75 -> v79") in
   the project root and ran its own `lake build` there. I made no edit in the project root, and the one root
   file this run changes (`formalization.yaml`) is changed on my branch only. The other session's fix and this
   run's overlap in intent: both bring the v75 pin in `formalization.yaml` to v79.
10. **`claim.sh` cannot carry a task the pack does not list.** It refuses `-t T2` and `-t T3` because
   `loom-pack/TASKS.md` has only T1; the two checks are in this report with their evidence and no claim row.

## 8. Doubts

- Pierce 1982 is not obtainable from an open repository; see section 2 for what that leaves unverified.
- The Lean statements are additive `A →+ A` where the paper asks for `K`-linear maps, and the binary `σ`
  encoding is narrower than an involution of `A ⊗ A`. Both are recorded in `lean/RESULTS.md` and in
  `formalization.yaml`; they are properties of the tree as it stands, not something this run changed.
- `prop:twisted` is the one row where the two honest readings differ. The six witness facts are kernel-checked
  and `BINDINGS.tsv` calls the row `proved`; the independent audit calls the row's sentence `weaker` because no
  Lean declaration states the non-inclusion. The `BINDINGS.tsv` note now sends the reader to the audit, and the
  gap is one declaration of a one-line deduction. I did not add it: no task named it (rule 14).
- The `§3.5`/`§10.7` locator observation for line 494 is an inference from the book's table of contents and
  preface, not from reading either section. It is a `PROPOSE:` for the owner, and I have not changed the paper.
- The audit did not run Lean itself; its axiom reading is the Lean member's run, which I reproduced separately
  with the same result (173 footprints, 6 with none). No `sorry`/`admit`/new `axiom` exists in `Research/` or
  `Background/`, checked by `rg` in this session.
- No Jev run was made and this report claims no PASS of any kind. The only PASS in it is the repository's own
  gate on its own tree.

## 9. PROPOSE (ideas for the owner; nothing of this is in the paper or the Lean)

- `PROPOSE:` the citation at `paper/braided-sym-deriv.tex:494` uses Pierce `§3.5` (Wedderburn's structure
  theorem) for "a product of finite *separable* field extensions"; the book's Chapter 10 is "Separable
  Algebras", `§10.7` at p. 190. A locator naming both would match the sentence better. It needs the section read
  first, which this run could not do.
- `PROPOSE:` `lean/RESULTS.md` writes `TwistedCommutative.prop_defect_aut`, `TwistedCommutative.TW.D1_alphader`
  and the like; those namespaces do not exist. The declarations are `Defect.prop_defect_aut`,
  `TW.D1_alphader`, and the root-level `twisted_commutative`, `leibnizDefect`.
- `PROPOSE:` `lean/check_axioms.lean` does not cover `BSDGeneral.*` or `Closures.TW_*`, so four of the
  declarations the four bound rows rest on are outside the repository's own audit. Six `#print axioms` lines
  would close it; this run had to audit them in a scratch file.
- `PROPOSE:` `lean/RESULTS.md`, row Prop 3.2: the status cell says "arbitrary rings, no hypothesis relating `D`
  and `alpha`", which is true of the two residual identities and not of the iff statements in the same row.
- `PROPOSE:` `README.md` line 4 says "Current version: **v76**" and the changelog stops at v76; the source is
  v79. The `text` role owns that file and no task named it.
- `PROPOSE:` one Lean declaration stating Prop 4.4's non-inclusion for `TW`, using `TW_dd_der_all`,
  `TW_dd_comm_alpha_all` and `der_twisted_iff_comm`; that would turn the audit's `weaker` on that row into
  `same statement`.
