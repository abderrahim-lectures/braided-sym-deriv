---
name: paper-review-gate
description: "Run and interpret the mechanical gate for a paper-plus-Lean review: LaTeX build (pages, overfull boxes, version label, released-artifact diff), Lean build under the pinned toolchain and manifest, sorry/axiom audit, and the report checklist. Use at the start and end of any review of this repository's paper, or when asked whether the paper and its formalization are in a consistent state."
---

# Paper review gate

**A PASS from this gate does not mean the paper is true.** It checks that the
artefact is consistent and that the Lean tree compiles with a clean axiom
footprint. It cannot see false mathematics: v62 passed the predecessor gate while
one of its sentences was false. Truth is the review's job; the gate's job is to
stop you reviewing a stale or broken artefact.

Run it before reading the paper and again after any edit:

```bash
python3 tools/papercheck.py            # all legs
python3 tools/papercheck.py --skip-lean
python3 tools/papercheck.py --skip-pdf
```

It prints one line per check and exits non-zero if any fails. Both legs skipped is
"nothing checked" and FAILs. Cost: the PDF leg is ~20 s; the Lean leg is minutes
when warm and **can exceed 30 minutes** when the VM is loaded by other projects'
Lean builds (measured: a comment-only edit to `Paper.lean` forced a rebuild of
its dependents and the 149-declaration audit took over 30 min at load 8.7). Run
the legs separately when that happens — `--skip-lean` for the PDF leg, then
`cd lean && lake build && lake env lean check_axioms.lean` in the background —
and do not read a timeout as a FAIL: it is UNKNOWN, and the tree may be further
along than the kill suggests (check `find .lake/build/lib/lean -name '*.olean'`).

## What the legs do now (v73 state — the tool is the authority; re-read it if in doubt)

1. **PDF.** `latexmk -g` in `paper/` (forced, so a no-op build cannot pass).
   Requires: 0 overfull, 0 undefined references/citations, no `! ` log errors;
   the fresh build's page count **equals the released artefact's**; its text
   equals the released text (`pdftotext`, modulo the "compiled ⟨date⟩" line); and
   the released `pdf/braided-sym-deriv-<v>.pdf` prints `\paperversion` on page 1.
   A missing or mismatched artefact fails. Say "text-identical" by default; a
   rebuild **is** byte-identical when `SOURCE_DATE_EPOCH` is set to the released
   file's `CreationDate` (measured on v73: md5 `a7d1b15b…` reproduced exactly),
   so "never byte-identical" is too strong.

   Check the fonts too: `pdffonts <pdf> | grep "Type 3"` must be empty. v73 and
   v74 embedded a bitmap font `F84` for every section sign — the class takes `\S`
   from OT1 at 10.95 pt, no scaled Type 1 CM is installed, and `mf-nowin` wrote a
   `.pk` that no repository file mentions. `\usepackage{lmodern}` fixes it
   (v75: 0 Type 3, 0 overfull, 0 underfull).
2. **Lean.** `lean/lake-manifest.json` must exist and the `lean` on `PATH` must
   be the toolchain `lean/lean-toolchain` pins (`v4.36.0-rc2` at v73), then
   `lake build` of the default target. Hash-based dependency tracking replaces
   the old per-file `LEAN_PATH` calls and the stale-olean problem; do **not**
   hand-manage oleans any more.
3. **Trust.** `lake env lean check_axioms.lean`: 149 declarations at v73, every
   footprint inside `{propext, Classical.choice, Quot.sound}` plus the
   explicitly enumerated `native_decide` sites in `NATIVE_DECIDE_SITES` (two
   named theorems at `Triangular.lean:132,166` plus three anonymous examples).
   A non-whitelisted axiom fails. The source trust scan counts
   `sorry`/`native_decide`/`axiom` uses against the same waiver list; new ones
   fail.
4. **Report.** Verdict as 0 fatal / N major / M minor; every numeric claim
   recomputed, not quoted (`bsd-exact-algebra` does the finite ones in 0.3 s);
   every citation opened at its page; a paper↔Lean ledger with an explicit row
   per claim of the current version; a blind-spot list; and a statement of what
   was not verified.
5. **Housekeeping.** Deliverables go to `results/` (gitignored), not the repo
   root; report files are Markdown plus a PDF built with pandoc/xelatex; the
   working tree is left as found.

## Reading a failure

* `FAIL` means the artefact is inconsistent with itself. `UNKNOWN` means the
  check was killed (signal, timeout, OOM) — that is **not** a proof failure and
  not a pass. A `Remark46.lean` failure on a loaded machine is usually memory
  (its peak is ~8 GB), not mathematics: re-run it alone before believing it.
* Run one Lean leg at a time. Two gates at once on a loaded VM produce OOM
  failures that look like proof errors.

## Pitfalls this project has already paid for

- `ring`/`ring_nf` do not know that `(3 : ZMod 3) = 0`; polynomial identities over
  `ZMod p` fail with them. Over `Fin p` `decide` works — but only on **closed**
  goals, and only up to about `81² = 6561` cases (≈16 s); `81³` is killed by the
  OOM killer. For three-variable identities prove bilinearity structurally and
  expand with `simp [mul, mul_add, add_mul, mul_assoc] <;> ac_rfl`.
- `native_decide` leaves `…_native.native_decide.ax_1_1` in `#print axioms`.
  Report it; do not hide it, and never introduce a new one.
- `#print axioms` on a name declared inside a namespace, from outside it, needs
  the qualified name — otherwise the file fails to elaborate and the failure
  looks like a Lean bug.
- Report PDFs: `pandoc … --pdf-engine=xelatex -V mainfont="DejaVu Sans"`;
  define the paper's macros (`\Der`, `\BSDer`, …) in an include-in-header file.
- The endpoint: `plugin_start` from `tools/papercheck.plugin.json`, then call
  `plugin-papercheck_papercheck` (accepts `skip_pdf`, `skip_lean`).
