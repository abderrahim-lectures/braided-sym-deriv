---
name: paper-review-gate
description: "Run and interpret the mechanical gate for a paper-plus-Lean review: LaTeX build (pages, overfull boxes, version label), Lean elaboration of every file, sorry/axiom audit, and the report checklist. Use at the start and end of any review of this repository's paper, or when asked whether the paper and its formalization are in a consistent state."
---

# Paper review gate

Run the gate before reading the paper and again after any edit. `python3 tools/papercheck.py` prints one line per check and exits non-zero if any fails; `--skip-lean` and `--skip-pdf` shorten it.

1. **PDF.** `latexmk` in `paper/`; the version label on page 1 must equal `\paperversion`; page count and overfull boxes are recorded in `paper/build/<jobname>.log` (`grep -c Overfull` must be 0).
2. **Lean.** `LEAN_PATH=$PWD/lean:$LEAN_PATH lean <file>` for every file under `lean/Research/BraidedSymDeriv/`. Never use `lake build` (no manifest, network). A file is only checked when its own elaboration exits 0 — an `#print axioms` line at the end of a file must name its declarations fully qualified, or the file fails.
3. **Trust.** `grep -rn "sorry\|native_decide\|^axiom" lean/Research` must be empty except documented exceptions; `#print axioms` must show only `propext, Classical.choice, Quot.sound`, and any `…_native.native_decide.ax_1_1` must be reported, never glossed over.
4. **Report.** Verdict as 0 fatal / N major / M minor; every numeric claim recomputed, not quoted; every citation opened at its page; a paper↔Lean ledger with an explicit row per claim of the current version; a blind-spot list; and a statement of what was not verified.
5. **Housekeeping.** Deliverables go to `results/` (gitignored), not to the repository root; report files are Markdown plus a PDF built with pandoc/xelatex; the working tree is left as found.

## Pitfalls this project has already paid for

- `ring` and `ring_nf` do not know that `(3 : ZMod 3) = 0`; polynomial identities over `ZMod p` fail with them. Over `Fin p` (which has mod-`p` `Add`/`Mul`/`Neg` and reducible equality) `decide` works — but only on **closed** goals, and only up to about `81^2 = 6561` cases (≈16 s); `81^3` is killed by the OOM killer. For three-variable identities prove bilinearity structurally and expand with `simp [mul, mul_add, add_mul, mul_assoc] <;> ac_rfl`.
- `native_decide` leaves `…_native.native_decide.ax_1_1` in `#print axioms`. Report it; do not hide it, and do not use it in a file whose header claims kernel-only proofs.
- `#print axioms` on a name declared inside a namespace, from outside it, needs the qualified name — otherwise the file fails to elaborate and the failure looks like a Lean bug.
- `lean file.lean` on a file that imports `Research.…` needs `LEAN_PATH=$PWD/lean:$LEAN_PATH`; produce the olean with `lean -o X.olean X.lean` when another file imports it.
- Report PDFs: `pandoc … --pdf-engine=xelatex -V mainfont="DejaVu Sans"` — DejaVu Serif has no ✓; define the paper's macros (`\Der`, `\BSDer`, …) in an include-in-header file.
- The endpoint: `plugin_start` from `tools/papercheck.plugin.json`, then call `plugin-papercheck_papercheck` (accepts `skip_pdf`, `skip_lean`).
