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
