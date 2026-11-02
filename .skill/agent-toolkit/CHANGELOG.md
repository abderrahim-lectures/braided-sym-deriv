# Toolkit changelog

- **2026-11-01** — created the index and the improvement loop. New skill
  `paper-review-gate` (with `tools/papercheck.py`). Lessons recorded from the
  v62/v63 review: the `LEAN_PATH` fix, the qualified `#print axioms` pitfall
  (`BraidedSymDerivTrace.traceScalar_lie_not_der`), the `native_decide` trust
  axiom in `Triangular.lean`, and the naturality pitfall behind Remark 2.4
  (natural on algebras ≠ natural on K-modules; idempotents give involutions by
  `id - 2P`).

- **2026-11-01 (second pass)** — self-review of the two authored skills against
  the session's friction: added the `ZMod p`/`ring` pitfall, the `decide`
  size limit (6 561 cases ≈ 16 s, `81^3` OOM), the `native_decide` axiom, the
  qualified `#print`, `LEAN_PATH`/oleans, the pandoc/xelatex recipe, and the
  endpoint call to `paper-review-gate`. Recorded the vendoring decision in the
  index. Evidence: `Remark46.lean`, `bsd_v62_general.lean`, `BraidedSymmetric.lean`.

- **2026-11-02 (v73 review)** — new skill `bsd-exact-algebra`: the validated
  exact solver (`harness.py`), the full battery (`cases.py`, 0.3 s, all values
  reproduce), and `BASELINE.md` — the number table, the **closed** findings a
  later review must not re-report, the traps that produced false findings, and
  the open question's exact state. `paper-review-gate` rewritten: it still said
  "never use `lake build` (no manifest, network)" long after the gate had been
  rebuilt around a committed manifest and the pinned toolchain; it now opens with
  "a PASS does not mean the paper is true" and describes the legs as they are.
  `paper-lean-sync-review` gained six blind spots: an asserted one-line
  implication, an OCR-split theorem number, an incomplete reference archive, a
  fix applied in one place only, a hand-rolled linear-algebra index/row bug, and
  an unavailable search endpoint. Evidence: Herstein 1957 p. 1109 (the "3.1. …
  THEOREM" split), `lean/BACKGROUND.md` §2, `F_5[ε]/ε²` brute force, and the
  v73 review `results/review-braided-sym-deriv-v73.md`.
