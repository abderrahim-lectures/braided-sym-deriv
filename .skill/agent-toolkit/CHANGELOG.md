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
