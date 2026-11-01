/- The import-clash regression test (kept for its historical name): Mathlib and
`BraidedSymmetric.lean`, whose root-namespace `LieDerivation` used to clash
with `Mathlib.Algebra.Lie.Derivation.Basic`, importable together again.  The
full axiom audit `check_axioms.lean` covers this too; this file is the minimal
probe. -/
import Mathlib
import Research.BraidedSymDeriv.BraidedSymmetric
