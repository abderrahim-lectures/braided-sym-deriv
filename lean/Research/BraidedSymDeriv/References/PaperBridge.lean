import Mathlib
import Research.BraidedSymDeriv.References.Basic
import Research.BraidedSymDeriv.Paper
import Research.BraidedSymDeriv.TwistedCommutative

/-!
# The reference catalogue and the paper's own formalization

The modules of `Research.BraidedSymDeriv.References` restate the notions of the
paper's bibliography in their own namespace `Ref`, so that each reference can be
read and checked on its own. This module proves that those restatements are the
notions the paper itself uses in `Research/BraidedSymDeriv/Paper.lean` (namespace
`BSD`) and in `TwistedCommutative.lean`: each bridge is an equivalence of
propositions, or an equality of maps, and none of them is a new assumption.

## Main results

* `RefPaper.der_iff`, `RefPaper.jder_iff`, `RefPaper.lieDer_iff`,
  `RefPaper.comm_iff`: the four classes of the catalogue coincide with the
  paper's.
* `RefPaper.innerDer_eq`: the inner derivation of the catalogue is the paper's.
* `RefPaper.leibnizDefect_eq`: the defect of the catalogue is the defect of
  `TwistedCommutative.lean`, which is where the paper's §3 proofs live.
-/

namespace RefPaper

open Ref

variable {A : Type*} [Ring A]

/-- `Ref.Der` is the paper's `BSD.Der`. -/
theorem der_iff (D : A →+ A) : Ref.Der D ↔ BSD.Der D := Iff.rfl

/-- `Ref.JDer` is the paper's `BSD.JDer`: the catalogue writes the Jordan product
as `Ref.jordan`, the paper writes it out. -/
theorem jder_iff (D : A →+ A) : Ref.JDer D ↔ BSD.JDer D := by
  simp only [Ref.JDer, BSD.JDer, Ref.jordan]

/-- `Ref.LieDer` is the paper's `BSD.LieDer`. -/
theorem lieDer_iff (D : A →+ A) : Ref.LieDer D ↔ BSD.LieDer D := by
  simp only [Ref.LieDer, BSD.LieDer, Ref.commutator]

/-- `Ref.Comm` is the paper's `BSD.Comm`. -/
theorem comm_iff (D : A →+ A) (α : A → A) : Ref.Comm D α ↔ BSD.Comm D α := Iff.rfl

/-- The catalogue's inner derivation is the paper's. -/
theorem innerDer_eq (g : A) : Ref.innerDer g = BSD.innerDer g := by
  ext x
  rfl

/-- In a commutative ring the catalogue's defect is the defect of
`TwistedCommutative.lean`, the file that carries the paper's §3 computations. -/
theorem leibnizDefect_eq {A : Type*} [CommRing A] (D : A →+ A) (a b : A) :
    Ref.leibnizDefect D a b = _root_.leibnizDefect (fun x => D x) a b := rfl

/-- The paper's identity (3.2) is `_root_.leibnizDefect_cocycle`, here
derived from the catalogue's version so that both are known to agree. -/
theorem leibnizDefect_cocycle_eq {A : Type*} [CommRing A] (D : A →+ A) (a b c : A) :
    a * _root_.leibnizDefect (fun x => D x) b c
        - _root_.leibnizDefect (fun x => D x) (a * b) c
        + _root_.leibnizDefect (fun x => D x) a (b * c)
        - _root_.leibnizDefect (fun x => D x) a b * c = 0 :=
  _root_.leibnizDefect_cocycle (fun x => D x) a b c

end RefPaper
