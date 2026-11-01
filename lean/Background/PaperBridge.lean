import Mathlib
import Background.Basic
import Research.BraidedSymDeriv.TwistedCommutative

/-!
# The catalogue and the paper's own development

The modules of `Background/` restate the notions of the paper's bibliography in
their own namespace `Background`, so that each reference can be read and checked on its
own. This module proves that the catalogue's Leibniz defect is the defect of
`TwistedCommutative.lean`, where the paper's §3 computations live, and that the
paper's identity (3.2) is that module's cocycle identity. Neither bridge is a new
assumption: both are definitional.

Only `TwistedCommutative.lean` is bridged here. `Paper.lean` is being
restructured by the paper session — it no longer defines `Der`, `JDer`, `LieDer`
or `innerDer`, and `BraidedSymmetric.lean` has just moved its contents into the
namespace `BraidedSymDeriv` — so a bridge from `Background.Der` to the paper
development's derivation condition would make this commit depend on uncommitted
work. It should be restored, as `Background.PaperBridge.der_iff`, once that refactor is in.

## Main results

* `Background.PaperBridge.leibnizDefect_eq`: the catalogue's defect is `TwistedCommutative`'s.
* `Background.PaperBridge.leibnizDefect_cocycle_eq`: the paper's identity (3.2) is
  `TwistedCommutative.leibnizDefect_cocycle`.
-/

namespace Background.PaperBridge

open Background

/-- In a commutative ring the catalogue's defect is the defect of
`TwistedCommutative.lean`. -/
theorem leibnizDefect_eq {A : Type*} [CommRing A] (D : A →+ A) (a b : A) :
    Background.leibnizDefect D a b = _root_.leibnizDefect (fun x => D x) a b := rfl

/-- The paper's identity (3.2) is `TwistedCommutative.leibnizDefect_cocycle`. -/
theorem leibnizDefect_cocycle_eq {A : Type*} [CommRing A] (D : A →+ A) (a b c : A) :
    a * _root_.leibnizDefect (fun x => D x) b c
        - _root_.leibnizDefect (fun x => D x) (a * b) c
        + _root_.leibnizDefect (fun x => D x) a (b * c)
        - _root_.leibnizDefect (fun x => D x) a b * c = 0 :=
  _root_.leibnizDefect_cocycle (fun x => D x) a b c

end Background.PaperBridge
