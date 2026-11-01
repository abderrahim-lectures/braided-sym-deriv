import Research.BraidedSymDeriv.References.Basic
import Research.BraidedSymDeriv.References.Reduced
import Research.BraidedSymDeriv.References.Nonassoc
import Research.BraidedSymDeriv.References.FDerivation
import Research.BraidedSymDeriv.References.JordanHerstein
import Research.BraidedSymDeriv.References.JordanProduct
import Research.BraidedSymDeriv.References.Involution
import Research.BraidedSymDeriv.References.AlphaDerivation
import Research.BraidedSymDeriv.References.Hochschild
import Research.BraidedSymDeriv.References.BraidedDerivation
import Research.BraidedSymDeriv.References.PaperBridge

/-!
# The catalogue of the paper's sixteen references

One module per reference cluster of `paper/braided-sym-deriv.tex`. Each module is
self-contained apart from `Basic.lean`, carries the citation of the passage of
the paper it serves in its header, and distinguishes what it *proves* from what
it *assumes*: the deep theorems of Herstein 1957, Cusack 1975 and Brešar 1988 are
`Prop`-valued definitions listed as hypotheses by everything that uses them.

| Module | References |
|---|---|
| `Basic` | the shared notions: Bresar 1988's ring conditions, Herstein's Jordan product, Hochschild's defect, Weibel's principal derivations |
| `Reduced` | Chambert-Loir 2021, 1.4.12 |
| `Nonassoc` | Jacobson 1937, Part I; Martindale 1964, p. 183 |
| `FDerivation` | Benkovič 2015, §1; Beidar–Brešar–Chebotar–Martindale 2001, Theorem 4.3 |
| `JordanHerstein` | Herstein 1957; Cusack 1975; Brešar 1988 |
| `JordanProduct` | Jordan–von Neumann–Wigner 1934, p. 64; Brešar–Zelmanov 2025, Example 2.1 |
| `Involution` | Herstein 1976, §1.2 |
| `AlphaDerivation` | Hosseini–Mohammadzadeh Karizaki 2019, §1 |
| `Hochschild` | Hochschild 1945, §§2 and 4; Weibel 1994, §§9.1 and 9.2 |
| `BraidedDerivation` | Różański 1996, §2; Huru 2006, §4.1 |
| `PaperBridge` | the comparison with the paper's own development in `Paper.lean` |

Build with `lean/build_references.sh`; see `results/references-formalization.md`
for what is proved, what is assumed, and why.
-/
