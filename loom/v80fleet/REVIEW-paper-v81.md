# REVIEW — *Braided-Symmetric Derivations of Algebras*, v81

Full-width review (rule 19). Artifact: branch `fix/v81-paper-fixes`, tip `338c593`, `\paperversion` 81,
released `pdf/braided-sym-deriv-v81.pdf`. Baseline `main` @ `6919724` (v80).

Method: one Ultramath swarm, `smw1yoi3w`, sixteen members, one perspective each, the sixteen from
`loom fleet --runbook`. Each member registered its perspective as its direction, wrote its own file at
`.scratch/review/v81/<perspective>.md`, and was barred from reading `results/review-*` or another
member's file before writing its own findings. The judge (this file) re-derived every accepted finding
from the source before accepting it.

Status: **in progress** — verdicts are added as members report.

## Findings, deduplicated by locator

| # | locator | finding | perspective | severity |
|---|---|---|---|---|
| R-01 | `lean/BACKGROUND.md:3` | "v80 (`\paperversion` 80)" — stale pin on a v81 branch whose own convention is that every pin moves with the release | p12 release | MINOR |
| R-02 | `Paper.lean:2` | "Results of … v80" — same stale pin | p12 release | MINOR |
| R-03 | `Remark46.lean:5` | "(v80)" — same stale pin | p12 release | MINOR |
| R-04 | `tools/papercheck.py:97,101` | reads `\paperversion` and `$jobname` and never compares them; a stale jobname renames the build artefact, and since the printed label comes from `\paperversion` both text comparisons still pass. Mutation-tested by the reviewer: jobname v80 with version 81 prints GATE PASS | p12 release | MAJOR (gate) |
| R-05 | README changelog, v81 entry | "No theorem, hypothesis, proof or example changes" is contradicted by N5, N7 and N10, which edit sentences inside proofs | p12 release | MINOR |
| R-06 | README table, `pdf/` row | "the PDF of the latest release" while the directory holds one per version | p12 release | MINOR |
| R-07 | `paper/build.log` | untracked and unignored (`paper/build/` is ignored, the log beside it is not) | p12 release | MINOR |

## Positive results worth keeping

* **p12 release, independent rebuild:** `paper/` rebuilt in the reviewer's own tree gives 13 pp,
  395 921 bytes and `pdftotext` text identical to the released `pdf/braided-sym-deriv-v81.pdf` — the
  release is not stale. Pins agree at 81 in `\paperversion`, `latexmkrc`, the artefact name,
  `formalization.yaml` and README; 0 overfull, 0 underfull, 0 undefined, 0 Type 3 fonts; 17/17
  bibliography keys resolve and README's list matches `\bibitem` order; all eleven repairs are present
  at the recorded lines and in the PDF; every `pdf/*.pdf` prints its own version.

### p4 paper-lean (m6) — 0 CRITICAL, 4 MAJOR, 5 MINOR, all type-checked with `#check`/`#print` under Lean 4.36.0-rc2

| # | locator | finding | severity |
|---|---|---|---|
| R-08 | `BraidedSymmetric.lean:60` vs paper 189–191 | Definition 2.1 is not stated at the paper's carrier: the Lean class takes a binary `σ : A → A → A`, with no `A ⊗ A`, no involution. **Known and disclosed** (Paper.lean header, `RESULTS.md` "strictly narrower in general"), but disclosed in a docstring while the mismatch is in a numbered definition. Fix proposed: a `BSDerSigma` at the tensor carrier plus a bridge for the four standard `σ` and `σ_α` | MAJOR (record) |
| R-09 | `Remark24.lean:103` vs paper 264–267 | `natural_form` is the paper's *Second* step only; the "First" determination step (an endomorphism is determined by its value on `K²`) is not stated, so "these are the only natural involutions" is machine-checked at `V = K²` only | MAJOR (record) |
| R-10 | paper 269–271 | the multiplication-using involution `a⊗b ↦ ab⊗1` and the clause "which is none of the four entries" have no Lean counterpart; `StructureUsing.bsder_eq_bot` covers only the `F₅[ε]/(ε²)` computation | MAJOR (record) |
| R-11 | paper 619–622 | the ℍ dimensions are half formalized: the BSDer side is `class_is_line`/`bsder_eq_line`, but nothing states `Der(ℍ)^α = ℝ·ad_I` or `dim Der(ℍ) = 3`, and the `α = id` case has only JDer = Der, not "3 for both" | MAJOR (record) |
| R-12 | paper 427 vs `AntiAutomorphism.lean` | the anti-automorphism inner-derivation criterion `g + α(g) ∈ Z(A)` has no Lean counterpart, although `RESULTS.md`'s Rem 3.3 row cites `der_twisted_iff_comm_anti` against it (that declaration is the paper's line 419, not 427) | MINOR |
| R-13 | paper 238 vs `General.lean:280` | `char_two_strict` is the instance `A = ℤ/2`, not "for every `A ≠ 0`" | MINOR |
| R-14 | `Paper.lean:168` | the declaration carrying the paper's name for Corollary 3.5 is the *conditional* form; the hypothesis-free one is `corollary_3_5_unconditional`, so a name-to-name audit reports a spurious hypothesis | MINOR |
| R-15 | `TwistedCommutative.lean` / `Closures.lean` | Proposition 4.4's two non-inclusions are components, not a theorem: no declaration states `D1 ∈ ADer ∧ D1 ∉ BSDer^α` or `dd ∈ BSDer^α ∧ dd ∉ ADer` | MINOR |

Two corrections to the record from this lane: `#print IsReduced` is `∀ x, IsNilpotent x → x = 0`, i.e. the paper's *reduced* exactly — the ledger's "stronger" note refers to the sharpened hypothesis at the end of Theorem 4.1's proof, not to the theorem's binder; and `corollary_3_5_anti_unconditional` does not assume involutivity of `α` and is sound, because the product `xy + α(xy)` does not need it.

### p5 lean-audit (m5) — 0 CRITICAL, 4 MAJOR, 3 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-16 | `tools/papercheck.py:208–210` | the source trust scan matches `\bsorry\b`, `\bnative_decide\b` and `^\s*axiom\b` only: **`admit` is not matched**, and an `axiom` indented inside a namespace body is missed. No live use today, so the gate is not currently passing over one | MAJOR (gate) |
| R-17 | `lean/check_axioms.lean` | the audit prints a curated list, so it cannot fail on a declaration it does not name; 32 of the 143 theorem/lemma declarations `RESULTS.md` cites are never axiom-printed, and an empty or mistyped list yields a clean run | MAJOR (gate) |
| R-18 | `Closures.lean` | imported by `check_axioms.lean:23` and a `lakefile.toml` root, but no `#print axioms` line names a `Closures.*` declaration, so its pair-closure lemmas are never audited (the reviewer's "imported by nothing" was wrong; this is the corrected form) | MAJOR (gate) |
| R-19 | `native_decide` budget | the whitelist holds 5 footprints but only the 2 `Triangular.lean` sites can produce one; `clash_test.lean` is never compiled; two miscounts in `RESULTS.md` | MINOR |

### p16 open-sweep (m4) — 0 CRITICAL, 0 MAJOR, 4 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-20 | paper line 393 (v81 repair N10) | "it is used again, later, for the splitting `A = A_+ ⊕ A_-`" — the splitting is introduced at line 292, *before* the sentence, so "later" points backwards. My own repair; fix: "and it is also what makes the splitting `A = A_+ ⊕ A_-` of Section 3 work" | MINOR |
| R-21 | paper line 151 | "each of the questions below" — the paper poses no question | MINOR |
| R-22 | paper line 340 | promises the defect for "the other classes"; one is given, the other is 285 lines away and unlinked | MINOR |
| R-23 | paper | two named notions are introduced and never referred to again | MINOR |

Pointer audit, clean: 23 labels, 78 `\ref`/`\eqref` sites, 0 dangling, 0 type-word mismatches, 0 hardcoded "Theorem N" outside citation brackets, 0 `??` in the released PDF, the 16 numbered items printing 2.1–2.5 / 3.1–3.5 / 4.1–4.6, all 17 bibitems cited.

### p11 remarks (m3) — 0 CRITICAL, 0 MAJOR, 5 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-24 | paper line 270 (Remark 2.5) | "they add no class to the dictionary" is asserted without the step that makes it true: in characteristic 2 the family gives `x·_σ y = c(x∘y)` with `c = 1+λ`; for `c ≠ 0` the Leibniz rule is the Jordan rule scaled by a unit, so the class is `JDer`, and for `c = 0` the product vanishes and every map qualifies | MINOR |
| R-25 | paper line 207 (Remark 2.2) | asserts that braided derivations are "a different notion" without stating the other definition, so the distinction is checkable only by opening Różański §2 / Huru Def. 14 | MINOR |
| R-26 | paper line 431 (Remark 3.3) | "twisted outer derivations" is defined and never used again (second sighting, with p16's F4) | MINOR |

Remark 4.6 was recomputed a third time here, independently, and agrees: associativity on all 64 triples, α an involutive automorphism, `D ∈ BSDer^α \ Der^α`, `dim = 3` and `2`, `E(v,w) = −t`, `E = 0` on every mixed pair, `(v+w)² = 0`, and the three-way equivalence re-derived. The quaternion numbers over ℚ, the commutant over `F₂…F₇`, the `F₅[ε]/(ε²)` brute force to `{0}`, and Remark 3.3 with its use in Example 4.5(a) all reproduce.

*Caveat recorded, not adopted:* the reviewer calls the `dim V ≤ 1` clause of line 266 redundant after repair N8. It is redundant at `dim V = 1` and still needed at `dim V = 0`; a style call, not a fix.

### p15 open-sources (m15) — 0 CRITICAL, 0 MAJOR, 4 MINOR

First pass went to the open web and skipped `loom-pack/references/`; four findings were withdrawn on
the second pass with the on-disk quotes that refute them (Hochschild's Definition 2.1, Benkovič's
Remark 1.4, JvNW p. 64, Jacobson's "Part I"). What survives:

| # | locator | finding | severity |
|---|---|---|---|
| R-27 | `tools/`-independent | line 329 cites Weibel §1.1 alone for `HH^n(A,A)`; the Hochschild complex itself is §9.1. Recorded as *arguable*, not a defect: §1 is "Chain Complexes" (p. 1) where `H^n = Z^n/B^n` is defined, §9.1 is the Hochschild complex (p. 300), and the sentence defines the cocycle quotient | MINOR |
| R-28 | bibliography 644–697 | no entry carries a DOI or stable identifier; worst for Huru, whose printed EMIS address 403s to zbMATH | MINOR (style) |
| R-29 | library file name | `results/refs/.../Jordan derivations of prime rings (1958).txt` says 1958; the article is Proc. AMS 8 (1957) 1104–1110. A library-file nit, not the paper's | MINOR (record) |

**OPEN-1 corrected by the judge:** Pierce 1982 is *not* unreadable. The owner supplied it as the
gitignored `.djvu` at the repository root (446 pages, OCR text layer); `djvutxt` from the unpacked
Debian packages reads it. §4.4 (p. 61), §3.5 (p. 49) and §12.6 (p. 230) are **correct**; §3.5 at line
500 is **incomplete** for separability, which is §10.7 (p. 190) — finding N11 of the v81 repairs.

Verified with quotations at every cited place: the other sixteen sources, and all seventeen
bibliographic records against Crossref. No bibliographic error found.

### p7 abstract-intro (m7) — 0 CRITICAL, 0 MAJOR, 3 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-30 | paper line 154 | the appositive "those that use nothing of `A` beyond its `K`-vector space" does not pick out four maps in characteristic 2: Remark 2.5 says `λ·id + (1+λ)·τ` are natural too, so there are `|K|` of them. Mitigation, which is why this is wording and not a false statement: the paper's own defence is that the extra family adds no class (its product is `(1+λ)(x∘y)`), so "structure-free" is being used for the four *entries*. My N1 repair fixed the `dim ≤ 1` clause and left this | MINOR |
| R-31 | paper line 151 | "the questions below" has no referent — the paper poses no question. Second sighting with p16 | MINOR |
| R-32 | paper line 431 | "twisted outer derivations" appears in no abstract, keyword or contribution sentence. Third sighting (p11, p16) | MINOR |

Cleared, and worth recording: line 99's "the results below need three notions" is true as printed, because Herstein's Theorem 3.1 as stated at line 104 uses primeness. It reads like an overclaim and is not one.

The **abstract** was audited sentence by sentence against the body for the first time in this record, with the example-based claims re-verified in exact arithmetic on six algebras including `M₂(F₂)`: every sentence names a numbered result whose hypotheses and conclusion match it.

### p1 statement-truth (m1) — 0 CRITICAL, 0 MAJOR, 0 MINOR

No false numbered statement in v81. All sixteen numbered results re-derived by hand and recomputed
by exact linear algebra over `F₂, F₃, F₅, F₈₁, ℚ`.

* **Theorem 4.1 on the paper's own imperfect-field family**, independently: `K = F₃(s)`,
  `L = K[x]/(x³ − s)`, `A = L × L`, `α` the swap — `dim BSDer^α = dim Der^α = 3`, `A` reduced.
  This confirms the instance added by v81's N2 and gives its dimension, which the sentence does not
  claim.
* Corollary 3.5 beyond the commutative cases: `M₂(F₃)`, `M₂(F₃) × F₃`, `M₂(F₅) × F₅`.
* Every printed dimension in Examples 2.3, 4.2, 4.3, 4.5, Proposition 4.4 and Remark 4.6 reproduces,
  including `dim BSDer^α = 3`, `dim Der^α = 2` and the quaternion values 1, 1, 3, 3.

**Cleared, do not re-flag** (each has been raised as a defect by an earlier pass): line 238's
`D(1) = D(1·1) = 2D(1) = 0` (valid — it is `D(1) = 2D(1)` in an additive group, so it cancels in
every characteristic); Example 4.5(b)'s "two-dimensional" in characteristic 2 (`D(1) = 0` forced by
unitality, `D(ε)` free); and line 500's imperfect-field example, where `Der(L)` is 3-dimensional and
the paper claims only non-vanishing.

Reducedness of `x³ − s` is argued numerically (generic dimension by minimising over `s ∈ F₈₁`,
degree bound `72 < 81`) and is labelled as numerical evidence, not as proof.

### p9 edge-cases (m9) — 0 CRITICAL, 0 MAJOR, 3 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-33 | paper line 443 (Corollary 3.5) and abstract line 69 | "2-torsion-free semiprime `K`-algebra" is not a condition on `A`: if `char K ≠ 2` it is automatic, and if `char K = 2` then `2·1_A = 0` forces `A = 0`, so the corollary is *vacuous* in characteristic 2 while the abstract reads as if it were covered. Fix: say `char K ≠ 2` | MINOR |
| R-34 | paper lines 460, 344 | "unital" is decorative in Theorem 4.1 and Proposition 3.2 — no step uses `1_A` — unlike Remark 3.3, where it is load-bearing. The paper says so only of the residual-identity computation at line 393 | MINOR |
| R-35 | paper lines 292–297 | in characteristic 2 the "symmetric" and "skew" parts coincide (`A₊ = A₋ = A`), which is exactly why the splitting cannot exist there; the text defines the two sets and says the splitting needs 2 invertible, but never says they coincide | MINOR |

Edge-case catalogue, all reproducing under exact `F_p`/`ℚ` linear algebra: the zero algebra, `dim 1`, the
char-2 dictionary, Example 4.2 (also over `F₃`), 4.3, 4.5(a) and (b) in both characteristics, Proposition 4.4's
two witnesses, Remark 4.6's `3` and `2` with `E(v,w) = −t`, the quaternions, Remark 2.5's `F₅` case, and line
269's idempotent involution. Load-bearing by test: 2-invertibility, reducedness (sharpened `A₋` form
corroborated on a non-reduced algebra), and `Dα = αD`. Commutativity is *not* needed at ℍ, as the paper says.

### p2 proofs (m2) — 0 CRITICAL, 0 MAJOR, 3 MINOR

No false step, no unstated-but-needed hypothesis and no circularity in any numbered proof of v81, nor in the
argued remarks 2.5, 3.3, 4.6. Every step tagged with the side condition it consumes; every displayed identity
re-derived and then machine-checked exactly.

| # | locator | finding | severity |
|---|---|---|---|
| R-36 | paper line 527 (Example 4.3) | after the three basis pairs, the argument treats "a pair with `e` in one entry", and `e = p + q` is **not** a basis element — so that half is checked on a spanning set, which is legitimate only by bilinearity, a reduction the paper states at 517 and 606 but not here. (The reviewer's premise that `(p,p),(q,q),(p,q)` are not basis pairs is wrong: `{p,q}` is a basis.) | MINOR |
| R-37 | paper lines 483, 488 | "the pairs `(zx,y)` and `(z,xy)` lie in `A₋`" — a pair is not an element; what is meant, and what Theorem 4.1 turns on, is that both entries lie in `A₋` | MINOR |
| R-38 | paper lines 617–618 | two compressed one-liners: `(Ad_u)² = id` forces `u² ∈ ℝ`, hence `u` pure imaginary or the identity; and `u q u⁻¹ = q'` gives conjugacy of the *automorphisms* only through `Ad_u Ad_q Ad_u⁻¹ = Ad_q'` | MINOR |

**v80's N5/N7/N10 re-audited by a reviewer who did not write them: correct as printed**, against the residual
identities at 384–391 for `D` not commuting with `α` in `F₃` and `F₅`, both kinds of `α`, zero mismatches.
Also checked: the cocycle identity (3.3), the `E_a` identity at 625, the Jordan criterion at 341, every printed
dimension (3/2, 1/1, 3/3, 1/3, 0; quaternion 1, 1, 3, 1; char 2: `End` 4, `Der` 2), the sharpened statement of
line 496 on ℍ and ℍ×ℍ in three `α` modes, and seven reduced finite-field instances giving `0 = 0`.

### p13 open-backlog (m13) — 0 CRITICAL, 2 MAJOR, 5 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-39 | `lean/RESULTS.md:32` vs `lean/FORMALIZATION-BACKLOG.md` B3 | RESULTS says the quaternion transport "is not formalized" while B3 is closed on `QuaternionTransport.class_transport`, which the reviewer re-elaborated and found to be a theorem over any division ring. Two files that both claim to be the ledger disagree | MAJOR (record) |
| R-40 | `FORMALIZATION-BACKLOG.md` B3, B5 | marked done/DONE while their bodies still read "what is missing (a)(b)… Plan:…" and "the first two are BLOCKED" — a closed item that still describes the work as open | MAJOR (record) |

**Caveat recorded by the judge:** the `lean/` tree audited carries another session's uncommitted edits — eight
modules (including `QuaternionTransport`) are untracked at HEAD, and `RESULTS.md`, `lakefile.toml`,
`check_axioms.lean` are modified-uncommitted. R-39 and R-40 are therefore true of the working tree and may not
be true of any committed branch; the fix belongs to whoever commits those modules.

**Closed by this lane, and it matters:** the toolchain pin. All 42 root modules elaborate under
`v4.36.0-rc2` against Mathlib `bf20166d`, 9/9 pins match, `check_axioms.lean` re-run gives **214 footprints, all
inside `{propext, Classical.choice, Quot.sound}`, no `sorryAx`**. The pin was an open "unverified" line in the
record since v63.

Also: `A = ℍ × ℍ` with the factor swap gives `dim BSDer = dim Der^α = 3` under exact rational linear algebra,
solver validated on `Der(ℍ) = 3` and `Der(ℍ × ℍ) = 6` — the third independent computation of that instance in
this review. Every B1–B5 closure was verified for statement, hypotheses and axiom footprint, including
`WedderburnReduced`'s `[Fintype K]` being present and essential. The odd–odd case remains open.

### p14 open-lean, upstream (m11) — 0 CRITICAL, 0 MAJOR, 7 MINOR

The only lane that left the repository. It wrote `.ultramath/smw1yoi3w/m11/p14/AlgebraIngredients.lean`
(138 lines, Mathlib only, **verified by the judge: no `sorry`/`admit`/`axiom`/`native_decide`**) and proved at
Mathlib generality: `muSigma_comp_sigma` (the paper's commuting triangle) from `σ ∘ σ = id` alone;
`sigmaAlpha_involutive` from `α ∘ α = id`; `bsd_iff_square`, the bridge between the square and pointwise forms
for an arbitrary `σ`; and `prop32_aut`, Proposition 3.2(i) as an iff over an arbitrary ring with `α` **any** ring
homomorphism — no involution, no 2-invertibility, confirming the paper's own sentence at line 393 from the other
end.

| # | locator | finding | severity |
|---|---|---|---|
| R-41 | paper line 291 | `β ⊗ β = id ⇒ β = λ•id` needs the pure-tensor cancellation `u⊗v = u'⊗v, v ≠ 0 ⇒ u' = c•u`, which Mathlib lacks (six-line proof supplied). Beyond that, "with a scalar independent of `x`" needs `β` **additive**: cancellation alone gives `β(x) = c_x x`, and independence comes from `β(x+x') = β(x) + β(x')` on two independent vectors. Available, because the paper calls `β` an endomorphism — but not said | MINOR |
| R-42 | `Derivation` in Mathlib | the carrier wants a commutative semiring, so `Der(A)` for non-commutative `A` — used at ℍ and at Remark 4.6's algebra — has no direct carrier and needs the bimodule setup | MINOR (formalization) |
| R-43 | paper line 267 | Remark 2.5's "direct computation with the 2 × 2 matrices" names no test maps, so a formal version must choose the spanning set — the same unstated reduction p2 found at Example 4.3 | MINOR |

Attempted and not done, correctly recorded as such: the `Aᵐᵒᵖ` twin of Proposition 3.2. Note for the next pass:
the anti-automorphism case is `α : A → Aᵐᵒᵖ`, and the paper's (ii) is the case where the product is reversed, so
the full opposite-ring theory should not be needed.

### p8 definitions (m8) — 0 CRITICAL, 0 MAJOR, 11 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-44 | tex 111–113, used at 190 and 217, pointer at 307 | the display defining `x ·_σ y = μ(x⊗y) + μ(σ(x⊗y))` is **unnumbered** and sits in the **Introduction** (Section 2 starts at line 159), yet line 307 says "as in Section 2", which never defines the product. Label the display and repoint 307 | MINOR (pointer) |
| R-45 | line 268 | `μ` is the multiplication map from line 108 and also a scalar in `λ² + μ² = 1` | MINOR |
| R-46 | lines 154 (×6 uses of the term) | "structure-free" is never defined; the gloss at 154 is the closest thing and slips in characteristic 2 (see R-30) | MINOR |
| R-47 | lines 612–618 | `\bar u`, the quaternion norm, `semisimple` and `radical` are used undefined in the Wedderburn paragraph | MINOR |
| R-48 | line 534 | "twisted derivations" shifts referent | MINOR |
| R-49 | line 154 | "in characteristic 2" now appears twice in the sentence — the second occurrence carries the scope, the first was already there. A redundancy introduced by my own N1 repair | MINOR |

Recorded as **intended, not defects**: line 622's `BSDer_{σ_α}(ℍ)` without `^α` compares the whole class with
`Der(ℍ)`; `E_a` at 624 is `E − Eᵀ` *and says so* ("twice the antisymmetric part of Section 3"), so the two
normalisations are disclosed; and "`Der_α(A)` is not defined" at 588 states the definition's requirement, which is
why Example 4.5(a) uses the transpose.

Checked correct: the full definition inventory with locators, every `\ref`/`\eqref` target verified semantically
(only line 307 wrong — the same pointer p16 found from the traceability side), and the definitions checked against
the printed dimensions of Examples 2.3, 4.2, 4.3, 4.5, Proposition 4.4, Remarks 2.5 and 4.6 and the quaternion
numbers.

### p3 compute (m14) — 0 CRITICAL, 0 MAJOR, 3 MINOR

**All 132 exact checks reproduce the paper's integers; no printed number in v81 is false.** Solver validated
before use by exhaustive enumeration on `3⁹` and `2⁴` and against hand-derived answers.

| # | locator | finding | severity |
|---|---|---|---|
| R-50 | line 271 | `σ = (T⊗T⁻¹)∘τ` is never displayed; `dim BSDer_σ = 0` is right under **both** readings of the composite, and the reviewer supplies `σ` on the basis so the entry can be audited | MINOR (reproducibility) |
| R-51 | line 608 | the dimensions 3 and 2 are right but no basis is shown; explicit bases in `1, t, v, w` over `F₃` supplied | MINOR (reproducibility) |
| R-52 | lines 619, 622 | at ℍ the numbers are right; the generator is `ad_i`, and the sharper fact holds: `Der(ℍ)^α = BSDer_{σ_α}(ℍ)^α = BSDer_{σ_α}(ℍ)` as spaces | MINOR (precision) |

Theorem 4.1 verified on `F₅ × F₅`, `F₉/F₃` (Frobenius) and `F₂₅/F₅`, `0 = 0` each; Proposition 3.2 (the reviewer
wrote "Cor 3.2") on `F₅ × F₅` and `M₂(F₃)` with the transpose; Examples 2.3, 4.2, 4.3, 4.5, Proposition 4.4 and
Remark 4.6 all reproduce.

*Warning recorded a third time:* Remark 2.5's centraliser is 2-dimensional only when one imposes commuting with
the **span** of `{f⊗f}` (10-dimensional); the four matrix units `E_ij⊗E_ij` alone give 5.

Not checked, correctly declared: `K[t]` with `α(t) = −t`, the function-field instances, and the conjugations of ℍ
symbolically — the three places no finite computation reaches.

### p10 examples (m10) — 0 CRITICAL, 0 MAJOR, 2 MINOR

| # | locator | finding | severity |
|---|---|---|---|
| R-53 | paper line 527 (Example 4.3) | the check names three of the four ordered basis pairs of `{p,q}`; `(q,p)` is unlisted. Here it follows — `A` is commutative and `α` an involution, so `x·_σ y = y·_σ x` and the two sides at `(q,p)` equal those at `(p,q)` — but it is not said. (p2's finding at the same line is a *different* defect: the later half of the argument moves to a spanning set.) | MINOR |
| R-54 | paper line 271 | "a direct computation on the two basis elements gives `BSDer_σ(A) = {0}`" — a space of maps needs the four ordered pairs and all four coordinates of `D`. **Third independent sighting** (with p4 and p16) | MINOR |

Reproduced exactly: Example 2.3 (non-associative, no unit); 4.2 (`D` twisted on all sixteen pairs, not a derivation,
`E(u,v) = uv`, `z² = 0`); 4.3 (`dim BSDer^α = 1`, `Der = 0`); 4.5(a) transpose and `ad_g`, 4.5(b) `1,1,1,1` in
characteristic `≠ 2` against `End 4` and `Der = ADer = 2`; Remark 2.4's four products and the char-2 collapse;
Remark 2.5's centraliser in characteristics 0, 2, 3, 5, the `λ·id + (1+λ)·τ` family, and `{0}` on `F₅[ε]/(ε²)`;
Remark 4.6 entire (64 triples, `3` and `2`, `E_D(v,w) = −t`, `(v+w)² = 0`); ℍ at `3`, `1 = 1 = 1 < 3`, and
`3/3/3` for `α = id`.

---

## The sixteen verdicts

| p | perspective | verdict | findings |
|---|---|---|---|
| p1 | statement-truth | ok | 0 · no false numbered statement; all 16 re-derived and recomputed; three earlier "defects" cleared |
| p2 | proofs | ok | 3 minor · no false step, no unstated-needed hypothesis, no circularity; N5/N7/N10 re-audited correct |
| p3 | compute | ok | 3 minor · all 132 exact checks reproduce; no printed number false |
| p4 | paper-lean | ok | 4 major, 5 minor · four numbered results' Lean counterparts are weaker or absent (record) |
| p5 | lean-audit | ok | 4 major, 3 minor · `admit` unscanned; audit is a curated list with no coverage floor |
| p6 | citations | **abandoned** (budget) — lane covered by the judge's own citation pass and by p15 |
| p7 | abstract-intro | ok | 3 minor · the 154 gloss slips in characteristic 2; two thirds sightings |
| p8 | definitions | ok | 11 minor · the `·_σ` display is unlabelled and in the Introduction while 307 points at Section 2 |
| p9 | edge-cases | ok | 3 minor · **Corollary 3.5 is vacuous in characteristic 2** |
| p10 | examples | ok | 2 minor · everything reproduces; one omitted pair, one "two basis elements" |
| p11 | remarks | ok | 5 minor · line 270's "no class" step is missing |
| p12 | release | ok | 6 minor · three pins at v80; **the gate never compares `$jobname` with `\paperversion`** |
| p13 | open-backlog | ok | 2 major, 5 minor · RESULTS vs backlog contradiction; the toolchain pin verified (214 footprints) |
| p14 | open-lean (upstream) | ok | 7 minor · a 138-line Mathlib-only file; the pure-tensor cancellation is missing from Mathlib |
| p15 | open-sources | ok | 4 minor · four own findings withdrawn on the second pass; sixteen sources verified |
| p16 | open-sweep | ok | 4 minor · pointer graph clean; the N10 "later" points backwards |

**Totals: 0 CRITICAL. 15 accepted, 1 abandoned.**

## Consolidated verdict

**The mathematics of v81 is unbroken.** Five independent lanes — statement-truth, proofs, compute, examples,
edge-cases — each returned zero critical and zero major, with Remark 4.6 recomputed three times, the centraliser
trap caught three times, and the residual identities checked in `F₃` and `F₅` against a `D` that does not commute
with `α`.

**The defects are in the record and in the gate**, which is where this paper's risk has always been:

1. `tools/papercheck.py` never compares `$jobname` with `\paperversion`, so a stale jobname renames the build
   artefact and both text comparisons still pass (R-04), and its trust scan does not match `admit` (R-16);
   `check_axioms.lean` prints a curated list with no coverage floor (R-17, R-18).
2. Three Lean pins still say v80 on a v81 branch (R-01–R-03), and `RESULTS.md` contradicts the backlog on the
   quaternion transport (R-39, R-40).
3. Four paper↔Lean statements are weaker than the paper's (R-08–R-11), and one remark's anti-automorphism clause
   has no counterpart although the ledger cites a declaration against it (R-12).

**The paper's own defects are all one-line prose or pointer repairs**, and they are listed as R-05, R-20, R-21,
R-24, R-26, R-30, R-33, R-34, R-35, R-36, R-37, R-38, R-44, R-45, R-47, R-49, R-50–R-54 above. Two of them —
R-20 and R-49 — are defects in v81's own repairs.
