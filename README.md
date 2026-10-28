# Braided-Symmetric Derivations of Algebras

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v56**.

## The idea of the paper

We study braided-symmetric derivations of an algebra over a field. These are maps that satisfy the Leibniz rule for the product symmetrized by an involution of A ⊗ A. The choice of involution decides which derivations appear. The identity involution gives the ordinary derivations when 2 is invertible. The swap gives the Jordan derivations. We then twist the swap by an involutive automorphism. Let the algebra be commutative and reduced, with 2 invertible. Then the twisted maps that commute with the automorphism are exactly the derivations that commute with it. An example with nilpotent elements shows that the reduced hypothesis is needed, and an example in characteristic 2 shows that the invertibility of 2 is needed.

### Contents

1. Introduction
2. Preliminaries and braided-symmetric derivations
3. Twisted involutions and the Leibniz defect
4. Reduced commutative algebras and twisted derivations

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-sym-deriv.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDF of the latest release |
| `lean/Research/BraidedSymDeriv/` | Lean 4 files that check computations and lemmas of the paper (mathlib only) |

Build the paper with `cd paper && latexmk -pdf braided-sym-deriv.tex`. Build the Lean files with `cd lean && lake build`.

## Change log

One entry per released version, newest first. Each version is also a tag of this repository.

- **v56** (2026-10-28): the sentence that named the companion paper jordan-lie-symmetrized is removed from the introduction; braided-sym-deriv does not cite it. Five references to a removed section label (printed as Section ??) now point to Section 2. No claim changes.
- **v55** (2026-10-28): sections merged and balanced (the preliminaries and the definition form one section; four sections remain), the f-derivation recall, the Weber formula, the Benkovic and Weber references and the tree pictures removed, three commutative diagrams (the symmetry triangle, the Leibniz square, the decomposition of sigma_alpha), the companion paper jordan-lie-symmetrized named in the introduction.
- **v54** (2026-10-28): every section serves the title (owner rule of 2026-10-28). Moved to the new paper jordan-lie-symmetrized: the base change and its Rotman results, the Zhang and Yu theorem with the triangular Jordan corollary, the dual numbers, and Section 6 (antisymmetrized product, Lie derivations, matrix and triangular algebras).
- **v53** (2026-10-27): release gates for v52. Five linking sentences before consecutive environments (body-style rule 11); every notion carries a citation (Weibel 9.1, 9.2, Benkovic 1.1, 1.2) or an ours marker (Rule 5f). No claim changes.
- **v52** (2026-10-27): review pass, five corrections. The introduction says the identity involution gives the derivations only when 2 is invertible; the roadmap limits the Cheung claim to its hypotheses; the remark on triangular algebras says T is not prime because e_1 and e_2 are nonzero; the Jordan-and-Lie remark states char K != 2; the paperversion macro (stale at 46) reads 52. No theorem changes.
- **v51** (2026-10-16): two citations state what their sources say. Weibel is removed from the 1-cochain coboundary formula (Hochschild 1945, Definition 2.1 gives it; Weibel section 9.1 does not). The Li and Wei section 3 sentence now says the section gives a necessary and sufficient condition for every Lie derivation of a generalized matrix algebra to be standard.
- **v50** (2026-10-16): every result recalled from a reference is stated as the source gives it: the source's own kind (proposition, lemma, theorem, corollary, definition), its whole statement, one environment per result, nothing merged or specialized. No claim changes.
- **v49** (2026-10-16): the base-change results are taken from Rotman 2009 (Theorem 3.1, Proposition 3.46, Lemmas 4.85 and 4.86) and the separability criterion from Weibel 1994 (Theorem 9.2.11) instead of Bourbaki 1989 and Hochschild 1945. No claim changes.
- **v48** (2026-10-16): the two recalled results on base change are merged into one theorem tied to Proposition 3.x, to satisfy the Loom coherence check. No claim changes.
- **v47** (2026-10-16): every result from another reference is stated with its citation before use; locators and statements corrected against the sources. No claim changes.
- **v46** (2026-10-15): owner rule that the paper text holds no Lean code: two sentences that named Lean declarations (leibnizDefect_cocycle, twisted_defect_sq_zero), one sentence on a Lean evaluation over F_5 and one that named the Triangular.lean theorems are removed. The Lean files go to the public repository of the paper. No claim of an earlier version changes.
- **v45** (2026-10-14): first Loom run (coherence reviewer, owner rule: every result homogeneous, linked and meaningful): verdict FAIL at v44 with one ISOLATED result, the quoted Theorem 5 of Bresar 1993 (thm:bresar-lie), unused since v37. The theorem environment and the sentence introducing the extended centroid for it are removed; the citations stay in the introduction and the preliminaries.
- **v44** (2026-10-14): machinery only where it shortens a proof (owner rule, now in math-paper-latex/SKILL.md): the two cited facts (F1, F2) of the proof of Proposition prop:base-change are stated in two short items with their locators; the twisted outer derivations of Remark rem:inner-twisted are the quotient BSDer^alpha / Inn_alpha, without the exact sequences, which added words and removed no step;
- **v43** (2026-10-14): homological rewrite (owner: use flat, projective and exact-sequence machinery in proofs and results; Bourbaki Algebra I and Rotman cited): Proposition prop:base-change is stated as an isomorphism of exact sequences and proved by exactness of the extension of scalars (Bourbaki II.7.9 Proposition 18) and Hom base change for finitely generated projective modules (Bourbaki II.4.2 Proposition 2(ii), II.5.1 Proposition 1,...
- **v42** (2026-10-14): third review (an outside referee report, facts checked against the source): Section 6 gains Proposition prop:twisted-lie, the defect description of the twisted antisymmetrized product for an automorphism and an anti-automorphism (parities opposite to Proposition prop:defect);
- **v41** (2026-10-14): the symmetric monoidal framing is dropped (owner: "drop it", after both referees found it unused in every proof) and every symbol of the proof of Proposition prop:base-change is declared at first use (owner report of undefined variables): the paper works with algebras over a field and a K-linear involution sigma of A tensor A;
- **v40** (2026-10-14): second readability pass on the blocks the Jev plain-English step scores under 0.4: five at v39 (007, 031, 036, 042, 062), four at v40 (028, 031, 035, 046; lowest 0.35). The triangular-algebra paragraph of the introduction, the matrix entries of the map D' in the base-change proof and the use of Proposition prop:defect in the commutative theorem are reworded. No claim changes.
- **v39** (2026-10-14): readability pass (owner report that the open plain-English blocks were not worked): eleven blocks scored under 0.4 by the Jev plain-English step at v38, five remain under 0.4 (007, 031, 036, 042, 062; lowest 0.33).
- **v38** (2026-10-14): one meaning per symbol (owner report of a quantifier mismatch between the statement and the proof of Proposition prop:base-change, then a full read of every statement against its proof): permutations are varpi, polynomial coefficients kappa, matrix units e_ij, the trace map theta, nu(lambda) replaces delta(lambda), Martindale Theorem 2 is stated with D, d and t, the proof of Proposition prop:base-change declares D in...
- **v37** (2026-10-14): referee-driven corrections (two isolated referees, full-text citation audit, Lean sync): Corollary cor:triangular-jordan requires a 2-torsion free triangular algebra (T_2(F_2) over Z is a counterexample otherwise); Example ex:twisted-char-two shows 2 invertible is needed in the twisted theorem; JDer is the circ-form space; Wang, Martindale, Cusack and Cheung citations corrected; S_4 sourced to Amitsur and Levitzki;
- **v36** (2026-10-08): two cuts of v35 are undone because they describe the space of derivations (owner review: "it describes/characterizes the space of derivations"): Proposition prop:base-change with its recalls, the finite-dimension remark, the fixed-part paragraph, the complex example and the Bourbaki entry, and Remark rem:inner-twisted. The graded-algebra text (owner's cut) and the Hopf-algebra text (v34) stay out.
- **v35** (2026-10-08): text cut (owner review): the graded-algebra paragraphs left Remark rem:distinction-from-braided; the base-field extension block (Proposition prop:base-change with its recalls, the finite-dimension remark, the fixed-part paragraph and the complex example) and Remark rem:inner-twisted were removed, since the abstract and later sections do not use them.
- **v34** (2026-10-07): Hopf-algebra text cut (owner review): the recall of bialgebras, triangular and Hopf algebras, twists and braided commutative algebras, and the paragraph on Weber's braided Cartan calculus, are removed because no result of the paper uses them; Remark 3.2 keeps the definition of braided derivations and the graded example; no theorem, proof or claim changed
- **v33** (2026-10-07): proof of Proposition 3.8 made self-contained (owner review): the recalled notions (minor, rank, structure constants) stand before the proposition with sources in Bourbaki, Algebra I (Chapter III section 8 no. 5 and no. 8, Chapter II section 10 no. 12); the coefficient formula for Phi_ijk is defined and derived line by line;
- **v32** (2026-10-06): notation clashes fixed (one meaning per symbol: S and T parts of the defect are E_s and E_a, e in the reduced proof is z, the base-change matrix is Theta, the Lie derivation L is D, Wang delta and tau are d and t, the dual-numbers scalar is c), readability pass on the new definition paragraphs, shorter explanation of the dot in sigma_L, and the peripheral literature (Liang, Ghahramani-Ghosseiri-Rezaei, Makhlouf-Stefa...
- **v31** (2026-10-06): Remark 3.2 rewritten and notation clashes fixed (owner review): the remark opens with the comparison, the Hopf-algebra notions and the string-diagram conventions moved to the Preliminaries, and each symbol now has one meaning (S and T parts of the defect are E_s and E_a, e in the reduced proof is z, the base-change matrix is Theta, L is D, Wang delta and tau are d and t, the dual-numbers scalar is c);
- **v30** (2026-10-06): readability pass (owner request, issue 650): about 25 paragraphs rewritten, long formulas moved into displays, sentences shortened and symbols named in words; the simple-English judge leaves 15 of 85 blocks below the mark; no theorem, proof, citation or label changed
- **v29** (2026-10-06): open points of v28 closed (owner review): Chambert-Loir 1.4.12 re-read, the source defines reduced for commutative rings only, so the paper now says commutative algebra; string diagrams introduced from Majid, section 9 before Figure 9.3; condition (vi) of Cheung Proposition 10 stated in words as the proof of the source reads it (an element whose inverse lies in V lies in V); 24 long paragraphs split for readability;
- **v28** (2026-10-06): notions recalled (owner review): sourced definitions added for prime, semiprime, 2-torsion free and primitive rings, idempotent, nilpotent, S_4, extended centroid and central closure, bimodule, multilinear polynomial, additive category, bialgebra and triangular Hopf algebra, braided commutative algebra, Hochschild cochains, crossed homomorphism, the seven conditions for W(X), generalized matrix algebra, Wang U_0;
- **v27** (2026-10-05): simple academic English rule (owner directive, all LaTeX): introduction and preliminaries rewritten as connected narrative, about 50 long sentences split, rare words replaced; no theorem, proof, citation or label changed. Mechanical check passes; Jev passes 38 of 61 blocks (mean 0.45); the 23 dense definition, proof and example blocks score below the pass mark 0.4.
- **v26** (2026-10-02): Rule 5e amended (owner directive): the six quoted results (Bresar 1988 Thm 1, Zhang-Yu Thm 2.1, Alizadeh Thm 3.1, Bresar 1993 Thm 5, Cheung Thm 11, Weibel Lemma 9.2.1) restated in modern notation and language, content unchanged; no claim changed
- **v25** (2026-10-02): Rules 5d and 5e (owner directives: use the literature, never reprove; quote a cited result in full, then use it): Der in JDer cited to Bresar 1988 p. 1003; cited results stated word for word from the PDFs before use (Bresar 1988 Theorem 1, Zhang-Yu 2006 Theorem 2.1, Alizadeh 2009 Theorem 3.1, Bresar 1993 Theorem 5, Cheung 2003 Theorem 11, Weibel Lemma 9.2.1) and used by reference;
- **v24** (2026-10-02): owner directive (uncited claims are fatal): every descriptive sentence outside proofs cited and checked against the source, given a reason, or removed; Weber remark rewritten from Weber 2020 Introduction and equation (3.9); super-derivation, Lie-algebra-object and "conditions differ" sentences removed (no checked source); Herstein "transpose is the basic example" removed (not in §1.2);
- **v23** (2026-10-02): owner review of v22: base field stated; monoidal recall with associator, unitors and Mac Lane symmetry gamma; first-definition citations (Jacobson 1937, Herstein 1957, Martindale 1964, Herstein 1976 for involutions); standard form and the central correction term explained; Prop 3.3 and Cor 3.4 merged into Remark rem:sigma-derivation-classification; new Example ex:not-associative;
- **v22** (2026-09-30): questions and acknowledgments removed (user directive): the closing Further braidings paragraph and Question, its two forward references, and the Acknowledgments section; no claim changed
- **v21** (2026-09-28): sections balanced and \section only (user directives): the twisted-braiding subsection split into Section 4 (Leibniz defect, semiprime case) and Section 5 (reduced commutative case, alpha-derivations); the short closing section is now a run-in paragraph at the end of the triangular section; no claim changed
- **v20** (2026-09-28): abstract rewritten in the "We study" form: braidings and the derivations they give first, then the twisted theorem and its counterexample; no claim changed
- **v19** (2026-09-28): Benkovic Theorem 1.1 citation in Corollary (triangular) limited to 2-torsion free T; new Remark: a derivation is twisted braided-symmetric exactly when it commutes with alpha, so ad_g qualifies exactly when g - alpha(g) is central
- **v18** (2026-09-28): standing assumption moved from a text display into Notation 2.1; Proposition 3.9 given a direct proof with two explicit maps; f-derivations (Benkovič 2015) cited and compared with the twisted braidings; new Theorem (twisted Herstein, commutative reduced case) with Lean-checked key step and Lean-checked counterexample for the nilpotent case; base change Proposition (BSDer commutes with field extension)
- **v17** (2026-09-28): Proposition 3.9 proved by contradiction through the identity E_D - F_D at (epsilon, epsilon); Example 3.10 folded into the proof, per author request
- **v16** (2026-09-28): twisted section merged into Section 3 with Leibniz-defect criterion, transpose witness replaced by Euler derivation, citation locators fixed
- **v15** (2026-09-25): Hochschild section removed (its theorem restated earlier results), triangular section restated as Corollary cor:triangular, orphan definition and example connected
- **v14** (2026-09-24): body rewritten to Journal of Algebra house style (located citations, standing hypothesis, linking sentences), identity-braiding case proved in Lean
- **v13** (2026-09-24): new paragraph on triangular algebras in the Examples section: definition of Tri(A,M,B) and faithfulness; Zhang–Yu 2006 Theorem 2.1 (2-torsion free R, M faithful on both sides: every Jordan derivation is a derivation), checked against the fetched PDF; Cheung 2003 Theorem 11 (every Lie derivation is proper, i.e. standard, under conditions (I) and (II)), read from the fetched PDF; Li–Wei 2015 (Colloq. Math.
- **v12** (2026-09-24): New Definition 2.1 recalls derivation, inner derivation, Jordan derivation (with the exact relation between the `x∘y` and `x^2` forms, and the char 2 commutative case), Lie derivation, and alpha-derivation; recalls Herstein 1957, Cusack 1975, Bresar 1988 (Jordan) and Martindale 1964, Bresar 1993 (Lie, form `d + t`).
- **v11** (2026-09-22): Fixes referee report 03 (v10, 3/3 HOLE FOUND) findings. (a) Added `char K != 2` hypothesis to Proposition 3.4(a)'s identity-braiding half — without it, at char 2 the symmetrized product `x·_id y = 2xy` vanishes identically and `BSDer_id(A)` is every additive map, not `Der(A)`; propagated the hypothesis into the Abstract and Remark 4.4.
- **v10** (2026-09-22): Removed all four Lean/Counterexamples.lean mentions from the paper's prose (abstract, two Introduction sentences, one Example sentence), so the paper no longer names its own formalization tool or file; each sentence keeps the same mathematical claim (witnesses checked exhaustively over the relevant finite algebra).
- **v9** (2026-09-22): Citation + typography fix, no math content changed. Added a verified citation (Makhlouf & Stefan 2024, "On deformation theory of associative algebras in monoidal categories," arXiv:2412.10952) for the deformation-theory literature connection added in v8's Introduction, replacing an uncited claim.
- **v8** (2026-09-22): Content revision, no claims changed. Added a paragraph to the Introduction explaining why the construction is useful (unifies Der(A) and JDer(A) as one construction over two braidings, extends to a third braiding, connects to categorical deformation theory) and an open Question on classifying BSDer_sigma(A) across all braidings.
- **v7** (2026-09-21): Notation pass, no math content changed. Introduced `\BSDer_\sigma(A)` for the set of braided-symmetric derivations for a braiding $\sigma$, `\Der_\alpha(A)` for the alpha-derivations, and fixed $\tau$ as the name for the standard swap braiding.
- **v6** (2026-09-21): Full prose rewrite from scratch, same machine-checked content as v5. Abstract rewritten as a plain narrative paragraph with no citations and no theorem labels.
- **v5** (2026-09-20): Corrected Prop 2.8(b) with machine witnesses both ways (new F2b witness in Counterexamples.lean); deleted §4 (trivial extensions), Cor 3.6, and the incidence-algebra framing in the title; rewrote Example 5.1 honestly; removed fabricated Huru DOI; removed the false local `HH1Trivial` def and corrected the `standardBraiding` docstring; latexmk now writes `build/braided-sym-deriv-v5.pdf` and `lake build` passes
- **v4** (2026-09-17): Fixed fatal errors, removed incorrect incidence algebra section
- **v3** (2026-09-17): Corrected proofs, completed paper
- **v2** (2026-09-17): Renamed terminology from σ-derivation to braided-symmetric derivation
- **v1** (2026-09-17): Initial draft

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. Brešar, M.: Jordan derivations on semiprime rings. Proc. Amer. Math. Soc. 104(4), 1003–1006 (1988).
2. Chambert-Loir, A.: (Mostly) Commutative Algebra. Universitext. Springer, Cham (2021).
3. Cusack, J.M.: Jordan derivations on rings. Proc. Amer. Math. Soc. 53(2), 321–324 (1975).
4. Herstein, I.N.: Jordan derivations of prime rings. Proc. Amer. Math. Soc. 8(6), 1104–1110 (1957).
5. Herstein, I.N.: Rings with Involution. Chicago Lectures in Mathematics. University of Chicago Press, Chicago (1976).
6. Hochschild, G.: On the cohomology groups of an associative algebra. Ann. of Math. 46(1), 58–67 (1945).
7. Hosseini, A., Karizaki, M.M.: Functional equations characterizing -derivations. Acta Sci. Math. (Szeged) 85, 431–440 (2019).
8. Jacobson, N.: Abstract derivation and Lie algebras. Trans. Amer. Math. Soc. 42(2), 206–224 (1937).
9. Huru, H.L.: Quantizations of braided derivations. I: Monoidal categories. Lobachevskii J. Math. 24, 13–42 (2006).
10. Różański, J.: Bicharacters, braids and Jacobi identity. arXiv:q-alg/9611029 (1996).
11. Weibel, C.A.: An Introduction to Homological Algebra. Cambridge Stud. Adv. Math. 38, Cambridge University Press, Cambridge (1994).

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.
