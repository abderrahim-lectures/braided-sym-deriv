# Prose review — `paper/braided-sym-deriv.tex`, v79

Reviewer: m-1bad6a (prose pass). Worktree `.loom/m-1bad6a/prose-1`, branch
`loom/v79/m-1bad6a/prose-1`. The paper was **not** edited. Line numbers are
those of the 686-line source; every row was read in the source, not inferred.

Scope: the five writing rules of the owner's `CLAUDE.md` (plain prose, simple
academic English ≤ 30 words, keep the paper's notation, cited names, abstract
states its results), plus cross-references, term order, ring/algebra wording and
LaTeX defects. Mathematical claims are flagged, never changed.

Commands run from the worktree root:

* `bash /workspace/nucleus/work/home/.loom/checks/check-plain-prose.sh paper/braided-sym-deriv.tex`
  → 1 antithesis finding (line 521), 0 vocabulary findings, "acceptable at this density".
* `bash /workspace/nucleus/work/home/.loom/checks/english.sh paper/braided-sym-deriv.tex`
  → exit 1: 32 sentences over 30 words, 16 uncommon words.
  Both checker lists are incomplete (the antithesis at 149 and most of the
  30-word cases inside math-heavy lines are missed, and several lines the
  checker counts are not separate sentences). The list below is the hand audit.

Counts of words per sentence are approximate where inline formulas are
involved; every flagged sentence is over 30 by the checker as well.

---

## 1. Defects

Table columns: line | category | text as printed (excerpt) | why it breaks a rule | minimal edit, quoted as it would be written.

| line | category | text as printed | why | minimal edit |
|---|---|---|---|---|
| 69 | LENGTH (33) | "For a commutative reduced algebra with $2$ invertible, the twisted maps are exactly the derivations that commute with $\alpha$, and on $2$-torsion-free semiprime algebras …" | 33 words, two distinct results in one sentence (Theorem 4.1 and Corollary 3.5) | "…that commute with $\alpha$. On $2$-torsion-free semiprime algebras, the Jordan maps among them are exactly those derivations." |
| 71 | RARE WORD | "Nilpotent elements show that reducedness is needed … and a four-dimensional example that reducedness and commutativity cannot both be dropped." | "reducedness" is a nominalization of the defined term "reduced" (defined at 165, not here); used twice in one sentence | "…that the reduced hypothesis is needed … and a four-dimensional example that the reduced and commutative hypotheses cannot both be dropped." |
| 71 | RARE WORD | "characteristic $2$ that the invertibility of $2$ is needed" | "invertibility" where the abstract itself (line 64) says "with $2$ invertible" | "characteristic $2$ that $2$ must be invertible" |
| 91 | NOTATION | "A \emph{Lie derivation} is a linear map with $D([x,y]) = [D(x), y] + [x, D(y)]$ \citep[p.~183]{Martindale1964}." | $[x,y]$ is used here (and at 92) but first defined only at 162; a reader meets an undefined symbol in the introduction | "…with $D([x,y]) = [D(x), y] + [x, D(y)]$, where $[x,y] = xy - yx$ \citep[p.~183]{Martindale1964}." (and drop "for the commutator" at 162) |
| 94, 162 | DEFINED TWICE | 94: "…where $x \circ y = xy + yx$." / 162: "$x \circ y = xy + yx$ for the Jordan product" | the same product is defined twice; and at 95 the paper calls $\tfrac12(xy+yx)$ "the Jordan product", so the phrase carries two meanings (with and without the half) | 162: "and $x \circ y = xy + yx$ for Herstein's Jordan product" |
| 110 | TYPO | "It gives a symmetrized product, as the Jordan product does \citep[Example 2.1]{BresarZelmanov2025}" | no full stop before the display; every other sentence before a display ends with one | "…{BresarZelmanov2025}." |
| 110 | TERM ORDER | "It gives a symmetrized product, as the Jordan product does" | first definition of a named term not marked, although every other coined term is `\emph` | "It gives a \emph{symmetrized product}, as the Jordan product does" |
| 116 | NOTATION | "Put $\mu_\sigma = \mu + \mu \circ \sigma$." | `\circ` is the Jordan product from 94 onward and composition here, with no word of warning; the same overload at 206 | "Put $\mu_\sigma = \mu + \mu \circ \sigma$, where $\circ$ here is composition of maps." |
| 126 | DEFINED TWICE | "We call a linear map $D \colon A \to A$ a \emph{braided-symmetric derivation} for $\sigma$ if …" | the notion is defined here and again as Definition 2.1 (186–192), both in `\emph` | "We say that a linear map $D \colon A \to A$ is a braided-symmetric derivation for $\sigma$, a notion defined in Section~\ref{sec:sigma-derivations}, if" |
| 138 | LENGTH (33) | "Remark~\ref{rem:sigma-derivation-classification} shows that the identity gives exactly the derivations when $2$ is invertible, the swap gives exactly the Jordan derivations, and the two sign changes give all linear endomorphisms and the Lie derivations." | 33 words, three results in one sentence | "…when $2$ is invertible. The swap gives exactly the Jordan derivations, and the two sign changes give all linear endomorphisms and the Lie derivations." |
| 140 | TERM ORDER | "We then twist the swap by an involutive automorphism or anti-automorphism $\alpha$ of $A$." | "automorphism", "anti-automorphism" and "involutive" are defined only at 274–277, although the same sentence at 191 already carries the forward pointer | "We then twist the swap by an involutive automorphism or anti-automorphism $\alpha$ of $A$ (both are recalled in Section~\ref{sec:twisted})." |
| 141 | LENGTH (40) | "For an involutive $\alpha$ we put …, and we write $\BSDer_{\sigma_\alpha}(A)^\alpha$ for …, we call them \emph{twisted derivations}; the literature's twisted ($\sigma$-)derivations are a different notion, the $\alpha$-derivations of Section~\ref{sec:sigma-derivations}." | 40 words, two semicolons, and the final appositive can be read as identifying the two notions | split into three sentences: "… we put $\sigma_\alpha(x \otimes y) = \alpha(y) \otimes \alpha(x)$. We write $\BSDer_{\sigma_\alpha}(A)^\alpha$ for the maps of the class of Definition~\ref{def:sigma-derivation} that commute with $\alpha$; we call them \emph{twisted derivations}. The literature's twisted ($\sigma$-)derivations are a different notion, the $\alpha$-derivations of Section~\ref{sec:sigma-derivations}." |
| 142 | TERM ORDER | "Proposition~\ref{prop:defect} describes the twisted derivations through the defect $E_D(x,y) = …$" | the tool is named "the Leibniz defect" only at 271 and defined at 310; here it carries a bare "the defect" | "through the Leibniz defect $E_D(x,y) = …$" |
| 145 | TERM ORDER | "treats commutative reduced algebras and needs no Jordan hypothesis" | "reduced" is defined at 165, 20 lines later | "treats commutative reduced algebras, those with no nonzero nilpotent element, and needs no Jordan hypothesis" |
| 146 | RARE WORD | "shows the same for the invertibility of $2$" | "invertibility" | "shows the same for the hypothesis that $2$ is invertible" |
| 149 | ANTITHESIS | "The dictionary itself is not new. The contribution of this paper is elsewhere:" | the forbidden "It is not X. It is Y." pair, at the head of the paper's account of its contribution; the checker's regex does not reach it | "The dictionary itself is due to \citet[Remark 1.4]{Benkovic2015}." — and in the next sentence "of \citet[Remark 1.4]{Benkovic2015}" → "of that remark" |
| 149 | LENGTH (62) | "The four structure-free involutions give the products …, which in the notation … are the cases …; that remark assigns a Lie derivation to …, a Jordan derivation to … and a derivation to …, under the regularity hypotheses stated there, and the degenerate zero product …" | 62 words, three semicolons, and "structure-free" is glossed only at 152 | "…are the cases $\beta = 2$, $\gamma = 0$; $\beta = \gamma = 1$; and $\beta = 1$, $\gamma = -1$. In that remark a Lie derivation corresponds to $\gamma = -\beta$, a Jordan derivation to $\gamma = \beta$ and a derivation to $\gamma \ne \pm\beta$, under the regularity hypotheses stated there. The degenerate zero product $\beta = \gamma = 0$ lies outside its cases." |
| 149 | LENGTH (55) | "The contribution of this paper is elsewhere: the criterion of Proposition~…, which …; Theorem~…, which …; Proposition~…, which shows that the two classes are incomparable; and Remark~…, which …" | 55 words: a colon followed by four semicolon-separated items, and "incomparable" is a dictionary word for "neither class contains the other" | "The contribution of this paper is the criterion of Proposition~\ref{prop:defect}, which turns each of the questions below into a linear condition. Theorem~\ref{thm:twisted-commutative} needs no Jordan hypothesis. Proposition~\ref{prop:twisted} shows that neither class contains the other. Remark~\ref{rem:commutativity-needed} gives a counterexample when commutativity and the reduced hypothesis are dropped together, and reduces the remaining case." |
| 152 | LENGTH (31) | "Section~\ref{sec:sigma-derivations} recalls …, and treats the four structure-free involutions, those that use nothing of $A$ beyond its $K$-vector space, which collapse to two in characteristic $2$." | 31 words and a three-deep relative construction | "… and treats the four structure-free involutions, those that use nothing of $A$ beyond its $K$-vector space. They collapse to two in characteristic $2$." |
| 165 | TYPO + CITE | "this is the notion of \citet[1.4.12]{ChambertLoir2021}" | the only citation in the paper with a bare number: every other locator names its kind (Part I, §2, Theorem 3.1, Example 2.1, p. 183, §4.1 Definition 14); and the citation is attributive, so `\citep` is the right form here (the only such place in the paper) | "this is the notion defined in \citep[Definition 1.4.12]{ChambertLoir2021}" |
| 173 | TYPO | "as a derivation of the Jordan ring of $A$, that is by $D(x \circ y) = …$" | "that is by" is ungrammatical (the comma is missing) | "that is, by" |
| 173 | LENGTH (36) | the whole sentence from "\citet[p.~1104]{Herstein1957} defines a \emph{Jordan derivation}" to "…the square identity $D(x^2) = D(x)x + xD(x)$." | 36 words, two results of Herstein in one sentence | "…that is, by $D(x \circ y) = D(x) \circ y + x \circ D(y)$. He records that for rings of characteristic different from $2$ it can be defined by the square identity $D(x^2) = D(x)x + xD(x)$." |
| 174 | DEFINED TWICE | "We write $\JDer(A)$ for the space of linear maps with $D(x \circ y) = D(x) \circ y + x \circ D(y)$ for all $x, y$." | the same condition is stated at 94 and again at 173; a third statement adds nothing | "We write $\JDer(A)$ for the space of Jordan derivations." |
| 177 | LENGTH (34) | "So the two conditions agree when $2$ is invertible in $K$, and also when $A$ is $2$-torsion-free, where the factor $2$ … can be cancelled; we use the $\circ$ form throughout." | 34 words with a semicolon splice | "…can be cancelled. We use the $\circ$ form throughout." |
| 210 | NOTATION | "Example~\ref{ex:not-associative} shows that the product $\cdot_\sigma$ can fail to be associative and unital" | the example is about $\cdot_{\sigma_\alpha}$; $\cdot_\sigma$ is the general product | "the product $\cdot_{\sigma_\alpha}$ can fail to be associative and unital" |
| 236 | LENGTH (31) | "If $A \neq 0$, this is larger than $\Der(A)$: the linear map with … is not a derivation, since a derivation satisfies …" | 31 words; the comma before "since" also invites the wrong scope for the reason | "…is not a derivation. A derivation satisfies $D(1) = D(1 \cdot 1) = 2D(1) = 0$ in characteristic $2$." |
| 242, 442 (also 105, 184) | DEFINED TWICE | 242: "Every derivation is a Jordan derivation \citep[p.~1003]{Bresar1988}." 442: "Every derivation is a Jordan derivation by Remark~\ref{rem:sigma-derivation-classification}." | the sentence, with the same citation, appears four times (105, 184, 242, 442) | 242: "Every derivation is a Jordan derivation, as recalled above." / 442: "Every derivation is a Jordan derivation." |
| 262 | LENGTH (133) | "The four entries of Remark~… are the involutions of $A \otimes A$ given by natural transformations of the functor $V \mapsto V \otimes V$ …, that is, natural for all $K$-linear maps and not only for algebra maps; the natural endomorphisms … for three reasons: …; …; and $\mathrm{id}$ and $\tau$ are natural." | the longest sentence in the paper (133 words): colon plus a three-item list whose items themselves contain "since", "while", "and"; "naturality" is a dictionary nominalization | split as follows (same claims, same order): "…on $K$-vector spaces. These transformations are natural for all $K$-linear maps, not only for algebra maps. The natural endomorphisms of the functor are the linear combinations of $\mathrm{id}$ and $\tau$, for three reasons. First, such an endomorphism is determined by its value on $K^2$. Indeed, every element of $V \otimes V$ is a sum of elements of the subspaces $j \otimes j(K^2 \otimes K^2)$ over the linear maps $j \colon K^2 \to V$. For $\dim V \le 1$ the assertion is immediate, because $\mathrm{id} = \tau$ on $V \otimes V$. Second, being natural in the maps $f \colon K^2 \to K^2$ makes that value an endomorphism of $K^2 \otimes K^2$ commuting with every $f \otimes f$. Those are the linear combinations of $\mathrm{id}$ and $\tau$, by a direct computation with the $2 \times 2$ matrices. Third, $\mathrm{id}$ and $\tau$ are natural." |
| 263 | LENGTH (60) | "Every idempotent $P$ … gives the involution …, and when $2$ is invertible every involution arises this way, from …; the four structure-free idempotents are …, whose reflections are …, while, when … and …, an idempotent that uses the multiplication, such as …, gives an involution that is none of them." | 60 words, semicolon splice, and a "while" clause of six words' depth | split at the semicolon: "…from $P = \tfrac12(\mathrm{id} - \sigma)$. The four structure-free idempotents are …" |
| 264 | LENGTH (50) | "In characteristic $2$ the maps …, for $\lambda \in K$, are involutions as well, and they are the only natural ones; the product one of them defines is … so they add no class to the dictionary, and the value $\lambda = 1$ gives the zero product." | 50 words with a semicolon and four coordinated clauses | split at the semicolon: "…and they are the only natural ones. The product one of them defines is …" |
| 265 | LENGTH (44) | "Involutions that use structure of $A$ give other classes: for invertible $T$ …, and on $\mathbb{F}_5[\varepsilon]/(\varepsilon^2)$ … a direct computation on the two basis elements gives …, which is none of the four entries of Remark~…" | 44 words, colon plus a two-part example inside one sentence | "…give other classes. For invertible $T$ the map … is an involution. On $\mathbb{F}_5[\varepsilon]/(\varepsilon^2)$ …, a direct computation on the two basis elements gives …, which is none of the four entries of Remark~…" |
| 285 | LENGTH (52) | "… and $\sigma_\alpha$ is an involution of $A \otimes A$ exactly when $\alpha^2 = \mathrm{id}$: if …, then … (an endomorphism $\beta$ with … is a scalar multiple of the identity: choosing …, the identity … forces …, with a scalar independent of $x$), and … gives $\lambda = 1$." | 52 words, a colon clause containing a parenthesis that itself contains a colon clause (nested parenthesis) | "…exactly when $\alpha^2 = \mathrm{id}$. If $\alpha^2 \otimes \alpha^2 = \mathrm{id}$, then $\alpha^2 = \lambda\,\mathrm{id}$ with $\lambda^2 = 1$, and $\alpha^2(1) = 1$ gives $\lambda = 1$. Indeed, an endomorphism $\beta$ with $\beta \otimes \beta = \mathrm{id}$ is a scalar multiple of the identity: choosing $y$ with $\beta(y) \ne 0$, the identity $\beta(x) \otimes \beta(y) = x \otimes y$ forces $\beta(x) \in Kx$ for every $x$, with a scalar independent of $x$." |
| 317 | ANTITHESIS (borderline) | "The name is ours, and the map is classical:" | set against "The dictionary itself is not new" at 149 it repeats the ours/theirs contrast; on its own it is a mild X-vs-Y pair | "The name is ours, following \citet[\S2]{Cusack1975}, who writes the map $d(a,b) = D(ab) - aDb - (Da)b$ and studies Jordan derivations through it." |
| 328, 332 | DEFINED TWICE | 332: "This says that $E_D$ is a cocycle of the Hochschild complex \citep[\S9.1]{Weibel1994}." | 328 already says "the defect is a $2$-cocycle" and displays the identity; 332 repeats it (and the complex was cited at 318) | delete line 332 |
| 334 | CLAIM | "The defect also describes the other classes of Section~\ref{sec:sigma-derivations}." | only one other class follows (the Jordan derivations, 335); the plural promises a list | "The defect also describes another class of Section~\ref{sec:sigma-derivations}." |
| 385 | LENGTH (41) | "Without it they no longer characterize the class, and when $A$ is unital they say something else: if they vanish, then … so $D$ lies in the class exactly when $D\alpha = \alpha D$." | 41 words, colon clause, and "they say something else" is vague | "Without it they no longer characterize the class. When $A$ is unital they still say something: if they vanish, then the difference of the two sides of the $\sigma_\alpha$-identity is $(D\alpha - \alpha D)(yx)$, so $D$ lies in the class exactly when $D\alpha = \alpha D$." |
| 387 | RARE WORD | "The computation uses neither the unitality of $A$ nor the involutivity of $\alpha$" | "unitality" and "involutivity" are both dictionary nominalizations of words the paper uses elsewhere in plain form (84, 277) | "The computation uses neither that $A$ is unital nor that $\alpha$ is involutive" |
| 394, 395 | NOTATION | 394: "… is symmetric." 395: "… is antisymmetric." | "symmetric" is a defined term of the paper for the elements of $A_+$ (291); here and at 462, 485 it means a property of a bilinear map, so one word carries two meanings | 394: "… is symmetric in $x$ and $y$." 395: "… is antisymmetric in $x$ and $y$." |
| 438 | LENGTH (34) | "…where $\Der(A)^\alpha$ is the set of derivations commuting with $\alpha$ (not to be confused with the space $\ADer(A)$ of $\alpha$-derivations of Section~…, which is the notion the literature calls a twisted derivation)." | 34 words and a parenthesis holding a second contrast for a notation that differs only by the position of $\alpha$ | "…commuting with $\alpha$. (The space $\ADer(A)$ of $\alpha$-derivations of Section~\ref{sec:sigma-derivations} is a different notion, the one the literature calls a twisted derivation.)" (the parenthesis at 438 becomes a sentence of its own) |
| 444 | LENGTH (42) | "Conversely, every Jordan derivation of $A$ is a derivation by Theorem~…, which applies since a $K$-linear map is additive; the $\circ$ form … and Herstein's $x^2$ form agree by the linearization of Section~…, which uses the $2$-torsion-freeness assumed here." | 42 words, semicolon splice, plus "linearization" and "torsion-freeness" | "…which applies since a $K$-linear map is additive. The $\circ$ form of the Jordan condition and Herstein's $x^2$ form agree by the argument of Section~\ref{sec:sigma-derivations} that replaces $x$ by $x + y$ in the square identity, which uses the hypothesis that $A$ is $2$-torsion-free." |
| 465 | RARE WORD + TYPO | "…into itself; and since $\alpha$ is multiplicative, $A_iA_j \subseteq A_{i+j}$." | "multiplicative" for "preserves products"; and "and" after a semicolon | "…into itself. Since $\alpha$ preserves products, $A_iA_j \subseteq A_{i+j}$." |
| 477, 482 | NOTATION | 477: "The pairs $(zx,y)$ and $(z,xy)$ lie in $A_-$" 482: "The pairs $(z,y)$ and $(xz,y)$ lie in $A_-$, and the pair $(x,zy)$ lies in $A_+$" | a pair is not an element of $A_-$; the paper's own notation for this is $A_-\times A_-$ (616, 623) | 477: "Both entries of the pairs $(zx,y)$ and $(z,xy)$ lie in $A_-$" 482: "Both entries of $(z,y)$ and $(xz,y)$ lie in $A_-$, and both entries of $(x,zy)$ lie in $A_+$" |
| 487 | RARE WORD | "and reducedness only to pass from $z \in A_-$ and $z^2 = 0$ to $z = 0$" | "reducedness" | "and the hypothesis that $A$ is reduced only to pass from …" |
| 490 | LENGTH (39) | "Second, commutativity is used nowhere else in the argument: for any unital $K$-algebra $A$ with …, if $D \in …$ has symmetric defect $E_D$ and no nonzero $z \in A_-$ satisfies $z^2 = 0$, then $D$ is a derivation." | 39 words, colon clause, and "has symmetric defect $E_D$" is not the paper's phrasing ("$E_D$ is symmetric") | "Second, commutativity is used nowhere else in the argument. For any unital $K$-algebra $A$ with $2$ invertible and any involutive automorphism $\alpha$, if $D \in \BSDer_{\sigma_\alpha}(A)^\alpha$ and $E_D$ is symmetric and no nonzero $z \in A_-$ satisfies $z^2 = 0$, then $D$ is a derivation." |
| 494 | RARE WORD | "The theorem is not vacuous." | "vacuous" for "has content" | "The theorem has content." |
| 494 | TERM ORDER + CLAIM | "Over a perfect field no finite-dimensional instance exists: a finite-dimensional reduced commutative algebra is a product of finite separable field extensions of $K$ …, and a separable extension has no nonzero $K$-derivation." | 31 words; "perfect field" and "separable extension" are named notions used without definition or citation, the only such terms in the paper; and as printed "no finite-dimensional instance exists" is about all finite-dimensional algebras, whereas the argument shows only that no such algebra has a nonzero derivation | "Over a perfect field, one whose every algebraic extension is separable, no finite-dimensional instance with a nonzero derivation exists. A finite-dimensional reduced commutative algebra is a product of finite separable field extensions of $K$ \citep[\S3.5]{Pierce1982}. A separable extension has no nonzero $K$-derivation." |
| 496, 514 | RARE WORD | "shows the same for the invertibility of $2$" / "shows that the invertibility of $2$ is needed" | "invertibility" | "shows the same for the hypothesis that $2$ is invertible" / "shows that the hypothesis that $2$ is invertible is needed" |
| 510 | LENGTH (54) + RARE WORD | "A direct computation verifies the three statements: commutation with $\alpha$ is linear in $D$ and is checked on a basis, and the Leibniz rule is linear in $D$ and bilinear in the pair, so it too is checked on basis pairs; the failure of the derivation rule is read at the single pair $(u,v)$." | 54 words, colon plus semicolon, and "commutation with $\alpha$ is linear" is a category error (a condition, not a map, is linear) | "A direct computation verifies the three statements. The condition $D\alpha = \alpha D$ is linear in $D$, so a check on a basis suffices. The Leibniz rule is linear in $D$ and bilinear in the pair, so it too is checked on basis pairs. The failure of the derivation rule is read at the single pair $(u,v)$." |
| 521 | ANTITHESIS | "…the two sides vanish because $D(e) = 0$ and $2e = 0$, not because the products vanish." | "X, not Y" contrast, the construction the owner forbids outright (the checker's one hit) | "…the two sides vanish because $D(e) = 0$ and $2e = 0$, although $p \cdot_{\sigma_\alpha} p = e \ne 0$." |
| 522 | LENGTH (34) | "For a pair with $e$ in one entry, …, so the left side vanishes because …, and the right side is …, which vanishes because … and …" | 34 words, four clauses in one sentence | split: "…so the left side vanishes because $D(e) = D(0) = 0$. The right side is $D(x) \cdot_{\sigma_\alpha} e$, which vanishes because $D(x)$ lies in $\{0, e\}$ and $e \cdot_{\sigma_\alpha} e = 2e = 0$." |
| 527 | CLAIM | "Our second natural candidate for the twisted derivations is the space $\ADer(A)$ of $\alpha$-derivations." | "second" has no first: the paper never named a first candidate before this point | "Another natural candidate for the twisted derivations is the space $\ADer(A)$ of $\alpha$-derivations." |
| 553 | TYPO | "Pairs that contain $1$ give $D$ of the other element of the pair on both sides" | ungrammatical ("give $D$ of the other element … on both sides") | "For a pair that contains $1$, both sides equal $D$ of the other element, since $D(1) = 0$ and $\alpha(1) = 1$." |
| 568 | NOTATION | "It is a derivation, since $d(\varepsilon^i) = i\varepsilon^i$ and exponents add under multiplication." | $i$ is an integer exponent and also the element $i \in \mathbb{F}_3$ by which one multiplies; the formula also silently needs $i \in \{0,1,2\}$ read mod $3$ | "It is a derivation, since $d(1) = 0$, $d(\varepsilon) = \varepsilon$, $d(\varepsilon^2) = 2\varepsilon^2$, and exponents add under multiplication." |
| 577 | TYPO/CROSS-REF | "Part (b) of the next example shows the first, part (a) the second." | the example has a label (`ex:twisted-meet`) that is never used; the text points by position only | "Part (b) of Example~\ref{ex:twisted-meet} shows the first, part (a) the second." |
| 583 | LENGTH (39) | "It commutes with $\alpha$ by the anti-automorphism case of Remark~…, since $g + \alpha(g) = 0$, and it has $E = 0$, so it lies in … by Proposition~…" | 39 words, three "it"s and three commas | split: "It commutes with $\alpha$ by the anti-automorphism case of Remark~\ref{rem:inner-twisted}, since $g + \alpha(g) = 0$. It has $E = 0$, so it lies in $\BSDer_{\sigma_\alpha}(A)^\alpha$ by Proposition~\ref{prop:defect}." |
| 588 | LENGTH (36) | "A direct computation gives that when $\operatorname{char} K \neq 2$ both classes are one-dimensional, …, so here they coincide; when $\operatorname{char} K = 2$ …" | 36 words with a semicolon splice joining two characteristics | split: "…, so here they coincide. When $\operatorname{char} K = 2$ …" |
| 591 | RARE WORD | "Reducedness and commutativity cannot both be dropped" (remark title) | "reducedness" | "The reduced and commutative hypotheses cannot both be dropped" |
| 599 | LENGTH (40) | "The linear map $D$ with … commutes with $\alpha$ and satisfies the Leibniz rule … on every pair of basis elements; since that rule is …, $D$ lies in …" | 40 words with a semicolon splice | split: "…on every pair of basis elements. Since that rule is linear in $D$ and bilinear in the pair, $D$ lies in $\BSDer_{\sigma_\alpha}(A)^\alpha$." |
| 602 | LENGTH (32) | "The defect is antisymmetric at $(v,w)$, where $E_D(v,w) = -t$, and $A_-$ does contain a nonzero square-zero element, $(v+w)^2 = 0$; this is consistent with …" | 32 words with a semicolon; "antisymmetric at $(v,w)$" also misuses the word (a bilinear map is antisymmetric, not a value) | "…, and $A_-$ does contain a nonzero square-zero element, $(v+w)^2 = 0$. This is consistent with …" |
| 604 | LENGTH (89) + RARE WORD | "A witness that drops commutativity while keeping reducedness is not to be had in finite dimension over a finite field: … then a product of matrix algebras over division rings …, and reducedness forces …, since $e_{12}^2 = 0$ …; so it is a product of division rings, each of which is a field when the base field is finite." | 89 words: a colon, three semicolons, two citations and a nested "since" clause in one sentence; "reducedness" twice; "is not to be had" is an idiom | "A witness that drops commutativity while keeping the reduced hypothesis does not exist in finite dimension over a finite field. The radical of a finite-dimensional algebra is nilpotent \citep[\S4.4]{Pierce1982}, so it is zero in a reduced algebra, and the algebra is semisimple. By Wedderburn's structure theorem it is then a product of matrix algebras over division rings \citep[\S3.5]{Pierce1982}. The reduced hypothesis forces the matrix sizes to be $1$, since $e_{12}^2 = 0$ in $M_n(D)$ for $n \geq 2$. So it is a product of division rings, each of which is a field when the base field is finite." |
| 605 | CLAIM | "The first candidate is therefore a non-commutative division algebra, such as the quaternions $\mathbb{H}$ over $\mathbb{R}$" | "the first candidate" — nothing was listed, so "first" has no referent | "The simplest candidate is therefore a non-commutative division algebra, such as the quaternions $\mathbb{H}$ over $\mathbb{R}$" |
| 607 | LENGTH (85) | "Every automorphism of $\mathbb{H}$ is inner …, so the involutive ones are …; any two of the latter are conjugate, since …; the structure constants are rational, …, and solving the linear conditions on the sixteen coordinates of $D$ … gives …; for $\alpha = \mathrm{id}$ the two dimensions are $3$, by Theorem~…" | 85 words: three semicolons and four separate claims | "Every automorphism of $\mathbb{H}$ is inner \citep[\S12.6]{Pierce1982}, so the involutive ones are the identity and the conjugations by pure imaginary quaternions. Any two of the latter are conjugate: $u q u^{-1} = q'$ for $u = 1 - q'q$ when $q, q'$ are pure imaginary of norm $1$ with $q' \ne -q$. The case $q' = -q$ gives the same conjugation. The structure constants are rational, so one computation settles all of them. Solving the linear conditions on the sixteen coordinates of $D$, for a conjugation $\alpha$, gives $\dim\BSDer_{\sigma_\alpha}(\mathbb{H})^\alpha = \dim\Der(\mathbb{H})^\alpha = 1$. For $\alpha = \mathrm{id}$ the two dimensions are $3$, by Theorem~\ref{thm:bresar}." |
| 609 | TYPO | "the derivations lie in the twisted class only in so far as they commute with $\alpha$" | "in so far as" is written as one word | "only insofar as they commute with $\alpha$" |
| 494, 548, 551, 562, 605 | TYPO | "non-trivial" (494), "non-inclusion" (548, 551, 562), "non-commutative" (605) | the prefix is closed in "nonzero" (14 times) and "nonassociative" (89, 228) and hyphenated in these three compounds, so the same prefix is written two ways | "nontrivial", "noninclusion", "noncommutative" (closed, to match "nonzero") |
| 613 | NOTATION | "since $E$ is additive in each argument and $A = A_+ + A_-$, three cases remain" | 286 and 485 write $A = A_+ \oplus A_-$ for the same decomposition; and "multiplicative" at 613 | "Since $\alpha$ preserves products and $D$ commutes with it, $E$ maps $A_i \times A_j$ into $A_{i+j}$. Since $E$ is additive in each argument and $A = A_+ \oplus A_-$, three cases remain." |
| 615 | LENGTH (34) + GRAMMAR | "… is a Jordan derivation of $A_+$, a reduced, hence semiprime, and $2$-torsion-free ring, and is therefore a derivation there by Theorem~…" | 34 words, and the comma before "and" misparses ("a reduced, hence semiprime, and $2$-torsion-free ring") | "… is a Jordan derivation of $A_+$, which is a reduced ring, hence semiprime and $2$-torsion-free. It is therefore a derivation there by Theorem~\ref{thm:bresar}, so $E(x,y) = 0$." |
| 616 | LENGTH (32) | "So only $x, y \in A_-$ remains, where $E$ is alternating with values in $A_+$: …, and $E(x,x) \in A_+ \cap A_- = 0$ because …" | 32 words with a colon clause | "…with values in $A_+$. The values lie in $A_+$ by the parity of $E$, and $E(x,x) \in A_+ \cap A_- = 0$ because Proposition~\ref{prop:defect}(i) at $(x,x)$ puts $E(x,x)$ in $A_-$." |
| 617 | CLAIM (mathematics) | "whether it must vanish is what is missing, and it is not settled here." | this says the vanishing on $A_-\times A_-$ is open, while 619–628 prove it equivalent to (i) and 628 concludes "Thus (i), (ii) and (iii) are equivalent". The two sentences cannot both stand | **no edit proposed** — which sentence is right is a mathematical decision |
| 619–628 | NOTATION | "Write (i) for $D \in \Der(A)$, (ii) for $E = 0$ on $A_+ \times A_-$, and (iii) for …" | (i) and (ii) are already the two enumerated parts of Proposition~\ref{prop:defect} (340, 341), with different content | "Write (a) for $D \in \Der(A)$, (b) for $E = 0$ on $A_+ \times A_-$, and (c) for $E = 0$ on $A_- \times A_-$." (and every later mention of (i), (ii), (iii) in this remark renamed) |
| 623 | LENGTH (34) | "Then $E$ vanishes on $A_+ \times A_+$ by the argument of the case $x, y \in A_+$ above, and on $A_- \times A_-$ by hypothesis; on a mixed pair $E(x,y) = E(y,x)$, because …" | 34 words with a semicolon | split at the semicolon: "…by hypothesis. On a mixed pair $E(x,y) = E(y,x)$, because …" |
| 624 | LENGTH (32) | "So $E$ is symmetric, and the argument of the proof of Theorem~…, which uses only the symmetry of $E$ and not the commutativity of $A$, gives $E = 0$; so $D$ is a derivation." | 32 words, semicolon, and two "so" | "…gives $E = 0$. So $D$ is a derivation." |
| 626 | LENGTH (39) | "Then $E$ vanishes on $A_+ \times A_+$ as above and on the mixed pairs by hypothesis, and on $A_- \times A_-$ it is alternating, hence antisymmetric, because …" | 39 words, four clauses | "Then $E$ vanishes on $A_+ \times A_+$ as above and on the mixed pairs by hypothesis. On $A_- \times A_-$ it is alternating, hence antisymmetric, because $E(x,x)$ lies in $A_+$ by the parity of $E$ and in $A_-$ by Proposition~\ref{prop:defect}(i) at $(x,x)$." |
| 627 | LENGTH (41) + RARE WORD | "So $E$ is antisymmetric, which makes $D$ a Jordan derivation of $A$, and $A$ is reduced, hence semiprime and $2$-torsion-free, so the two forms of the Jordan condition agree by the linearization of Section~… and $D$ is a derivation by Theorem~…" | 41 words, five clauses, and "linearization" | "So $E$ is antisymmetric, which makes $D$ a Jordan derivation of $A$. Since $A$ is reduced, it is semiprime and $2$-torsion-free, so the two forms of the Jordan condition agree by the argument of Section~\ref{sec:sigma-derivations} that replaces $x$ by $x + y$ in the square identity. Hence $D$ is a derivation by Theorem~\ref{thm:bresar}." |

### Not defects, checked and clean (recorded so the list is not re-read)

* Every `\ref` and `\eqref` resolves; no duplicated `\label`; no double space; no
  `i.e.`/`e.g.`; no unbalanced `$`; `\citet` is used where an author is the subject or the
  attribution reads as a name (89, 90, 92, 93, 97, 106, 149, 169, 173, 228, 278,
  317, 428); the only `\citet` that should be `\citep` is at 165 (reported).
* "the two remaining terms" (384): the displayed residual has three terms, the
  hypothesis removes the third, so "the two remaining terms" is right.
* 130 "So \eqref{eq:sigma-leibniz} is …" carries no `~`; that is right, since the
  reference follows a sentence-initial "So" and a tie is not wanted there.
* "First/Second" (488, 490) and "the first/the second" (577) match what follows;
  "the three conditions" (619) and "three cases remain" (613) match.
* `\ADer` prints as $\mathrm{Der}_\alpha$, and the prose never writes "ADer":
  438 and 527 correctly say "the space $\ADer(A)$ of $\alpha$-derivations".
  `$\Der(A)^\alpha$` and `$\BSDer_{\sigma_\alpha}(A)^\alpha$` are used
  consistently; 191's generic `$\BSDer_\sigma(A)^\alpha$` is the correct
  general form. `\mathrm{id}` for the identity map and `1` for the unit are kept
  apart throughout.
* The `$\operatorname{ad}_g$` sign convention (169) is consistent with
  $[x,y] = xy - yx$ (162): $\operatorname{ad}_{-m}(x) = xm - mx$.
* "principle" never appears; "principal derivations" (169) follows Weibel.
* "quasi-multiplication" (96), "semiprime"/"prime"/"$2$-torsion-free" (100–102),
  "braided derivations" (131), "Jordan product" (95), "Hochschild complex" (318)
  and "Wedderburn's structure theorem" (604) each carry a located citation at
  first use, as rule 4 asks.

---

## 2. Abstract ↔ body

The abstract is lines 62–71; sentence numbers count from line 62.

| # | line | abstract sentence | proved by |
|---|---|---|---|
| 1 | 62 | "We study braided-symmetric derivations of an algebra over a field." | Definition~\ref{def:sigma-derivation} (186) |
| 2 | 63 | "These are maps that satisfy the Leibniz rule for the product symmetrized by an involution of $A \otimes A$." | Definition~\ref{def:sigma-derivation} with \eqref{eq:sigma-leibniz} (188); the product is built at 108–117 |
| 3 | 64 | "The identity involution gives the ordinary derivations when $2$ is invertible." | Remark~\ref{rem:sigma-derivation-classification}, 234 ($\BSDer_{\mathrm{id}}(A) = \Der(A)$ if $\operatorname{char} K \neq 2$) |
| 4 | 65 | "The swap gives the Jordan derivations." | same remark, 240 ($\BSDer_\tau(A) = \JDer(A)$ in every characteristic) |
| 5 | 66 | "The negative of the identity gives all linear endomorphisms, and the negative of the swap gives the Lie derivations." | same remark, 251–255 |
| 6 | 67 | "We then twist the swap by an involutive automorphism or anti-automorphism $\alpha$ of $A$." | \eqref{eq:twisted-product} (304) with 293–294 |
| 7 | 68 | "The Leibniz defect of a map that commutes with $\alpha$ decides when it is a twisted derivation." | Proposition~\ref{prop:defect} (337–344) |
| 8a | 69 | "For a commutative reduced algebra with $2$ invertible, the twisted maps are exactly the derivations that commute with $\alpha$, …" | Theorem~\ref{thm:twisted-commutative} (453–456) |
| 8b | 69 | "… and on $2$-torsion-free semiprime algebras the Jordan maps among them are exactly those derivations." | Corollary~\ref{cor:twisted-semiprime} (436–439) |
| 9 | 70 | "On the algebra $\mathbb{F}_3[\varepsilon]/(\varepsilon^3)$ the twisted derivations … and the $\alpha$-derivations do not contain each other." | Proposition~\ref{prop:twisted} (531–539) |
| 10a | 71 | "Nilpotent elements show that reducedness is needed" | Example~\ref{ex:twisted-nilpotent} (498–512: $z = E(u,v) = uv$, $z^2 = 0$) |
| 10b | 71 | "characteristic $2$ that the invertibility of $2$ is needed" | Example~\ref{ex:twisted-char-two} (516–525) |
| 10c | 71 | "and a four-dimensional example that reducedness and commutativity cannot both be dropped" | Remark~\ref{rem:commutativity-needed} (591–603) |

Every abstract sentence is proved; none over-claims. Two points about rule 5
("the abstract states every own main result"):

* Remark~\ref{rem:natural-involutions} (261–266: in characteristic $\ne 2$ the
  four are the only involutions natural in $V \mapsto V \otimes V$) is an own
  result with a proof and is not stated in the abstract. Owner's call whether
  it counts as a main result.
* The two stronger statements at 489–490 (inside the proof of
  Theorem~\ref{thm:twisted-commutative}) are also own results not in the
  abstract. The equivalence of (i), (ii), (iii) at 619–628 is a third, but it
  must first be reconciled with 617 (see the CLAIM row).

---

## 3. "ring" / "algebra"

The convention is set at 84: "an algebra means a unital associative $K$-algebra".

| line | sentence | word printed | needed |
|---|---|---|---|
| 86 | "We say so when a result cited below holds more generally for additive maps on rings." | ring | ring — correct (the cited results are about rings) |
| 99 | "The results below need three notions for a ring $R$." | ring | ring — correct (Brešar's setting) |
| 100–102 | prime / semiprime / $2$-torsion-free for $R$ | ring | ring — correct |
| 103 | "So every prime ring is semiprime." | ring | ring — correct |
| 104 | "every Jordan derivation of a prime ring of characteristic different from $2$" | ring | ring — correct (Herstein) |
| 106 | "extended this result of Herstein to $2$-torsion-free semiprime rings" | rings | rings — correct (Cusack, Brešar) |
| 173 | "a derivation of the Jordan ring of $A$ … for rings of characteristic different from $2$" | ring | ring — correct (Herstein's formulation) |
| 278 | "an involution of the ring $A$ in the sense of \citet[\S1.2]{Herstein1976}" | ring | ring — correct (Herstein's notion) |
| 428 | "a Jordan derivation of a $2$-torsion-free semiprime ring is a derivation" | ring | ring — correct |
| 431 | Theorem~\ref{thm:bresar}: "Let $R$ be a $2$-torsion-free semiprime ring." | ring | ring — correct |
| 604 | "a product of matrix algebras over division rings … a product of division rings" | division rings | division rings — correct (division rings need not be commutative) |
| 615 | "the restriction of $D$ to $A_+$ is a Jordan derivation of $A_+$, a reduced, hence semiprime, and $2$-torsion-free ring" | ring | ring is right for applying Theorem~\ref{thm:bresar}, but the sentence reads as if $A_+$ were not an algebra; keep "ring" and fix the commas as in the LENGTH row for 615 |

No sentence calls an algebra a ring where the result is stated for algebras, and
no recalled ring theorem is stated for algebras. Only 615 needs an edit, and only
in its punctuation.

---

## 4. Counts and the three most worth fixing

| category | rows | lines |
|---|---|---|
| ANTITHESIS (one of them borderline) | 3 | 149, 317, 521 |
| LENGTH, sentence over 30 words | 32 rows, 31 distinct lines | 69, 138, 141, 149 (two sentences), 152, 173, 177, 236, 262, 263, 264, 265, 285, 385, 438, 444, 490, 510, 522, 583, 588, 599, 602, 604, 607, 615, 616, 623, 624, 626, 627 |
| RARE WORD (defective) | 11 | 71 (twice), 146, 387, 465, 487, 494, 496 & 514, 510, 591, 604, 627; the fixes for 262, 444 and 613 also remove "naturality", "linearization"/"torsion-freeness" and "multiplicative" |
| TERM ORDER (used before defined, or unglossed) | 6 | 91, 110, 140, 142, 145, 494 |
| DEFINED TWICE, or a statement repeated | 5 | 94 & 162, 126 & 188, 174, 242 & 442 (& 105, 184), 328 & 332 |
| NOTATION | 8 | 91, 116, 210, 394 & 395, 477 & 482, 568, 613, 619–628 |
| CLAIM (unsupported, unclear or contradictory) | 5 | 334, 494, 527, 605, 617 |
| TYPO / LaTeX | 8 | 110, 165, 173, 465, 553, 577, 609, 494 & 548 & 551 & 562 & 605 (hyphenation) |
| CROSS-REFERENCE | 1 | 577 (same row as its TYPO) |
| GRAMMAR | 1 | 615 (same row as its LENGTH) |
| RING/ALGEBRA mismatch | 0 | (615 reads oddly but needs only the punctuation fix already listed) |

The table has 73 rows; 7 of them carry two categories (465, 494, 510, 577,
604, 615, 627), which is why the rows above add to 80.

Words from the checker's list judged **not** defects and left alone:
"conjugations" (607), "functor" (262), "quaternions" (605), "triples" (598),
"verifies" (510) — all either technical terms the paper needs or ordinary
English; "involutive", "reduced", "semiprime", "unital" themselves stay, since
the paper defines and reuses them.

### The three most worth fixing

1. **617 vs 619–628 (CLAIM).** The remark says the vanishing of the defect on
   $A_- \times A_-$ "is not settled here" and then proves it equivalent to
   being a derivation. A reader who stops at 617 gets the wrong state of the
   paper. This one needs a mathematical decision before any prose edit.
2. **149 (ANTITHESIS + two long sentences).** "The dictionary itself is not new.
   The contribution of this paper is elsewhere:" is exactly the forbidden
   "It is not X. It is Y." pair, in the paragraph that states the paper's
   contribution, and the paragraph also carries the two longest sentences of
   the introduction. The checker misses it.
3. **262 (LENGTH, 133 words).** The longest sentence in the paper is a
   three-item justification with a colon and three semicolons, and it carries
   the argument that the four involutions are the only natural ones. Split it
   as quoted in the table; the mathematical content is untouched.
