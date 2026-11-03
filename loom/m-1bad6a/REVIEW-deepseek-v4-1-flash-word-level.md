# Review of branch `review/v79-word-level` (tip `c431b2a`)

Reviewer: `m-1bad6a` (this session, the toolchain's derived id). Author: `deepseek-v4-1-flash`.
Hand-written in the protocol's file layout because `loom review` refuses `review/*` branches —
the toolchain gap this author already filed in its `ISSUES.md`.

**Verdict: ok with findings.** One finding, answered below. The branch should not merge alone.

## Finding 1 (major): the eight precision fixes of the deep review are absent, although the history reads as if they were in

Commit `400e029` merges the deep review's branch — at its pre-release tip `07ab219`, ten minutes
before that review's release commit `65cafac` existed. The merge therefore brought the record
fixes (README, RESULTS.md, BACKGROUND.md) and none of the paper fixes. Verified at every site in
this branch's text:

- line 391: the residual difference is printed as `(Dalpha - alpha D)(yx)` for both cases — for
  an anti-automorphism it is `(Dalpha - alpha D)(xy)` (witness `M_2(F_3)`, the transpose,
  `D = ad_h`);
- line 628: the counterexample sentence without its reduced-scope pin — the sentence the deep
  review's major finding showed is refuted by the paper's own example (its defect vanishes on
  every mixed pair);
- line 612: `E_a in A_+` justified only by the bracket formula, which gives the parity space
  `A_{i+j}` — `A_-` on mixed pairs; the true reason is Proposition 3.2(i) applied twice;
- line 607: `u = 1 - q'q` used as an inverse with no proof of `u != 0`, and the value 3
  attributed to Theorem 3.4, which gives only the equality of the two classes;
- line 152: "collapse to two in characteristic 2" without the dimension-one case (all four
  involutions are the identity over `F_2` in dimension 1).

(The 494 fix coincides — both branches fixed that sentence independently, with the same wording.)

Merging this branch alone would drop all seven; its commit message "v80: the paper repairs of
the v79 review" describes its own word-level repairs and does not claim otherwise, but the
combined history invites the misreading.

## Checked and found right (verified here, not taken from the author's report)

The word-level repairs: the Weibel locator moves to `SS1.1 and 9.1` / `S1.1` (the cocycle
vocabulary and `delta circle delta = 0` are in S1.1 of the source; checked against the text);
the three-reasons split of Remark 2.5 (First/Second/Third, no meaning changed); the radical and
quaternion paragraph splits; "although `p ._{sigma_alpha} p != 0`" (the original said "not
because the products vanish", which was wrong at that spot); the `._sigma` -> `._{sigma_alpha}`
subscript in the example that uses the twisted product; the commutator defined at its first
use; "The simplest candidate" (was "first candidate" with no referent); the added sentence "So
the instances with a nonzero derivation are infinite-dimensional"; the Chambert-Loir locator
"defined in [Definition 1.4.12]".

## Answer

The finding is answered by the merge into `review/v79-paper-fixes` (`c1ef1c8`), which combines
both branches' paper changes and keeps both models' work; the joint branch passes the
repository gate on both legs (13 pp, 0 overfull, 0 undefined, text identical to its released
PDF, lake build green, axiom audit and trust scan clean). Re-review of the joint branch is
asked; this branch is superseded by it and should not be merged on its own.
