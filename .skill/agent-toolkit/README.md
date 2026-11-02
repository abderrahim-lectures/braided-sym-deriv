# Agent toolkit — the skills this agent uses

This folder is the index, not a skill: every entry below is a separate
`.skill/<name>/SKILL.md`. Load one only when its task matches.

| skill | load it when |
|---|---|
| `paper-review-gate` | before and after any review of the paper-plus-Lean repository; `python3 tools/papercheck.py` is the gate |
| `bsd-exact-algebra` | before recomputing any dimension of Der / BSDer / ADer / the Section-4 examples: `python3 .skill/bsd-exact-algebra/cases.py` reproduces every finite number of the paper (and two beyond it) in 0.3 s; `BASELINE.md` lists the closed findings and the open question's exact state |
| `paper-lean-sync-review` | a full deep review: word-by-word reading, claim-by-claim verification, paper↔Lean ledger, citation audit, blind spots |
| `lean-statement-audit` | comparing Lean statements with a mathematical source |
| `lean-workflow` | ordinary Lean coding: finding lemmas, fixing proofs, naming |
| `lean-project-architecture` | module boundaries, campaigns, release structure |
| `lean-elaboration` | a measured performance investigation |

## The improvement loop (do this after every task)

1. **Note the friction.** Where did the work stall: a missing lemma, a wrong
   tactic, a broken build, a claim that was false, a tool that lied?
2. **Patch the skill that owns it.** One concrete edit — a command that works,
   a pitfall with its fix, a checklist item — in the `SKILL.md` that failed to
   prevent it. Not a rewrite.
3. **Log it** in `CHANGELOG.md` with the date and the evidence (file, command,
   number), so a later session can see what was learned and undo it if wrong.
4. **Keep the gate honest.** If a check moves into `tools/papercheck.py`, say so
   in the skill so nobody runs the old manual step.

Lessons already folded into `paper-review-gate` (2026-11-01): `lean` needs
`LEAN_PATH=$PWD/lean:$LEAN_PATH` for files that import the library; `#print
axioms` on a name outside its namespace must be qualified or the file fails to
elaborate; `native_decide` leaves a compiler-trust axiom (`…_native.native_decide.ax_1_1`)
that `#print axioms` reports; `lake build` is not reproducible here (no manifest).

## Vendoring

**All of them are versioned here.** `git ls-files .skill | wc -l` counts the
tracked files; at the v73 review every skill directory (`agent-toolkit`,
`bsd-exact-algebra`, `lean-elaboration`, `lean-project-architecture`,
`lean-statement-audit`, `lean-workflow`, `paper-lean-sync-review`,
`paper-review-gate`) was in the index, and the four `lean-*` skills carry their
`references/`, `agents/` and `LICENSE` files with them. The earlier paragraph
here claimed the five catalog skills were not vendored; that was false on both
counts and sent a reader looking for a checkout that does not exist. A skill
loaded from the catalog is copied into this folder and, from then on, is this
repository's to edit — so edit it here.
