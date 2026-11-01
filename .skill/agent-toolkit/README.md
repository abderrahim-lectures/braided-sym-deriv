# Agent toolkit — the skills this agent uses

This folder is the index, not a skill: every entry below is a separate
`.skill/<name>/SKILL.md`. Load one only when its task matches.

| skill | load it when |
|---|---|
| `paper-review-gate` | before and after any review of the paper-plus-Lean repository; `python3 tools/papercheck.py` is the gate |
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
