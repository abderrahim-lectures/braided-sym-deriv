---
name: lean-statement-audit
description: "Authored by <strong>Scott Armstrong</strong>. Compare Lean theorem statements and definitions with their mathematical source, checking hidden assumptions, quantifier and carrier changes, definition meaning, and proof axioms. Use for a requested fidelity or proof-status review, not ordinary tactic debugging."
---

# Lean statement and proof-status audit

Identify the exact Lean exports, source version and passages, and the requested
claim. Read the source and reconstruct its meaning before relying on a previous
audit or implementation summary. If no authoritative source is available, report
that source fidelity cannot be established; typechecking can still be assessed.

## Check the mathematical claim

- Compare every explicit, implicit, and instance binder with the source. Expand
  project-owned structures, predicates, and typeclasses that can hide premises.
  A proof of `A → Step → B` does not prove the requested `A → B` unless `Step`
  is discharged in the delivered result.
- Check quantifier order, shared witnesses, constant dependencies, carriers,
  endpoints, normalization, and the strength of the conclusion.
- Inspect meaning-carrying definitions and notation, not only their types.
  Verify formulas or defining properties on the claimed domain. Choice from an
  existence theorem is legitimate when an arbitrary witness is intended; when
  the source requires a unique or canonical object, verify uniqueness or the
  required independence of choice. Do not demand uniqueness for every use of
  `Classical.choose`.
- Compile the exact export or a focused application and inspect `#print axioms`
  when tools permit. Distinguish expected foundational axioms from `sorryAx`,
  additional project axioms, and expressly accepted external assumptions.
  A clean axiom list does not show that the statement matches the source.

Report source correspondence and proof status separately, with concrete locations,
extra or missing premises, checked commands, and unverified claims. A conditional
helper may be valid without completing the source theorem. An audit request alone
does not require changing statements, creating manifests, or launching reviewers.
Do not call a self-review independent.

## Projects with frozen declarations

Only when the repository already adopts a frozen-anchor manifest or the user asks
for that process, read [Frozen declaration audit](references/frozen-audit.md).
Its identity, quarantine, versioning, and closure gates apply to that profile.
Do not impose them on an ordinary Lean project or create draft proof holes merely
to perform an audit.

## Upstream sources

This skill is adapted from [lean-statement-audit](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/main/skills/lean-statement-audit) in Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills).

Synchronized against upstream commit [`1837b95`](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/commit/1837b95b3d5a9fd8d311367603902ad7fe261adf). The entrypoint and bundled guides retain the Open Math Model consolidation; see [NOTICE.md](NOTICE.md) for attribution and adaptations.
