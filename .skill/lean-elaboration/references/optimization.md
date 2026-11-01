# Profile-guided optimization

Use this after reproducing the slow target. Historical examples in
[Evidence](evidence.md) suggest experiments; their thresholds and speedup ratios
are not universal properties of Lean or Mathlib. Check the pinned toolchain's
profiling options and compare matched runs.

## Locate the cost

| Expensive phase | First experiment |
|---|---|
| Import loading | Narrow consumer imports; build to catch implicit instance and tactic dependencies |
| Typeclass inference | Inspect the search goal; supply type information for open metavariables |
| Arithmetic tactics | Isolate the algebraic step; compare monotonicity or targeted automation |
| Simplification | Inspect expensive calls; try targeted rewrites or `simp only` |
| Statement elaboration | Check dependent arguments, aliases, implicit types and repeated definitional equality |
| Congruence search | When the function is known, compare `congrArg f` with broad `congr` |
| Large proof terms | Try a focused helper lemma with a smaller context |

Build-log duration is not a declaration's own elaboration time. Profile with warm
dependencies. To separate statement and proof cost, use a scoped trace or an
isolated reproducer. A diagnostic proof-hole substitution is permitted only in
an untracked copy under project policy, never in delivered source or proof evidence.

## Apply the relevant technique

- **Imports:** text search misses instances, notation and tactic dependencies.
  Validate each removal. Splitting helps only if it changes what consumers load
  or enables useful parallelism; a facade importing everything may cost more.
- **Arithmetic:** compare explicit bounds and `calc` with broad `nlinarith` only
  where the tactic is expensive. A helper over abstract reals can keep
  transcendental expressions out of unnecessary unfolding.
- **Simplification:** use the trace to locate expensive calls; `simp?` can suggest
  a lemma set. Do not replace every ordinary `simp` without a measured reason.
- **Instance search:** unknown carriers need type information, not more instance
  candidates. For repeated closed searches, experiment with a concretely typed
  local cache. Verify scope, visibility, actual reuse and downstream performance
  on this toolchain; a successful sibling-file cache is not evidence for this one.
- **Definitional equality:** using the same existing `abbrev` expected by a
  dependent consumer can reduce repeated unfolding. Check definitional equality
  and consumers. Do not bundle or remove source premises for convenience, or
  change an approved frozen interface outside its versioning process.
- **Helpers and file boundaries:** a smaller context may reduce inference cost.
  A chain of split files can increase import overhead. Preserve mathematical
  meaning and validate consumers as well as the edited file.

## Interpret the experiment

Compare one change against a baseline with the same targets, cache state, timing
method and concurrency. Repeat noisy wall-clock and profiler measurements.
Profiler categories are not immune to contention and need not sum to wall time.
Keep logs and report variability; historical floors are not acceptance criteria.

Distinguish total work from the dependency critical path. Savings off that path
may help throughput without changing wall time on this machine. Summed per-job
elapsed times are not CPU time; use process accounting for CPU measurements.

A heartbeat increase changes a budget, not computational cost. Follow project
policy for overrides. Preserve upstream caches and use exact project-artifact
rebuild procedures instead of `lake clean`. Keep expensive diagnostic commands
out of ordinary compiled modules unless the project intentionally includes them.
Stop or change hypotheses when measurements refute an optimization.
