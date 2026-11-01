# A repeatable Lean build measurement

Use for a requested repository benchmark or trend report. For one slow file,
start with its warm profile instead. Measurement does not require applying fixes.

## Setup

Record revision, dirty state, Lean/Mathlib versions, targets, host, timing tool,
cache state and concurrency. Inspect Lake targets and root imports: a default
build may cover only part of the source tree.

For a committed-source size snapshot, use the bundled
[scripts/count_lean_lines.py](scripts/count_lean_lines.py); read `--help` first.
It counts Git content, not uncommitted edits. Its module-header count is
informational unless this project actually requires the module system.

## Build

Use the repository's guarded project-only rebuild procedure. Prepare dependency
caches separately; first-time dependency compilation is not a project regression.
Preserve pins and upstream artifacts. Do not use `lake clean` or `lake update`
for measurement. Before invalidating project artifacts, resolve the exact paths
and verify they belong to the project rather than its dependencies.

On a system with GNU time, a representative measurement is:

```sh
/usr/bin/time -v <project-build-command> > <unique-log-path> 2>&1
```

Record exit status, wall time, user/system CPU, peak RSS, warnings and target
coverage. Unexpected dependency compilation invalidates a project-only comparison:
label the different scope or stop your own benchmark and repair setup. Never
terminate another user's processes. Avoid conflicting artifact writes in a shared
checkout. A process listing alone neither proves contamination nor comparability.

## Confirm and compare

Extract slow modules from the build log, then profile a small number serially
with warm dependencies. Record the expensive phases and significant events.
A slow job in a parallel build is a candidate, not an own-file hotspot diagnosis.

Summed module durations are **summed job elapsed time**, not CPU time. Some jobs
may be unlogged. Their sum divided by wall time is only a rough overlap measure,
not a reliable core count. Use process CPU accounting for CPU measurements.

Compare trends under matched targets, versions, cache conditions and timing
methods, or state the differences. Repeat noisy runs. Heavy-tail thresholds such
as 10/20/30 seconds are optional summaries, not universal quality gates.

## Report

Use the project's format or a concise report with setup, commands, build success,
timing and memory, slow targets, confirmed causes and comparability limits.
Include file counts or directory breakdowns only if useful. Separate observations
from proposed fixes; do not promise a speedup before an A/B experiment.
