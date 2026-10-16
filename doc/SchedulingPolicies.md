# Schedule ranking and constructor weights

Complete schedules are ranked separately from candidate generation. The
`ScheduleRanking` OCaml module compares measured features; the scheduler collects
those features. This boundary permits testing ranking without running derivation.

The existing `QC_SCHEDULE_RANKING` environment setting is preserved:

| Value | Primary criterion | Secondary criterion |
| --- | --- | --- |
| `density_then_vars` (default) | Density | Fewer uses of previously bound variables |
| `density_only` | Density | None |
| `vars_then_density` | Fewer uses of previously bound variables | Density |
| `vars_only` | Fewer uses of previously bound variables | None |

Generation and theorem testing prefer higher density. Checking and enumeration
prefer lower density. Densities, in ascending order, are Checking, Backtracking,
Neutral, Partial, and Total. A producer uses the lowest density among its steps;
a checker or enumerator uses the highest. An empty producer schedule is Total;
an empty checker or enumerator schedule is Checking. Candidate identifiers break
remaining ties, preserving deterministic selection from the generated list.
Existing aliases and unknown-value fallback to the default are unchanged.

`QC_SCHEDULE_TRACE=1` reports the selected policy, candidate count, identifier,
density, and variable-use count. `QC_SCHEDULE_TIE_REPORT=1` enables tie diagnostics;
`QC_SCHEDULE_TIE_LIMIT` limits their output (default 3; 0 means no limit).
These are existing diagnostic environment settings, not new Rocq options.

## Search limits

The earlier search uses a different score: fewer checks, then shorter schedules,
then fewer unconstrained instantiations. It prunes with lower bounds and an
environment memo before final ranking. The current path also takes at most 1000
candidates before deduplication. Final ranking therefore selects among the
surviving candidates; it is not a guarantee of the global optimum under any of
the four ranking policies.

The comparison refactor preserves this behavior. A complete modular scoring
interface must give each selected policy an admissible bound: the bound at a
search node must be no worse than every reachable completed score. Custom
policies should retain score-based pruning through that contract. Dominance
memoization needs a separate condition; a lexicographically better prefix need
not remain better under a common extension containing maxima. Dependency and
validity checks remain independent. Small exhaustive searches provide a test
oracle for bounds, rather than a default execution mode for custom policies.
A candidate cap must remain visible in any optimality claim.

At pinned Specimen revision `121cf234`, scoring bundles explicitly associate
comparison and aggregation with pruning strategy, including a no-pruning option.
QuickChick does not yet provide that bundle interface or arbitrary Rocq scorers.

## Constructor weighting

Scheduled generation currently gives base constructors weight 1 and recursive
constructors the current size. Enumeration and checking do not use these random
weights. Fuel and base/recursive branch selection are separate safeguards and
must remain independent of distribution policy.

The planned weighting boundary is a function used by code generation, separate
from schedule ranking. The current rule remains the default. Initial extensions
can be named policies; a Rocq weight function could instead be referenced in
generated code, avoiding evaluation of arbitrary Rocq functions in the plugin.
Its argument contract, zero/all-zero behavior, and extraction tests still need
design and validation. This document does not introduce a new weighting setting.
