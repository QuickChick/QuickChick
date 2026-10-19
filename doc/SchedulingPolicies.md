# Schedule ranking and constructor weights

Complete schedules are ranked by the `ScheduleRanking` OCaml module. The active
scheduler constructs candidates lazily and chooses every eligible unbound
output of a selected positive hypothesis. It also removes redundant orders of
independent plain hypotheses. `QC_SCHEDULE_POR=0` disables that order reduction
for diagnosis; it does not change output selection.

The existing `QC_SCHEDULE_RANKING` environment setting is preserved:

| Value | Primary criterion | Secondary criterion |
| --- | --- | --- |
| `density_then_vars` (default) | Density | Fewer uses of previously bound variables |
| `density_counts_then_vars` | Density | Fewer steps at each worse density, then fewer variable uses |
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

The opt-in `density_counts_then_vars` policy breaks a worst-density tie by
counting annotated steps at each density, starting with the worst grade for the
derivation direction. It counts a recursive dependency's computed density once
at the call site; it does not expand the dependency's internal schedule. Thus
the count is bounded by the selected schedule's steps. This is a measure of the
chosen calls, not a count of underlying constraints. It uses the scheduler's
current recursive density annotations, including its existing treatment of
recursive cycles.

`QC_SCHEDULE_TRACE=1` reports the selected policy, candidate count, identifier,
density, and variable-use count. `QC_SCHEDULE_TIE_REPORT=1` enables tie diagnostics;
`QC_SCHEDULE_TIE_LIMIT` limits their output (default 3; 0 means no limit).
These are existing diagnostic environment settings, not new Rocq options.
The trace also prints `selected-counts=Checking,Backtracking,Neutral,Partial,Total`
for the counted-density policy (as five integers).

## Search limits

The active search branches over the next hypothesis, commits its typed steps,
and skips orders that differ only by a certified independent swap. It does not
yet use a score bound or an environment-dominance memo. It stops after 1000
candidates before deduplication and warns on truncation. Final ranking selects
among those candidates, so a capped run has no global-optimality guarantee.
Order reduction can change candidate identifiers; indexed alternatives refer
to the reduced candidate list.

Policy-driven branch-and-bound is still being developed. A policy bound must
be no worse than every completed descendant of the actual typed search node.
The internal prefix-pruning callback is exercised by a narrow variable-use
test, but public derivation does not use it. Recursive dependency scores need
stable full-mode keys before density can safely prune. Custom policies should
retain score-based pruning through the same admissibility contract. Small
exhaustive searches serve as the validation oracle.
The counted-density policy currently ranks completed candidates only; its
histogram is not used as a partial-node pruning bound.

`test/pruning_bounds.v` proves the candidate prefix bounds for both density
directions and the counted-density key. Under a committed prefix with finalized
step grades, every completed descendant appends nonnegative grade counts;
generation's worst grade can only worsen, and checking's can only worsen in
its comparison direction. The file also proves that a stateful nonnegative
variable-use scan cannot reduce its accumulated count. Candidate identifiers
are excluded from the bound, so equal scores must remain searchable.
The proof also shows that a strictly better incumbent remains better than any
completion whose score is componentwise above the node bound.
It also proves a conservative bound with unresolved recursive grades: treat
each such call as the best possible density (`Total` for generation,
`Checking` for checking) and count it in no histogram bucket. Once the
dependency's grade is known, replace that optimistic contribution with its
actual grade. This keeps the bound admissible, though it may be too weak to
prune before dependency resolution.

For plain positive direct-variable relations, the proof additionally gives
`committed checks + max(0, remaining hypotheses - unbound variables)` as a
lower bound on check count: each remaining non-check consumes at least one
fresh variable. This stronger formula needs a separate typed certificate before
use with indexed arguments, forced bindings, negative premises, or rewriting.
The current plugin is not formally verified against the proof's assumptions:
converted prefix steps and recursive dependency grades must remain unchanged
in descendants. A typed exhaustive fixture checks the counted key against
every descendant, but that is evidence for the fixture, not a replacement for
the adapter proof. No public score pruning is enabled.
In particular, completed scoring sorts a candidate's steps before discovering
recursive dependencies. Adding a future step can change which dependency is
encountered first, including the provisional grade used for a cycle. A prefix
bound must therefore treat a nonrecursive producer call as unresolved unless
its grade is certified independently of the remaining steps. Direct checks,
matches, unconstrained bindings, lets, and direct recursive calls have fixed
grades under the current scorer; this is the first useful certified subset.

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
