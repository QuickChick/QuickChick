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
actual grade. The proof shows that resolving a call can only tighten or
preserve the bound in either density direction. This keeps the bound admissible,
though it may be too weak to prune before dependency resolution.

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
When a committed producer call needs a dependency grade, the bound should
resolve that dependency then, using its actual mode and applied relation. It
should not postpone all dependency work until a leaf. Completed scoring sorts
the candidate's steps before discovering dependencies, however. Adding a future
step can change which dependency encounters a provisional cycle grade first.
The scorer now records whether a completed memo entry read such a grade. For
the current heuristic, an applied relation is checked for an existing instance
before its generic declaration is scored; omitted applied arguments alone do
not show that this generic score changes within one derivation. The unresolved
bound question is whether a cycle-dependent grade computed from a partial
candidate remains valid after other calls are discovered. A future policy that
scores applied calls directly will also need a full applied/context key. Until
these cases are established, the proved optimistic grade is used for an
uncertified call. Direct checks, matches, unconstrained
bindings, lets, and direct recursive calls have fixed local grades. Some of
these steps still trigger dependency discovery for code generation, but their
own grade is fixed.

`test/dependency_cycle_laws.v` states the relevant graph argument precisely.
If evaluating a key has visited every dependency it may score, a later unseen
key cannot newly become part of a cycle with that completed key. For an
acyclic dependency graph, deterministic score equations have a unique result,
regardless of evaluation order. The current constructor scorer visits every
generated candidate and its step dependencies before marking a key done;
candidate-local memo snapshots make the cycle marker conservative. A direct
source-to-model correspondence test is still needed before the marker enables
production pruning. A cycle-dependent result remains uncertified by this
argument.

`test/scoring_cycles` demonstrates why that distinction matters. For the same
generator memo key, resolving one side of an asymmetric mutual relation first
gives `Partial`, while resolving the other side first gives `Total`. A connected
parent derivation reaches both results in separate candidate-local scoring
passes. A prefix bound that treated the earlier `Partial` as permanent could
prune a completion whose call is `Total`; `test/pruning_bounds.v` computes the
resulting bound reversal. This is a cycle-order effect, not an applied-argument
cache collision. The public scheduler still ranks with its existing heuristic;
it does not prune from these partial grades.

Exact scores for a mutual group cannot be read from the provisional memo
entry. A possible context-based scorer would first fix the proof context,
available instances, full applied relation and mode keys, and the candidate
schedules for each member. It would then score every candidate symbolically in
terms of the other members' scores and solve the group together. Acyclic calls
keep their existing exact on-demand scores. For a cyclic group, the scoring
policy must also say what a cycle means: equations such as `A = B` and `B = A`
have several solutions even on the five-grade density scale. Choosing the
first DFS seed is not a context-only answer. A direct recursive-call grade,
or an explicitly chosen fixed-point convention with a termination/productivity
interpretation, can make the meaning deterministic. Either choice may change
the present ranking and needs separate compatibility review.

The five-grade density component admits a finite SCC analysis once its mode
alternatives and aggregation are fixed. It does not follow that the whole
BudgetAware score has a finite exact fixed point: additive fabrication and
dependency counts can yield equations such as `x = 1 + x`. Lexicographic
selection among candidate schedules also requires checking whether its
equations are monotone before using iteration. A practical first probe should
enumerate the small asymmetric mutual fixture's complete mode graph, solve
its density equations under a stated cycle rule, and compare every selected
constructor and parent score with the current order-dependent results. For the
current pruning work, use the optimistic grade for a cycle-dependent call and
the exact grade only for a certified cycle-independent call. In generator
minimization the optimistic density is `Total`; in checker/enumerator
minimization it is `Checking`. A prefix bound must also give unresolved calls
the best possible values for every earlier lexicographic coordinate; an
optimistic density alone cannot rescue an overestimated selectivity or
fabrication bound. This deliberately weakens pruning until the mutual group
has a stable scoring rule. Do not replace the bound with a provisional memo
grade merely because the call has returned during one traversal.

The internal ranking module now builds this conservative prefix key from
certified call-site grades, unresolved calls, and a lower bound on committed
variable uses. It compares an incumbent with that key without candidate IDs
and prunes only on a strict improvement. The ranked-key test checks every
resolution of up to two unknown grades, every possible appended grade, both
density directions, and all built-in policies. The typed prefix-search test
compares each bound with every descendant of a five-premise fixture and
checks that callback pruning retains its optimal modes. With a deliberately
unknown producer dependency, checker counted-density search visits 53 nodes
and 13 leaves versus 61 nodes and 16 leaves without score pruning; the other
built-in policies make no cuts on this fixture. These grades are synthetic;
the real-scorer results below are the evidence for the production adapter.

The prefix search also exposes the number of unprocessed positive hypotheses
whose variables are all bound. Each must become a check: the environment only
grows, and maximal-output scheduling cannot select an already bound output.
Eager checking is disabled here, so none has appeared in the prefix steps.
The bound adds one `Checking` grade per such hypothesis. Negative hypotheses
are excluded because their check grade differs. Exhaustive typed search checks
this floor against every descendant, including a nested-argument case.

`NewUnifyQC.type_to_schedules` now forwards optional observation and pruning
callbacks after its variable correction, together with the fixed match and
equality preludes. The ordinary command path supplies neither callback and
keeps its previous search behavior. A typed test checks that observed terminal
schedules equal the returned candidates, that open corrected prefixes remain
prefixes of their descendants, and that a nonempty match prelude is visible
at this boundary.

The constructor scorer now uses those callbacks when the internal
`QC_SCHEDULE_SCORE_PRUNING` environment switch is set. It scores completed
leaves with the ordinary scorer in a temporary memo session. For a committed
step with a fixed grade it uses that grade; for a nonrecursive producer it
resolves the dependency on demand and uses its grade only if the computation
never read a provisional or cycle-dependent memo entry. Other calls keep the
optimistic grade. The bound includes fixed match and equality preludes and
the committed variable-use count. Temporary scoring restores memo and
uncertainty state before final candidate scoring. Per-constructor bound probes
cache a call-site result by corrected step and schedule mode, so repeated
prefixes do not rederive the same dependency merely to bound it.
The forced-check floor comes from the scheduler's environment before variable
names are corrected for display; it does not infer bindings from renamed steps.

`QC_SCHEDULE_SCORE_PRUNING=verify` enumerates all leaves and checks each
bound against every completed descendant, then compares the scores seen at
the leaves with final candidate rescoring. Setting it to `1` enables strict
cuts. The default is off. The maintained three-premise fixture scores four
root candidates without cuts and one with the switch on, selecting the
same best density and variable-use score under default and counted-density
ranking. The connected mutual-cycle and public derivation fixtures pass the
verification mode; see `test/scoring_pruning`. The five-premise saturation
fixture makes no real-score cuts under either ranking. This adapter has not
yet been proved sound for all typed unification and source rewrites, nor
shown to reduce end-to-end derivation time. The extra leaf and prefix scoring
can cost more than the cuts save. Keep the switch internal until wider
correspondence and performance tests justify enabling it by default.

The reduced SemGuS fixture merges `eval` with itself and merges the result
with `eval` again. With the internal switch set, `Valid Schedules` now sends
its selected constructor through the same bound-aware scheduler as derivation.
The verifier checks all 12 root leaves over 25 prefixes, finds no bound
violation, and selects the same candidate as the unpruned run. It makes zero
cuts. Score probes suspend nested experimental pruning while resolving
dependencies; otherwise verification repeatedly re-enters those searches and
multiplies the work without improving the root bound. The ordinary diagnostic
shares dependency memo state across candidate scores and took 1.2 seconds in
one local run. A comparable internal `baseline` uses the same search as
pruning but no bounds. With all candidate reuse disabled it took 8.3 seconds.
The scorer now shares completed, cycle-independent dependency entries across
candidates. It also caches grades for equal multisets of scoring steps:
`schedule_density` visits those steps in a fixed sorted order, then the cache
restores each candidate's original order for ranking. Multisets with duplicate
steps are scored afresh. Verification recomputes these scores independently
and checks for disagreement. With reuse, the baseline took 2.3 seconds,
verification 15.4 seconds, and pruning 2.5 seconds. The ordinary diagnostic's
time is not a like-for-like pruning comparison.
The bound-grade cache had 26 hits and 3 misses; the mode cache hit 10 times
across 12 leaves, which had only two distinct step multisets. Pruned ranking
reuses completed-leaf annotations and rescores only the winner to recover its
dependency memo. In the reused run, bound, leaf, and final scoring cost 0.28,
1.26, and 0.57 seconds of CPU time.
The verifier still independently rescores all candidates. All 12 leaves have
the same density, counted-density histogram, and variable-use score:
`Checking`, `(1,0,0,3,0)`, and one use. Strict score pruning cannot discard
those ties while candidate IDs come from the final sorted candidate list.
This fixture stresses recursive score resolution, not discrimination between
schedules; the bound makes no cuts. Recursive score resolution remains
expensive.

`test/prefix_adapter_laws.v` proves the list-level adapter rule: stepwise
conversion distributes over appended choices, and sorting unconstrained
blocks preserves an earlier prefix when that prefix ends in a producer, check,
or match. It also proves variable-use counts are unchanged by an injective
renaming of binders and occurrences. The actual converter allocates new names
for constrained-output matches on each call, so equality of observed prefixes
must be checked up to that renaming. The typed oracle checked 711,239
prefix–descendant pairs across small footprints and focused fixed, indexed,
negative, and nested-pattern cases; one pair required alpha-renaming. This is
an adapter model and executable correspondence check, not a formal
verification of the OCaml converter.

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
