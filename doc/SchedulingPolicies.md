# Schedule ranking and constructor weights

Complete schedules are ranked by the `ScheduleRanking` OCaml module. The active
scheduler constructs candidates lazily and chooses every eligible unbound
output of a selected positive hypothesis. It also removes redundant orders of
independent plain hypotheses. `QC_SCHEDULE_POR=0` disables that order reduction
for diagnosis; it does not change output selection.

`QuickChick Scorer <name>.` (or `QC Scorer <name>.`) selects the scorer for
later derivations in the file. The choice follows undo and backtracking, is not
exported to files that import this one, and a prepared `quickchick` test keeps
the schedules it was prepared with. An unknown name is an error that lists the
scorers. The `QC_SCHEDULE_RANKING` environment variable has been removed.

| Scorer | Primary criterion | Secondary criterion |

| --- | --- | --- |
| `density_then_vars` (default; also `density`) | Density | Fewer uses of previously bound variables |
| `density_counts_then_vars` | Density | Fewer steps at each worse density, then fewer variable uses |
| `density_only` | Density | None |
| `vars_then_density` | Fewer uses of previously bound variables | Density |
| `vars_only` | Fewer uses of previously bound variables | None |
| `budget_aware` | Specimen's completed BudgetAware score | See below |
| `cardinality` (experimental) | Filters by acceptance class | See below |

Generation and theorem testing prefer higher density. Checking and enumeration
prefer lower density. Densities, in ascending order, are Checking, Backtracking,
Neutral, Partial, and Total. A producer uses the lowest density among its steps;
a checker or enumerator uses the highest. An empty producer schedule is Total;
an empty checker or enumerator schedule is Checking. Candidate identifiers break
remaining ties. They follow search order, so among equal scores the first
schedule the search finds wins.
The former environment aliases remain accepted as names, such as `vars_density`.

### Scorers written in Rocq

Any other name must be a constant of type `QuickChick.SchedulingPolicy.policy`
(`src/SchedulingPolicy.v`). A policy chooses its own score type `S`; its
`scorer` scores each step of a candidate, combines them into a schedule score
(`score_schedule` also sees the whole schedule), and compares scores. Lower is
better, and among equal scores the first candidate found wins.

`QC Scorer my_policy.` compiles the policy once. The plugin extracts the
policy's scorer, comparison and bound, with the view types mapped onto the
plugin's own OCaml types, compiles them with `ocamlfind ocamlopt -shared`, and
loads the result with `Dynlink`. Scoring then runs at native speed. Compiled
objects are cached in the system temporary directory, under
`QuickChick-scorers`, by a digest of the extracted code and of the plugin.

The policy receives read-only views of each candidate: its steps with their
sources, grades and patterns, the constructor's locals and original inputs,
and each dependency request marked `SuppliedInstance` when an instance
resolves in context and `Pending` otherwise. Recursive steps add no request;
the policy sees their source category. `test/compiled_density.v` writes the
built-in `density_then_vars` ranking as a policy; on Cedar it makes the
built-in's selection for all 862 constructor modes.

A policy may declare, in `policy_grouping`, how its score combines over
footprint-disjoint hypothesis groups: a unit, a combine function, and its
comparison as a lexicographic list of fields, each `Additive` (a sum) or
`Extremal` (a maximum or minimum). The plugin then searches each group
separately and keeps a Pareto set per group, as it does for the built-in
scorers. The plugin trusts these laws. `QC_SCHEDULE_GROUPS=verify` checks
the grouped result against joint search; set `QC_SCHEDULE_MAX_CANDIDATES=0`
with it, since the capped joint search can miss the grouped winner. With
`policy_grouping := None` each constructor is searched jointly.

A policy is pruned with its `lower_bound` when `policy_bound_sound` proves
that bound admissible: no complete schedule below a search node scores better
than the bound (`bound_admissible`, over `completes` in
`src/SchedulingPolicy.v`). A search node lists its committed steps, each with
its grade and whether that grade is final, the remaining hypotheses, how
many of them must become positive checks, and how many further variable uses
every schedule below incurs (`step_uses` defines the engine's count). The plugin cuts a branch when the
best schedule found so far is no worse than the bound; since the first of
equal scores wins, the selection is unchanged. Without a proof the policy
runs unpruned, under the 1,000-candidate cap. A proof that depends on axioms,
such as an admitted lemma, still enables pruning, and selecting the policy
warns about it. `QC_SCHEDULE_SCORE_PRUNING=verify` checks every bound against
every completed descendant.

`src/SchedulingPolicyLaws.v` builds policies with proved bounds.
`fold_policy M f floor kind` combines step scores in an ordered monoid `M`
(`nat_max` and `nat_sum` are provided); a step score may depend on the steps
before it. Its bound combines the committed steps' scores, masking uncertain
grades, and an optional `floor` that every positive check reaches, counted
once per forced check (`fold_bound_admissible`). `lex_policy p q` compares
two policies lexicographically, with a proved bound when both have one
(`lex_bound_admissible`). `uses_policy` sums `step_uses`; its bound adds the
node's future uses to the committed ones (`uses_bound_admissible`). All
declare their grouping. `test/compiled_density.v` builds `density_then_vars`
as `lex_policy` of a maximum of grades and `uses_policy`. On Cedar it makes
the built-in's selection on every key, pruned and in verify mode, with no
bound violation, and it prunes exactly as much as the built-in. It takes
20 s against 10 s, the cost of quoting each search node for the policy.

### Cardinality ranking (experimental)

`QC Scorer cardinality` reads a schedule as a query plan. Counts
are growth classes in the size bound (`1 < fin < poly < exp`). Type classes
come from the inductive definitions. Each completed relation mode records its
solution count for given inputs, from its constructors' chosen schedules: a
constructor that starts by matching an input recurses on smaller inputs, and
such constructors with different head constructors are alternatives. A filter
(a check, a refutable match on a produced value, or a producer fed generated
inputs) has acceptance admitted/reaching as a class; a variable nested under
a constructor in a checked argument is admitted only by the relation's
constructors with that head there. A check is also bounded by its scarcest
generated variable's conditional count: how many values that variable can
take when everything else in the relation is fixed, from the relation's
definition (a variable also occurring elsewhere in the conclusion is fixed;
one pinned by a hypothesis takes that hypothesis's count). The score counts filters with acceptance
`1/exp`, then `1/poly`, then unknown, then constant; lower is better, and
candidate identifiers break ties. A candidate whose free generation of a type
lacks an instance is excluded. Score pruning does not apply yet, so the
unpruned candidate cap does (`QC_SCHEDULE_MAX_CANDIDATES` overrides it for
diagnosis; 0 removes it). `test/cardinality_ranking` checks the case that
BudgetAware ties: inventing a list and then checking the relation that
determines it. The prototype and Cedar measurements are in
`audit/3.0-scoring/cardinality/`.

### BudgetAware ranking

`QC Scorer budget_aware` ranks each
constructor's candidate schedules by `BudgetAwareScore`, the port of
Specimen's completed six-field score (selectivity, density, fabrication,
locality, input-check dependencies, variable dependencies), compared
lexicographically. Ties keep the lowest candidate identifier. A candidate
the scorer cannot represent, such as one with a `let` step, is a user error
rather than a fallback to density ranking.

A relation's score combines, over the same input-pattern coverage leaves the
density ranking uses, the best score among each leaf's constructors; an
uncovered leaf scores Partial, as in Specimen. It is stored with the
relation's completed memo entry. A dependency contributes its stored score
only when that entry is complete and cycle-independent. Self-recursive,
mutually recursive in-progress and cycle-dependent calls, and existing
instances without a measured schedule, are unknown and score as Partial with
no fabrication. Constructor schedules are chosen per constructor, as in
Specimen; this is not a joint optimum over the relation's aggregate.

Grouped search uses BudgetAware's grouped policy in this mode, and
`QC_SCHEDULE_GROUPS=verify` compares best BudgetAware scores with the joint
search. Theorem testing still ranks by density.

Score pruning (`QC_SCHEDULE_SCORE_PRUNING`, below) also applies here. A
prefix's bound is BudgetAware's own score of the committed steps, with an
unstable dependency at its best score and a forced check at Checking
density: a step's score does not depend on its position, and each variable
is produced once, so no field improves when steps are added. Because the
first fields often tie for every candidate, variable dependencies get the
floor's look-ahead: a non-input variable the prefix binds is counted for each
remaining hypothesis that mentions it, and an unbound variable that is a bare
argument of k remaining hypotheses is counted k - 1 times. The bound is
computed first without deriving dependencies, which is already admissible,
and with them only when selectivity ties. `test/pruning_verify_budget`
checks it in verification mode.

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
`QC_SCHEDULE_SELECTION_LOG=<file>` appends one line per selected constructor
schedule (relation, output positions, mode, constructor, schedule), for
comparing rankings across runs.

Completed dependency entries whose derivation read no provisional grade from
outside itself are shared by all candidates of a top-level derivation; other
entries are recomputed per candidate, so a candidate's score does not depend
on which candidates were scored before it. `QC_SCHEDULE_REUSE_STABLE=0`
disables the sharing for diagnosis. Theorem candidates share these entries too.
A shared entry is copied without the entries added while it was derived, such
as a mutually recursive relation that is cycle-dependent inside it; a later
derivation rederives those on demand, and code generation, which finds a
schedule's dependencies in the memo, first restores them.

A cycle-dependent derivation is determined by its key and the memo entries it
read from outside itself: the in-progress ancestors it saw and the completed
entries it used. It is recorded with those reads and the memo entries it
added, and replayed wherever the same reads observe the same values and none
of the keys it derived is in progress. `QC_SCHEDULE_CONTEXT_REUSE=0` disables
this; over the full test suite the distinct selected schedules are identical
either way.

Selecting the best theorem schedule (`quickchick` with index 0) scores
candidates lazily in identifier order. A candidate's density is the minimum
grade of its steps and its variable uses are structural, so once the grades
seen so far bound it no better than the incumbent, which precedes it and wins
ties, its remaining dependency modes are not derived. Other indices, the
listing tactics and `try_all_quickchick_schedules` rank every candidate.
`QC_THEOREM_LAZY_SCORING=0` disables lazy scoring; under
`QC_SCHEDULE_SCORE_PRUNING=verify` the lazy and exhaustive selections are
compared.
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

### Independent hypothesis groups

When a constructor's hypotheses split into groups that share no unbound
variables (after unification aliasing, and including variables named in other
variables' types), constructor derivation searches each group separately. A
group's local schedules are scored on their own. Density combines across
groups by its extremum and the other ranking fields add, so a group's single
best schedule is not always part of the best combination. Each group therefore
keeps every candidate not dominated in both density and the remaining fields.
A dynamic program over combined density then yields at most five combinations,
which are ranked as ordinary candidates. The best complete score is unchanged.

Combinations place groups one after another, so ties between equal-scoring
schedules can select a different order of independent steps than the joint
search. `QC_SCHEDULE_GROUPS=0` restores the joint search;
`QC_SCHEDULE_GROUPS=verify` runs both and fails if the best score differs or a
grouped candidate is not one the joint search produces without order
reduction, up to fresh-name renaming. `QC_SCHEDULE_GROUPS_LOG=<file>` appends
one line per verified constructor search. The prefix score-pruning modes
still use the joint search.

Theorem testing uses the same grouped search. In `quickchick n i`, `n` is the
test size and `i` a schedule index; `quickchick_idx i` keeps the default size.
Indices, `try_all_quickchick_schedules`, and the `schedules`,
`valid_schedules`, `Derive Schedules` and `Derive Valid Schedules` listings range over the
grouped combinations, not every joint ordering, so a theorem can offer fewer
schedules than before. An out-of-range index is a user error.
`QC_SCHEDULE_GROUPS=0` restores the full list. Under `verify`, theorem testing
also checks that the best score matches the joint search.

#### Policy contract

`GroupedScore` implements the group search for any score type. A policy gives
a unit, a `combine` function and a lexicographic list of fields, each declared
`Additive` or `Extremal`. Two laws make the search exact:

1. Separability. A schedule built from footprint-disjoint groups and the
   shared steps (constructor matches and equality checks) scores as the
   `combine` of their separate scores, in any order. `combine` is
   associative and commutative, with the unit as identity.
2. Field order. Each field combines on its own. Combining both sides with the
   same score preserves an `Additive` field's strict order and its ties, as a
   sum does. It preserves an `Extremal` field's non-strict order only, as max
   or min do.

From these, a candidate dominates another when, field by field, an additive
field is strictly better, or equal with the rest dominating; or an extremal
field is no worse and the rest dominate. Each group keeps its undominated
candidates. States with equal extremal fields receive the same future
combinations, under which additive fields keep their order, so the dynamic
program keeps one state per class of extremal values.

Declaring a max field `Additive` is unsound: it treats a lead that combination
can absorb as decisive. `GroupedScore.check_laws` tests the field and
combination laws on sample scores. It cannot test separability, which depends
on the scorer.

The built-in rankings are instances: density is extremal; the histogram and
variable uses are additive. BudgetAware is also an instance
(`BudgetAwareScore.group_policy`). Selectivity, fabrication and both dependency
counts are additive; density and locality are extremal. Its scorer is
separable because each step naming a variable lies in that variable's group,
so selectivity's per-variable sets do not overlap, and the shared steps
produce no variable and pin none. It is used for selection under `QC Scorer budget_aware`.
The test `plugin/test_grouped_score.ml` checks the generic search against
brute force on random policies, BudgetAware's laws and exactness, and
separability on fixture schedules.

Custom Rocq policies have no grouped instance yet. A policy that inspects the
whole schedule, or whose score depends on the order of independent steps,
must declare its laws or keep the joint search.

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

A separate completed-score library now mirrors the pinned Specimen
`BudgetAwareScore` on concrete QuickChick steps. Fifteen differential cases
match the Lean reference, including all six coordinates, finite-pinning
analysis, recursive locality, fabrication propagated from an enumerator,
and coverage aggregation; see `test/budget_aware`. The scorer also accepts
real scheduler candidates, including their match and equality preludes.
The unifier exposes prepared fixed inputs and dependency requests retain
applied type arguments. The `budget_aware` ranking above uses this library with
completed dependency scores from the memo. The search bound must still be
built and checked separately.
Unsupported QuickChick-only `let` and defined-source
steps return an error rather than silently receiving an approximate score.

Finite pinning follows Specimen's ground-constructor rule. The environment
lookup selects the requested member of a mutual inductive, intersects ground
argument positions across its constructors, and returns no pins if translation
fails. It caches only within a derivation, so undo cannot retain stale metadata.
No deeper finite-domain inference is planned without evidence that it improves
selected schedules.

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

The constructor scorer now uses those callbacks unless the internal
`QC_SCHEDULE_SCORE_PRUNING` environment switch disables them. It scores completed
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
the leaves with final candidate rescoring. Setting it to `1` enables cuts.
Pruning is on by default, because exact selection without a candidate cap
needs it to stay bounded; `0`, `false`, `no` or `off` disables it.
Cardinality ranking has no bounds and ignores the switch. With pruning on,
and in its verification mode, searches have no candidate cap; without pruning
(and under cardinality ranking) the 1000-candidate cap remains. With pruning on, a constructor whose
hypotheses split into several independent groups is still searched group by
group, without cuts; a single group is searched jointly and pruned.
Verification mode always searches jointly.

Cuts are exact, not only optimal in score. Candidate identifiers follow
search order, so the incumbent precedes every candidate of a node explored
after it; a node is cut when the incumbent is at least as good as its bound,
and the incumbent also wins every tie. Each dependency derivation prunes
against its own incumbent, at every nesting level. The variable-use bound adds
uses that every completion must incur: a variable bound by a committed step
counts once in each remaining positive hypothesis that mentions it, either in
the step source or, inside a constrained output, in the equality check that
replaces it; and an unbound variable that is a bare argument of k remaining
positive hypotheses counts k - 1 times, since only one of them can produce it.
`plugin/test_prefix_search.ml` checks these bounds against every completed
descendant and checks that tie pruning selects the exhaustive winner for each
built-in policy. The release audit proves them in Rocq
(`audit/3.0-scoring/rocq-prototype/`): `DensityPrefixBound.v` shows the bound
admissible and cuts exact for every built-in policy, `BudgetAwarePrefixBound.v`
does the same for BudgetAware, including selectivity and the look-ahead's
counting argument, and `DensityLookahead.v` applies that argument to the
density bound. Their premises are what verification mode checks: committed
steps and forced checks keep their grades in every completion, a variable is
produced at most once, outputs are unbound when a hypothesis is scheduled,
and a hypothesis's steps count each of its non-input, non-output variables.
`test/pruning_verify` runs a fixture in that mode. The full test suite passes in verification mode. The maintained three-premise fixture scores four
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
cuts. The ordinary diagnostic
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
`Checking`, `(1,0,0,3,0)`, and one use. This fixture stresses recursive score resolution, not discrimination between
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
QuickChick now has an experimental `QuickChick.SchedulingPolicy` Rocq module.
It defines a typed score across steps, complete schedules, coverage leaves,
and inductive summaries. A policy also supplies an ordering and a partial-node
bound; strict pruning keeps ties. The scheduler view includes applied symbolic
terms, scoped local ids, dependency states, finite-pin metadata, leaf patterns,
and search decisions.
`test/scoring_policy.v` computes examples with a user-defined record score and
a bound that reads search state. This is an interface test, not a selected
derivation. The plugin's first quotation stage converts scheduler terms and
patterns to the corresponding symbolic view. It preserves shadowed binders and
applied arguments, and exposes implicit type holes as `TImplicitHole`; a test uses a real scheduler
candidate. An internal diagnostic now elaborates that view as a Rocq term and
evaluates a Rocq-defined function with VM reduction. The derivation probe covers
an indexed polymorphic relation and a user-defined record score. Quotation
resolves global names to qualified paths and represents `Type`, `Prop`, and
`Set` as sorts. The probe is enabled only by `QC_POLICY_QUOTE_PROBE=1`, with
`QC_POLICY_SCORE_PROBE` naming the Rocq function; it does not select a policy.
The remaining bridge must retain scores across dependency calls, compare them
through the policy, and feed policy bounds into search. Existing ranking and
settings remain active.

The diagnostic also quotes real `Check`, unconstrained, and relation-producer
steps and evaluates a Rocq callback named by `QC_POLICY_STEP_PROBE`. The
focused fixture covers a polymorphic checker, a generated output, a relation
output, a finite-pinned output, and a relation with a separate input. Rocq
sees the output count, bound-source input count, and finite-pin count as
`(0,2,0)`, `(1,0,0)`, `(1,0,0)`, `(1,0,1)`, and `(1,1,0)` respectively in
those cases. Recursive helper references use a distinct generated-name node.
This step probe inspects the first candidate of each constructor. A separate
`QC_POLICY_SCHEDULE_PROBE` callback receives the first fully scored candidate
as a Rocq `schedule_view`, including ordered steps, density annotations, and
the result when present. On a nested-output derivation, the callback confirms
that the producer's output ID is the subsequent match input, the matched
payload ID is the result, and the grades are one `Partial` and one
`Backtracking`. Synthetic output types that the scheduler stores as `DHole`
are represented as `TOpaque` with the same local ID. `LetStep` likewise has an
opaque local type; it has no real derivation fixture yet. The probe does not
rank candidates or certify a policy bound.

`QC_POLICY_COMPARE_PROBE` names a Rocq function of type `S -> S -> comparison`
when `QC_POLICY_SCHEDULE_PROBE` names a function from `schedule_view` to `S`.
The plugin keeps each result as a typed Rocq term and asks Rocq to compare
them. On a four-candidate relation, a record-valued policy preferring the
first `policy_compare_c` source chooses candidate 3; the observed comparison
results are two `Lt` and one `Eq`. This is diagnostic only. It does not replace
the default completed-schedule ranker, and no bound callback or recursive
score context is connected yet. `TImplicitHole` is distinct from `TOpaque`:
the former is a source-level implicit placeholder, while the latter marks
metadata the scheduler did not retain.

Run `python3 test/check_policy_bridge.py` with the local validation `coqc` on
`PATH` after building `@install`. It recompiles the focused Rocq fixture with
diagnostics enabled and checks record evaluation, source inputs and pins,
match/result binder links, and four-candidate comparison. The scorer compares
the final segment of a qualified name so the test works under both Dune and
direct `coqc` module paths. It also checks that default ranking still selects
candidate 0 while the diagnostic Rocq comparator prefers candidate 3. The
first-candidate and all-candidate diagnostics share one finite-pin lookup cache
per constructor. The ordinary Dune theory build does not enable
these diagnostic callbacks.
The comparator fixture also uses a polymorphic record parameterized by
`list nat`; scores from separate callback evaluations remain type-compatible
when the plugin applies their Rocq comparator. A wrong result type is rejected.

A further internal `QC_POLICY_RECORD_PROBE` accepts a named Rocq `scorer`
record. It invokes both `score_step` and `score_schedule` on every candidate
whose source obligations all resolve to existing instances. Its context quotes
the root application and output positions, original inputs, typed result and
producer locals, and each supplied dependency's full application. The
`list nat` fixture distinguishes that dependency from an unparameterized `list` and
checks the step score contributes to the schedule score. Candidates with a
pending derived or recursive dependency, an unknown local type, or an
unrepresented match-bound local are skipped. This is a diagnostic subset;
general `Completed` dependency scores and policy selection still need the
separate typed memo described in the scoring design.
The regression also derives `policy_quote_missing A`, whose generator needs
`GenSized A` from its eventual caller. It receives no supplied-instance score
notice, while concrete `nat` and `list nat` sources do. The diagnostic uses
direct resolution of the elaborated class obligation in the current context,
without adding hypothetical typeclass premises. Parameter sources are checked
by the same rule. Recursive helper sources are explicitly excluded: their
rewritten syntax no longer contains a complete applied dependency key.
When every candidate is eligible, the probe applies the record's `compare_scores`
to their typed Rocq scores. It preserves candidate order on ties. The
four-candidate fixture supplies all needed generator and checker modes, then
selects candidate 3 with two strict improvements and one tie. If any candidate
is ineligible, no best-candidate notice is emitted. This comparison remains
diagnostic; it is not used for policy search or pruning.

`QC_POLICY_RECORD_PENDING_PROBE` uses the same Rocq `scorer` interface but
includes unresolved nonrecursive requests as `Pending` in the context. A
Rocq-defined scorer observes one pending `GenSized A` dependency in
`policy_quote_missing A` and one supplied dependency in `policy_quote_list`.
It still skips recursive helper sources until their full request can be
carried through rewriting. The older supplied-only Rocq helper remains
available; both helpers produce the same score when every dependency is
supplied. Neither probe selects a production schedule.

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
