# Schedule selection and scoring

A derived generator, enumerator or checker runs one *schedule* per
constructor: an order in which to produce, match and check the constructor's
variables and premises. QuickChick enumerates the possible schedules of each
constructor, scores them with the selected *scorer*, and generates code from
the best one. This document describes the scorers, how to write one in Rocq,
and how the search stays exact and bounded.

## Search

For each constructor, the scheduler repeatedly picks the next premise to
schedule and commits its steps. A positive premise produces all of its
eligible unbound outputs; a premise whose arguments are all bound becomes a
check. Orders that differ only by swapping two independent premises are
explored once (`QC_SCHEDULE_POR=0` disables this reduction).

Selection is exact: the chosen schedule is the best under the scorer among
all candidates, and among equal scores the first one found wins. Candidate
identifiers follow search order, so ties are deterministic. Two mechanisms
keep the search bounded.

- **Score pruning.** A partial schedule is cut when its bound shows that no
  completion can beat the best complete schedule found so far. Because the
  earlier candidate wins ties, cutting on "no better than the incumbent" does
  not change the selection. Pruning is on by default. Scorers without a bound
  (cardinality, and Rocq scorers that do not prove theirs) search
  exhaustively up to 1,000 candidates per constructor; the cap applies only
  to them.
- **Independent groups.** Premises that share no unbound variables form
  separate groups, searched on their own. Combining group scores can reverse a
  local preference (a maximum absorbs a lead that a sum keeps), so each group
  keeps every schedule that is not dominated, and the combinations of these
  are ranked as ordinary candidates. With pruning on, a constructor with one
  group is pruned and one with several is searched group by group.

Each dependency derivation (a mode of another relation called by a schedule)
is a search of its own, with its own incumbent, and its result is memoized.

## Choosing a scorer

`QuickChick Scorer <name>.` (or `QC Scorer <name>.`) selects the scorer for
the derivations that follow in the file. The choice follows undo and
backtracking and is not exported to importing files; a prepared `quickchick`
test keeps the schedules it was prepared with. An unknown name is an error
listing the scorers.

| Scorer | Ranks by |
| --- | --- |
| `density_then_vars` (default; also `density`) | density, then fewer uses of bound variables |
| `density_counts_then_vars` | density, then fewer steps at each worse density, then variable uses |
| `density_only` | density |
| `vars_then_density` | variable uses, then density |
| `vars_only` | variable uses |
| `budget_aware` | Specimen's six-field BudgetAware score |
| `cardinality` (experimental) | filters by acceptance class |
| any constant of type `SchedulingPolicy.policy` | that policy (see below) |

**Density.** Each step has a grade: in ascending order Checking,
Backtracking, Neutral, Partial and Total. A producer's density is its lowest
step grade and higher is better; a checker's or enumerator's is its highest
step grade and lower is better. A call to another relation takes the grade
of that relation's mode, derived on demand. *Variable uses* counts how often
already bound variables are read, which favours schedules that produce
values rather than test them.

**BudgetAware.** `budget_aware` ports Specimen's completed score: selectivity,
density, fabrication, locality, input-check dependencies and variable
dependencies, compared lexicographically. A relation's score combines, over
its input-pattern coverage leaves, the best score among each leaf's
constructors. An uncovered leaf, a recursive call, or a dependency that is
not yet derived scores Partial. A schedule the score cannot represent (one
with a `let` step) is an error rather than a fallback.

**Cardinality** (experimental) reads a schedule as a query plan. Counts are
growth classes in the size bound (`1 < fin < poly < exp`). Each filter (a
check, a refutable match on a produced value, or a producer given generated
inputs) has an acceptance class: what it admits over what reaches it. The
score counts filters with acceptance `1/exp`, then `1/poly`, then unknown,
then constant; fewer is better. It has no pruning bound, and its scores can
depend on which other modes the search has already derived.

## Writing a scorer in Rocq

A scorer is a value of `QuickChick.SchedulingPolicy.policy`
(`src/SchedulingPolicy.v`). It chooses its own score type, scores the steps
of a candidate, combines them into a schedule score (seeing the whole
schedule if it wants), and compares scores; lower is better.
`doc/ScoringDemo.v` is a complete example.

`QC Scorer my_policy.` extracts the policy to OCaml, compiles it with
`ocamlfind ocamlopt`, and loads it into the plugin, so scoring runs as native
code. The compiled object is cached in the system temporary directory, under
`QuickChick-scorers`, keyed by the extracted code and the plugin.

**Views.** The policy sees each candidate's steps with their sources, grades
and patterns, the constructor's locals and inputs, and the state of each
dependency a step calls: `Completed` with its score under the same policy (a
relation's score is computed by the policy's `score_leaf` and
`score_inductive` over its coverage leaves), `InProgress`, `SuppliedInstance`
when an instance in context provides it, or `Pending`. Local identifiers are
stable throughout a derivation.

**Grouping.** `policy_grouping` declares how the score combines over
independent groups: a unit, a combine function, and the comparison as a
lexicographic list of fields, each `Additive` (a sum) or `Extremal` (a
maximum or minimum). The plugin trusts these laws; declaring a maximum
`Additive` is unsound. With `policy_grouping := None` each constructor is
searched jointly.

**Pruning.** A policy is pruned with its `lower_bound` when
`policy_bound_sound` proves the bound admissible: no complete schedule below
a search node scores better than the bound at that node (`bound_admissible`).
A search node lists its committed steps (each with its grade and whether that
grade is final), the remaining premises, how many of them must become
positive checks, and the variable uses every completion still incurs. The
schedule below may be scored in a context that knows more, since a pending
dependency may have completed meanwhile, so a step scorer must score an
unknown dependency no worse than any completed one. A proof that uses axioms,
such as an admitted lemma, still enables pruning, with a warning. Without a
proof the policy is searched unpruned, under the candidate cap.

`src/SchedulingPolicyLaws.v` builds policies with these proofs:

- `fold_policy M f floor kind` combines step scores in an ordered monoid `M`
  (`nat_max` and `nat_sum` are provided). Its bound combines the committed
  steps' scores and, once per forced check, an optional `floor` that every
  positive check reaches.
- `spec_step_scorer` builds a step scorer that reads only the specification;
  `dependency_step_scorer` one that also reads the completed score of the
  dependency a step calls.
- `lex_policy p q` compares two policies lexicographically, and `uses_policy`
  counts variable uses with a bound that includes the node's future uses.

`test/compiled_density.v` writes the default density ranking as such a
policy. On a large typing relation it selects exactly what the built-in does,
with the same pruning, in about twice the time: the cost is quoting each
search node into the policy's view types.

## Pruning bounds

The built-in bounds are computed from a node's committed steps. Density uses
the committed grades plus Checking for each forced check. BudgetAware scores
the committed steps with unresolved dependencies at their best. Both add a
look-ahead for variable uses: a variable a committed step binds counts once
in each remaining positive premise that mentions it, and an unbound variable
that is a bare argument of k remaining premises counts k - 1 times, since
only one of them can produce it. A dependency's grade enters a bound only
when its derivation read no provisional grade; otherwise the bound uses the
best possible grade, which keeps it admissible.

`test/bound_proofs/` proves these bounds admissible and the cuts exact, for a
model of the OCaml code: `DensityPrefixBound.v` for every density ranking,
`BudgetAwarePrefixBound.v` for BudgetAware, and `DensityLookahead.v` for the
look-ahead. Their premises are that committed steps and forced checks keep
their grades in every completion, a variable is produced at most once, and
outputs are unbound when a premise is scheduled.
`QC_SCHEDULE_SCORE_PRUNING=verify` checks every bound against every completed
descendant at run time; `test/pruning_verify` and `test/pruning_verify_budget`
run in that mode.

## Dependencies and the memo

A relation mode derived during a derivation is memoized with its schedule,
grade and score. An entry whose derivation read no provisional grade from
outside itself is shared by every candidate of the top-level derivation.
Other entries depend on what was in progress when they were derived; such an
entry is recorded with the entries it read and replayed wherever those reads
see the same values. A candidate's score therefore does not depend on which
candidates were scored before it.

Selecting the best theorem schedule (`quickchick` with index 0) scores
candidates lazily: once the grades seen so far show a candidate cannot beat
the incumbent, its remaining dependencies are not derived. Other indices, the
listing tactics and `try_all_quickchick_schedules` score every candidate. In
`quickchick n i`, `n` is the test size and `i` a schedule index; indices range
over the grouped combinations, and an out-of-range index is an error.

## Constructor weights

Derived generators choose among constructors by weight. By default a base
constructor has weight 1 and a recursive one the current size.
`QuickChickWeights [(C, 3); (D, size)]` overrides this per constructor, with a
number or `size`, which means the current size plus one. Enumerators and
checkers do not use weights. A weight is looked up by the constructor's name
and is not substituted through functor application.

## Diagnostics

These environment variables are for diagnosis and comparison; none is needed
in normal use.

| Variable | Effect |
| --- | --- |
| `QC_SCHEDULE_TRACE=1` | Report each selection: policy, candidate count, identifier and score. |
| `QC_SCHEDULE_TRACE_BOUNDS=1` | With the trace, report every bound and leaf score. |
| `QC_SCHEDULE_TIE_REPORT=1`, `QC_SCHEDULE_TIE_LIMIT=n` | Report ties among the best candidates (default limit 3; 0 for none). |
| `QC_SCHEDULE_SELECTION_LOG=file` | Append one line per selected constructor schedule. |
| `QC_SCHEDULE_SCORE_PRUNING` | `verify` checks bounds instead of cutting; `0`, `false`, `no` or `off` disables pruning. |
| `QC_SCHEDULE_GROUPS` | `0` searches jointly; `verify` also runs the joint search and fails if the best score differs. |
| `QC_SCHEDULE_GROUPS_LOG=file` | With `verify`, append one line per verified constructor. |
| `QC_SCHEDULE_MAX_CANDIDATES=n` | Change the unpruned candidate cap (0 removes it). |
| `QC_SCHEDULE_POR=0` | Disable swap reduction. |
| `QC_SCHEDULE_REUSE_STABLE=0`, `QC_SCHEDULE_CONTEXT_REUSE=0` | Disable memo sharing or contextual replay. |
| `QC_THEOREM_LAZY_SCORING=0` | Score every theorem candidate. |
| `QC_BUDGET_AWARE_DEMO=relation` | Print BudgetAware scores of every candidate for that relation (used by `test/budget_aware`). |
| `QC_CARDINALITY_TRACE=1` | Print the cardinality count of each mode. |

Dune does not track environment variables, so compare modes in separate
build directories.
