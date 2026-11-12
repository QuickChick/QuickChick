# BudgetAware completed-score parity

`plugin/budgetAwareScore.ml` implements Specimen's completed `BudgetAwareScore`
at revision `121cf23435a17d93f1dde283daa62d2899628a8b`. It scores concrete
QuickChick schedule steps and combines constructor scores across coverage
leaves. Its caller supplies the original input variables, completed dependency
scores, and finite-pinned positions. The latter can be computed from a
translated Rocq relation with `finite_pins_of_relation`. The
`finite_pins_from_environment` callback looks up the relevant member of a
mutual inductive and caches its result for one derivation. An unavailable or
untranslatable relation gives no pinned positions, matching Specimen's
conservative fallback. The analysis intentionally stops at ground constructor
conclusions; it does not infer finite ranges from premises.

`SpecimenParity.lean` runs the reference scorer on matching schedules. The
OCaml test checks the values in `expected.txt`; `check_parity.py` reruns both
implementations against the local pinned Specimen checkout. The cases cover
all six score fields, finite and loose production, repeated pins, dependency
fabrication, recursive locality, and coverage aggregation.

Separate OCaml tests score candidates returned by the real scheduler,
including a match prelude. `UnifyQC.type_to_schedules` reports prepared
fixed inputs through `on_prepared`; callers pass these inputs to the scorer
after unification. `score_candidate` prepends the match and equality steps
that compilation uses. Dependency requests retain full applied arguments,
so callers can distinguish applications of one relation to different types.

`doc/BudgetAwareDemo.v` is a live diagnostic over two real constructor
schedules. With `QC_BUDGET_AWARE_DEMO=budget_root`, the plugin prints each
completed six-field score and the schedule that received it. For this
monomorphic, acyclic fixture it resolves the selected dependency modes from
the completed scheduler memo; an unavailable dependency is reported instead
of silently receiving a score. The finite producer has selectivity zero, and
the loose producer followed by a finite check has selectivity one. This
diagnostic does not change public ranking or provide a search bound.

`QC Scorer budget_aware.` uses the library to select constructor
schedules; see `doc/SchedulingPolicies.md`. `S_Let` and `SrcDef` have no
counterparts in the pinned Specimen schedule syntax and return an error
instead of an invented score. Dependency scores come only from completed,
cycle-independent memo entries; other calls score as Partial.
`test/budget_aware_ranking` checks a fixture where BudgetAware and the
default density ranking choose different schedules.
Admissible bounds are a separate subsequent step.
