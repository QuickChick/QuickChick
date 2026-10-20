# BudgetAware completed-score parity

`plugin/budgetAwareScore.ml` implements Specimen's completed `BudgetAwareScore`
at revision `121cf23435a17d93f1dde283daa62d2899628a8b`. It scores concrete
QuickChick schedule steps and combines constructor scores across coverage
leaves. Its caller supplies the original input variables, completed dependency
scores, and finite-pinned positions. The latter can be computed from a
translated Rocq relation with `finite_pins_of_relation`.

`SpecimenParity.lean` runs the reference scorer on matching schedules. The
OCaml test checks the values in `expected.txt`; `check_parity.py` reruns both
implementations against the local pinned Specimen checkout. The cases cover
all six score fields, finite and loose production, repeated pins, dependency
fabrication, recursive locality, and coverage aggregation.

Separate OCaml tests score candidates returned by the real scheduler,
including a match prelude. `NewUnifyQC.type_to_schedules` reports prepared
fixed inputs through `on_prepared`; callers pass these inputs to the scorer
after unification. `score_candidate` prepends the match and equality steps
that compilation uses. Dependency requests retain full applied arguments,
so callers can distinguish applications of one relation to different types.

This library is not connected to QuickChick's ranking or recursive dependency
derivation yet. `S_Let` and `SrcDef` have no counterparts in the pinned
Specimen schedule syntax and return an error instead of an invented score.
The callback must supply completed scores in the correct applied context;
cycle-dependent or provisional grades are not safe substitutes. The public
ranking and syntax remain unchanged. Production use still needs instance-aware
recursive score derivation and relation metadata from Rocq for finite pinning.
Admissible bounds are a separate subsequent step.
