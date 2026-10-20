# Recursive density order probe

Run `dune build --build-dir _build-validated @install`, then
`python3 test/scoring_cycles/check.py` with the local Rocq `coqc` on `PATH`.
The script passes `-I` for the locally built plugin and compiles each fixture
in a fresh process. It checks debug output from the actual scheduler.

`asym_a` has a base constructor and refers to `asym_b`; `asym_b` has no base
constructor and refers back to `asym_a`. In generator mode, both derivation
orders visit a provisional cycle score. Starting from `asym_a` records the
`GenSizedSuchThat_asym_b_O` mode as `Partial`. Starting from `asym_b` records
it as `Total`. Those separate processes have identical relation definitions
apart from their file-qualified names, and no differing instances.

The `Pair` and `Triple` fixtures expose the effect in parent scoring. The pair
visits `asym_a` before `asym_b` and has density `Partial`. The triple reaches
`asym_b` through `asym_c` first and has density `Total`. `Connected` contains
both dependency orders within one parent derivation and logs both grades for
`asym_b` under the same fully qualified key and proof context while
candidate-local memo state is restored between alternatives.
Its selected execution schedule has the `asym_a`, `asym_b`, and `asym_c` calls
in that order; completed density scoring visits `asym_c` first because it
sorts steps before resolving dependencies.

For generation, using the `Partial` grade of a committed `asym_b` call as a
lower bound would be unsound if a later step makes that call `Total`: its
minimization cost falls from 1 to 0. The current public search does not use
this bound. A cycle-dependent grade must remain unresolved in a prefix bound
unless the scoring order and cycle semantics are made stable.
