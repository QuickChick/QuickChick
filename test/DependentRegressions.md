# Dependent derivation regressions

`dependent_regressions.v` ports the active relation cases from the former
`examples/other/DependentTest.v` to public scheduled derivations. Dune compiles
it as part of the normal testing theory and CI's `@runtest` build.

The old tests compared generated code to handwritten terms by reflexivity.
The port instead checks enumerated results, accepted and rejected inputs,
recursive witnesses, and independently specified properties of generated
values. Enumeration observations take at most twelve lazy results at fixed
fuel. They are regression checks, not general soundness or completeness proofs.
Positive witness assertions prevent the corresponding output checks from
passing merely because no successful values were produced.

Retained cases cover equality, unrestricted generation, constructor unification,
constructor fields, input matching, recursion with changed inputs, prerequisites,
producer/check narrowing, nonlinear shared variables, reverse mode, function
applications in premises, pair outputs, and compound recursive premises.
Generators and enumerators are derived for every original active relation;
checkers are additionally derived for the goodFoo family and goodFun.
Basic Show/shrink derivation remains exercised, with a child-shrinking assertion.
Constructor weights have a dedicated existing regression in constructor_weights.v.

The previously commented parameterized Bar example is now active. Added cases
also cover fixed/repeated inputs, reordered outputs, and rejection of repeated
or nested generated outputs. public_derivation.v covers both pair-lambda
spellings and their instance types; function_conclusion.v covers function
applications in conclusions. Other focused tests cover instance reuse, full
applied prerequisites, proof-local lifecycle, and custom scorer selection.

The historical False-premise case now supplies a genuine rejecting checker and
asserts that no values are emitted. It uses no admitted generator of False.
Random checks exercise constructor outputs and reordered pairs (20 trials each).
