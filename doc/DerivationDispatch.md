# Derivation commands

`QCDerive` uses the scheduled engine for generators, enumerators, and checkers.
Derived instances are registered for typeclass search. Type parameters and class
dictionaries are implicit; ordinary value inputs remain explicit.

| Command | Implementation |
| --- | --- |
| `QCDerive GenSized` / `EnumSized` | Scheduled, including mutual datatype blocks |
| `QCDerive Arbitrary` | Scheduled generation and existing shrinking |
| `QCDerive DecOpt` / `Checker` | Scheduled checking |
| `QCDerive GenSizedSuchThat` / `ArbitrarySizedSuchThat` / `Generator` | Scheduled constrained generation |
| `QCDerive EnumSizedSuchThat` / `Enumerator` | Scheduled constrained enumeration |
| `QCDerive Show`, `Shrink`, `Sized` | Existing implementations |
| `QCDeriveLegacy` / `DeriveLegacy` | Deprecated access to the old engines |

The experimental `Testing` entry point and the `Fuzzy`/`Mutate` implementations
are unchanged. Fuzzing repairs are outside this release-preparation work.

## Examples

```coq
From QuickChick Require Import QuickChick.
Inductive box (A : Type) := Box : A -> box A.
QCDerive (GenSized, EnumSized) for box.

Inductive related {A B : Type} : A -> B -> Prop :=
| Related : forall x y, related x y.
QCDerive Checker for (@related A B x y).
QCDerive Generator for (fun (y : B) => @related A B x y).
QCDerive Enumerator for (fun y => related x y).
```

The generator instance for `box A` takes an implicit `Gen A` dictionary, as the
old command did. Enumeration takes `Enum A`. Public command wrappers adapt the
scheduled engine's sized prerequisites locally; they add no global reverse
`Gen -> GenSized` or `Enum -> EnumSized` instances. Existing sized dictionaries
still supply unsized ones through QuickChick's usual instances. This adaptation
also applies to sized prerequisites inherited through checker dependencies.

Requirements follow actual dependency calls, including applied type arguments.
A checker using an instance that requires `C (list A * B)` carries that same
requirement. An unused parameter does not acquire arbitrary generation or
equality requirements. This can change explicit `@` applications of old helpers;
prefer class methods or implicit instance applications.

Default public names remain `GenSizedbox`, `EnumSizedbox`, and `DecOptrelated`.
Simple derivations also retain `arbitrarySized_impl_box` and
`enumSized_impl_box`, with size last. Repeated explicit derivations get fresh
names. Automatic testing instead reuses suitable existing instances. Explicit
`Derive Inductive Schedule` commands retain their size-first helpers, sized
premises, and collision errors.

## Syntax and compatibility

Implicit type arguments are elaborated before selecting output positions.
A generated output must occur once as a whole predicate argument. Pair outputs
can use `fun p => let '(x,y) := p in P x y` or `fun '(x,y) => P x y`.
Term inputs must be distinct variables, and output order must match predicate
argument order. Fixed or repeated term inputs and reordered outputs are rejected
rather than silently generalized; use `QCDeriveLegacy` for those forms. Larger
or nested output tuples have not been certified.

`QCDeriveLegacy` and `DeriveLegacy` accept the old command forms, including
`using`, and issue the `quickchick-legacy-derive` warning. There is no automatic
fallback to the old engine. Correctness tactics that recognize the old generated
terms still need legacy derivation; `tutorials/DerivingProofs.v` demonstrates this
workflow. Proof automation for scheduled terms remains future work.

Bare `Derive` requires `From QuickChick Require Import LegacyDerive.` It aliases
the new public dispatcher, not the legacy engine. Prefer `QCDerive`: bare
`Derive` can conflict with Stdlib syntax.

A mutual datatype with a member lacking a base constructor currently fails
unconstrained derivation; the legacy generator fails on the same example.
Constructor applications such as the recorded Specimen hash example also remain
a scheduler limitation. Neither case is a reason to silently choose a different
engine.

## Validation

`test/derivation_contracts.v` checks the preserved public contracts.
`test/public_derivation.v` covers implicit and explicit type arguments, pair
outputs, custom checker dictionaries, missing requirements, mutual datatypes,
universe polymorphism, fresh names, both legacy spellings, and public generator/checker/enumerator
requirement propagation with dictionary-dependent results.
`test/enum_constraint_chain.v` covers the generator/checker/enumerator chain in
the scheduled engine. Validation currently covers Coq 8.20 with an explicitly
selected local plugin; the full supported-version matrix remains outstanding.
