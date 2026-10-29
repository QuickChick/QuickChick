# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased] — 3.0 candidate

- `QCDerive` is replaced by `QuickChick Derive` and its short form
  `QC Derive`; `QC` is now a keyword. They use the scheduled engine for
  generators, enumerators, and checkers, and register their typeclass
  instances.
- The old derivation engine is removed, with `DeriveLegacy` and the `using`
  clauses of derivation commands. Correctness proofs for derived instances
  are no longer generated: the proof tactics recognized only the old
  engine's terms, and the `DerivingProofs` tutorial is removed.
- Bare `Derive` is available through `QuickChick.LegacyDerive`; the normal
  import leaves Stdlib's `Derive` syntax alone.
- The `quickchick` proof tactic keeps its generated test and helpers local to
  the proof. A saved test can be rerun before the proof ends.
- Testing works inside ordinary and nested modules and on properties exported
  by applied functors. An unapplied functor cannot run a test.
- Public derivations accept fixed or repeated inputs, such as
  `(le' 2 y)` or `(R x x)`, through the instance derived for distinct inputs,
  and outputs out of predicate order, such as `(fun '(y, x) => R x y)`,
  through a second instance typed as the request. An output that occurs
  more than once or inside a term is rejected as unsupported. Constructor
  conclusions may apply functions, as in `R n (double n)`. See the
  [migration guide](doc/3.0Migration.md).
- Schedule derivation shares completed dependency derivations between
  candidate schedules and caches instance checks up to variable renaming,
  which makes large relations derive several times faster.
- `QuickChick Scorer <name>.` (or `QC Scorer`) selects the schedule scorer,
  such as `density` (the default), `budget_aware` or `cardinality`, for later
  derivations in the file. It replaces the `QC_SCHEDULE_RANKING` environment
  variable, which is removed. `Scorer` is now a keyword.
- A scorer can be written in Rocq, as a `QuickChick.SchedulingPolicy.policy`.
  `QC Scorer my_policy.` compiles it to native code once and loads it into the
  plugin; see `doc/SchedulingPolicies.md`. Compiling needs `ocamlfind`. A
  policy is pruned when it proves its bound admissible, and searched by groups
  when it declares a grouping. It sees the scores of the dependencies already
  derived, computed by its own leaf and relation scorers. `QuickChick.SchedulingPolicyLaws` builds
  policies from step scores with both proofs supplied.
- Schedule selection is exact by default: score-based pruning, proved sound
  for the built-in rankings, replaces the 1,000-candidate cap. Set
  `QC_SCHEDULE_SCORE_PRUNING=0` to disable it. Cardinality ranking has no
  bounds and keeps the cap.
- `quickchick` on a goal over an abstract type, and derivation of a
  constructor whose premise is an implication or quantified statement,
  report what is unsupported instead of failing with an anomaly.
- `QuickChick` on a property with an unresolved instance, such as a missing
  `Show`, reports the instance instead of a kernel anomaly.
- A mutual type member with no base constructor gets an unconstrained
  generator when a partner member has one: at fuel zero it builds on the
  partner's base case. A type with no finite values, such as one whose only
  constructor takes itself, is rejected with an error naming the type.
- Derived `Show` and `Shrink` work for types with explicit parameters,
  including mixes of implicit and explicit ones and mutual types.
- `quickchick` shrinks a counterexample's unconstrained variables with their
  `Shrink` instances, and leaves a variable unshrunk when its type has none.
  A shrunk value that breaks a later hypothesis is discarded. The outputs of
  a producing hypothesis are shrunk only when an existing checker for that
  hypothesis (for example from `QuickChick Derive Checker`) confirms each shrunk
  value; otherwise they are not shrunk.
- Tested with Coq 8.20, Rocq 9.0 and Rocq 9.1. Rocq 9.2 and later need a release of
  `coq-simple-io` that supports them. During large derivations `coqc` has
  occasionally aborted with "stack smashing detected" on OCaml 5.2 and, more
  rarely, 5.4; rerunning succeeds. It did not occur in testing on OCaml 4.13.

This section describes the candidate branch; its final release scope has not
been settled.

## [2.2.0] - 2026-05-26

- Remove `Derive` in favor of `QCDerive` to avoid clash with Stdlib and Equations

## [2.1.0] - 2025-02-28

- Add compatibility with Rocq 9.
- Extend deriving for simple mutually inductive types.
- Fix a file system race that could happen when multiple `QuickChick` commands
  run in the same directory.

## [2.0.5] - 2024-12-05

- Fix `mycppo` script for Windows.

## [2.0.4] - 2024-09-18

- Add compatibility with Coq 8.20.
- Fix exponential blow up in derived generators and other deriving bugs.
- Rename `Derive` command to `QuickChickDerive` to disambiguate from Equation's `Derive` command.

## [2.0.3] - 2024-04-05

- Add compatiblity with Coq 8.19
- Improve robustness of `QuickChick` by generating truly unique temporary directories
- Resolve extraction warnings:
    + Avoid extraction-opaque-accessed by not depending on `Qed` reflection lemmas.
    + Make `StringOT.compare` and `AsciiOT.compare` `Defined` instead of `Qed`
    + Disable extraction-reserved-identifier

## [2.0.2] - 2024-01-04

## [2.0.1] - 2023-10-08

- Add compatibility with Coq 8.18

## [2.0.0] - 2022-04-13

Major 2.0 Release of QuickChick

- Introduce the notion of `Producer`, a typeclass that abstracts both generators and enumerators.
- No longer support a Monad instance for `G (option A)`. 
- bind notation for optional generators can be obtained by importing `BindOptNotation`,
  `x <-- c1 ;; c2` with a double arrow, resolving typeclass resolution issues.
- Include support for deriving checkers for inductive relations based on 
  [PLDI 2022](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf). 
  
  `Derive Checker for (P x1 x2 ... xn)` 
  
  Defines an instance of the `DecOpt` typeclass that can be access using `??` notation.
- Introduce an enumeration monad `E`, with the same API as generators. Automatic 
  type-based enumerators for an inductive `T` can be derived using `Derive` notation:
  
  `Derive EnumSized for T.`
  
- Introduce the `EnumSizedSuchThat` typeclass for constrained enumeration, similar to 
  `GenSizedSuchThat`. Include support for deriving enumerators for inductive relations based on 
  [PLDI 2022](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf). 
  
  `Derive EnumSizedSuchThat for (fun y => P x1 ... xn y xm ...).`
  
- Introduce convenient notation for deriving constrained generators:

  `Derive Generator for (fun y => P x1 x2 ... y ... xm ...)`
  
- Introduce a mechanism for [Merging Inductive Relations](https://lemonidas.github.io/pdf/MergingInductiveRelations.pdf).

  `Merge P with Q as R.`

- No longer support Coq 8.13 and 8.14

## [1.6.5] - 2022-04-13

- Support Coq 8.17
- No longer support Coq 8.11 and 8.12

## [1.6.4] - 2022-08-14

- Future proofing (internal changes, resolve warnings, keep up with the times)

## [1.6.3] - 2022-05-25

- Add `-use-ocamlfind` to invocations of `ocamlbuild`
- Add `--root=.` to invocations of `dune`, fixing tests using Dune
  without a `dune-project` file

## [1.6.2] - 2022-04-08
- Fix Windows compatibility: pass on environment when running test executable
  This fixes QuickChick in a Coq Platform "compiled from source" environment. (issue #269)

## [1.6.1] - 2022-03-03
- Add Windows compatibility
- Improve extraction of `randomRNat`, `randomRInt`, `randomRN` by using
  `Random.State.full_int` instead of `Random.State.int`.

## [1.6.0]
- Remove all dependency on perl (replaced with cppo (OCaml preprocessor) at compile time; awk at runtime).
- Added more informative error messages when tests fail to compile or throw exceptions.
- Fixed inefficient extraction of Nat arithmetic; this previously caused tests to run in time quadratic in the number of generated test cases.
- Added `RelDec` instance for `eq`.

## [1.5.1]
- Support Coq 8.11 to 8.14.

## [1.5.0]
- Support Coq 8.13.
- No longer support Coq 8.12.

## [1.4.0]
### Added
- Support Coq 8.12.

### Removed
- No longer support Coq 8.11.

## [1.3.2] - 2020-07-11
### Added
- `QCInclude` command to replace `Declare ML Module`.

### Fixed
- Sound extraction of `modn`.

### Changed
- `Decimal.int` no longer depend on an external file for extraction.

## [1.3.1] - 2020-04-06
### Changed
- Add `-cflags -w -3` to `ocamlbuild` for running extracted code.
  This silences the warning from using the deprecated `Pervasives` functions
  until it's fixed by Coq (Issue #11359).
- Rename `src/unify.ml` to `src/unifyQC.ml` to avoid clashing with the
  Coq module of the same name.

### Removed
- Remove our own reliance on `Pervasives`.
  This will enforce OCaml >= 4.07 going forward,
  but it's marked for deprecation anyways.

### Fixed
- Declare all scopes before using them.
- Fix most remaining warnings during compilation.
- Fix compatibility with ExtLib monad notations.

## [1.3.0] - 2020-03-19
### Added
- Support Coq 8.11.

### Removed
- No longer support Coq 8.10.

## [1.2.1] - 2020-04-09
Backport some fixes in [1.3.1] to Coq 8.10.
These changes are not included in [1.3.0].
### Fixed
- Fix most remaining warnings during compilation.
- Fix compatibility with ExtLib monad notations.

## [1.2.0] - 2020-01-30
### Added
- Support Coq 8.10.

### Removed
- No longer support Coq 8.9.

### Fixed
- `div`, `divn`, and `modn` no longer throw `Division_by_zero` exceptions.

## [1.1.0] - 2019-04-19
### Added
- Support Coq 8.9.

### Removed
- No longer support Coq 8.8.

### Fixed
- Examples use new generator combinators.
- Determine C source files with `*.c` rather than `*c`.
- Derive instances properly regardless of interpretation scope.

### Deprecated
- `-exclude` option in `quickChickTool` is deprecated. Use `-include` instead.

## [1.0.2] - 2018-08-22
### Added
- Functor and Applicative instances for generators.
- Decidable equivalence between `unit`s.
- `-N` option to modify max success in `quickChickTool`.
- Collect labels for discarded tests.
- `quickChickTool` takes Python and Solidity files.

### Changed
- Rename `BasicInterface` to `QuickChickInterface`.
- Rename `Eq` to `Dec_Eq`.
- Separate generator interface from implementation.

### Deprecated
- `elements`  is deprecated in favor of `elems_`.
- `oneof`     is deprecated in favor of `oneOf_`.
- `frequency` is deprecated in favor of `freq_`.

### Fixed
- Show lists with elements separated by `;` rather than `,`.

## [1.0.1] - 2018-06-13
### Added
- Support Coq 8.8
- `-include` option for `quickChickTool`.
- Highlighted success message for `quickChickTool`.
- Checker combinator `whenFail'`.
- Tagged mutants.
- Line number information of mutants.

### Fixed
- OPAM dependencies.

### Removed
- No longer support Coq 8.7

## [1.0.0] - 2018-04-06
### Added
- OPAM package `coq-quickchick` on [coq-released](https://coq.inria.fr/opam/www/).

[1.6.5]: https://github.com/QuickChick/QuickChick/compare/v1.6.4...v1.6.5
[1.6.4]: https://github.com/QuickChick/QuickChick/compare/v1.6.3...v1.6.4
[1.6.3]: https://github.com/QuickChick/QuickChick/compare/v1.6.2...v1.6.3
[1.6.2]: https://github.com/QuickChick/QuickChick/compare/v1.6.1...v1.6.2
[1.6.1]: https://github.com/QuickChick/QuickChick/compare/v1.6.0...v1.6.1
[1.6.0]: https://github.com/QuickChick/QuickChick/compare/v1.5.1...v1.6.0
[1.5.1]: https://github.com/QuickChick/QuickChick/compare/v1.5.0...v1.5.1
[1.5.0]: https://github.com/QuickChick/QuickChick/compare/v1.4.0...v1.5.0
[1.4.0]: https://github.com/QuickChick/QuickChick/compare/v1.3.2...v1.4.0
[1.3.2]: https://github.com/QuickChick/QuickChick/compare/v1.3.1...v1.3.2
[1.3.1]: https://github.com/QuickChick/QuickChick/compare/v1.3.0...v1.3.1
[1.3.0]: https://github.com/QuickChick/QuickChick/compare/v1.2.1...v1.3.0
[1.2.1]: https://github.com/QuickChick/QuickChick/compare/v1.2.0...v1.2.1
[1.2.0]: https://github.com/QuickChick/QuickChick/compare/v1.1.0...v1.2.0
[1.1.0]: https://github.com/QuickChick/QuickChick/compare/v1.0.2...v1.1.0
[1.0.2]: https://github.com/QuickChick/QuickChick/compare/v1.0.1...v1.0.2
[1.0.1]: https://github.com/QuickChick/QuickChick/compare/v1.0.0...v1.0.1
[1.0.0]: https://github.com/QuickChick/QuickChick/compare/itp-2015-final...v1.0.0
