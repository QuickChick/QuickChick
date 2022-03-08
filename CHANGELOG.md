# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

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

[Unreleased]: https://github.com/QuickChick/QuickChick/compare/v1.3.2...master
[1.3.2]: https://github.com/QuickChick/QuickChick/compare/v1.3.1...v1.3.2
[1.3.1]: https://github.com/QuickChick/QuickChick/compare/v1.3.0...v1.3.1
[1.3.0]: https://github.com/QuickChick/QuickChick/compare/v1.2.1...v1.3.0
[1.2.1]: https://github.com/QuickChick/QuickChick/compare/v1.2.0...v1.2.1
[1.2.0]: https://github.com/QuickChick/QuickChick/compare/v1.1.0...v1.2.0
[1.1.0]: https://github.com/QuickChick/QuickChick/compare/v1.0.2...v1.1.0
[1.0.2]: https://github.com/QuickChick/QuickChick/compare/v1.0.1...v1.0.2
[1.0.1]: https://github.com/QuickChick/QuickChick/compare/v1.0.0...v1.0.1
[1.0.0]: https://github.com/QuickChick/QuickChick/compare/itp-2015-final...v1.0.0
