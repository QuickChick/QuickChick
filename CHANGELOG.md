# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased 8.8]
### Added
- Support Coq 8.8.

### Removed
- No longer support Coq 8.7.

## [Unreleased 8.7]
### Added
- `-include` option for `quickChickTool`.
- Highlighted success message for `quickChickTool`.
- Checker combinator `whenFail'`.
- Tagged mutants.
- Line number information of mutants.

### Fixed
- OPAM dependencies.

## [1.0.0] - 2018-04-06
### Added
- OPAM package `coq-quickchick` on [coq-released](https://coq.inria.fr/opam/www/).

[Unreleased 8.8]: https://github.com/QuickChick/QuickChick/compare/8.7...8.8
[Unreleased 8.7]: https://github.com/QuickChick/QuickChick/compare/v1.0.0...8.7
[1.0.0]: https://github.com/QuickChick/QuickChick/compare/itp-2015-final...v1.0.0
