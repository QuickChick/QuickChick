QuickChick
==========

[![CircleCI](https://circleci.com/gh/QuickChick/QuickChick.svg?style=svg)](https://circleci.com/gh/QuickChick/QuickChick)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237977-Coq-users)

## Description
 
- Randomized property-based testing plugin for Coq; a clone of [Haskell QuickCheck]
- Includes a [foundational verification framework for testing code]
- Includes a [mechanism for automatically deriving generators for inductive relations]

[Haskell QuickCheck]:
https://hackage.haskell.org/package/QuickCheck

[foundational verification framework for testing code]:
http://prosecco.gforge.inria.fr/personal/hritcu/publications/foundational-pbt.pdf

[mechanism for automatically deriving generators for inductive relations]:
https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf

## Tutorial

- Small tutorials on Basic Usage and Automation can be found under `tutorials/`
- [Testing a theorem inside a proof](tutorials/ProofScopedTests.v) shows how to
  prepare and rerun a test without leaving global helpers behind.
- An extended introduction can be found in [QuickChick: Property-Based Testing in Coq][sfqc] (Software Foundations, Volume 4)

[sfqc]: https://softwarefoundations.cis.upenn.edu/qc-current/index.html

## Installation

### From OPAM

    # Add the Coq opam repository (if you haven't already)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    # Install the coq-quickchick opam package
    opam install coq-quickchick

## Simple Examples

Test the current goal before proving it:

```coq
From QuickChick Require Import QuickChick.
Goal forall n : nat, n = n.
  quickchick 2.
  QuickChick (theorem 4).
  intros; reflexivity.
Qed.
```

`quickchick` prepares a proof-local test called `theorem` and runs it at size 2.
`QuickChick (theorem 4)` reruns that test at size 4 without deriving it again.
The goal remains open after testing. The helpers disappear when the proof ends.
The compiled [proof-scoped tutorial](tutorials/ProofScopedTests.v) also shows
how to name a saved test and change execution settings.

Other examples:

  - `examples/Tutorial.v`
  - `examples/RedBlack`
  - `examples/stlc`
  - `examples/ifc-basic` 

Running `make tests` in the top-level QuickChick folder will check and execute all of these.
If successful, you should see "success" at the end.

## Documentation

The public API is summarized in [QuickChickInterface.v](doc/QuickChickInterface.v).
See the [derivation commands](doc/DerivationDispatch.md) and
[3.0 migration guide](doc/3.0Migration.md) for the scheduled engine and legacy
commands.

### Top-level Commands

- `QuickCheck c`
- `Sample g`
- `QCDerive Arbitrary for c`
- `QCDerive Show for c`
- `QCDerive ArbitrarySizedSuchThat for (fun x => p)`
- `QCDerive DecOpt for p`
- `QCDerive EnumSizedSuchThat for (fun x => p)`
- `QCDerive ArbitrarySizedSuchThat for (fun x => let (x1,x2...) := x in p)`
- `QuickCheckWith args c`
- `MutateCheck c p`
- `MutateCheckWith args c p`
- `MutateCheckMany c ps`
- `MutateCheckManyWith args c ps`

### Older `Derive` commands

Use `QCDerive` with the usual `From QuickChick Require Import QuickChick.`
import. It avoids a parser conflict with Stdlib's `Derive` command.

To keep bare `Derive` commands in an older file, replace that import with:

```coq
From QuickChick Require Import LegacyDerive.
```

This compatibility import enables the old spelling, including class lists and
`using` clauses. It uses the same derivation engine as `QCDerive`. It can still
conflict with other plugins' `Derive` commands, so prefer `QCDerive` when combining
plugins. `Derive Inductive Schedule` and `Derive Valid Schedules` remain available
with the normal import.

### More resources

Here is some more reading material:
  - Our PLDI 2022 paper on [a mechanism for automatically deriving generators, enumerators, and checkers for inductive relations](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf)
  - Our POPL 2018 paper on [a mechanism for automatically deriving generators for inductive relations](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)
  - Our ITP 2015 paper on [Foundational Property-Based Testing](http://prosecco.gforge.inria.fr/personal/hritcu/publications/foundational-pbt.pdf)
  - Our PLDI 2023 paper on [a mechanism for merging multiple inductive relations into one](https://lemonidas.github.io/pdf/MergingInductiveRelations.pdf)
  - Leo's invited talk at CLA on [Random Testing in the Coq Proof Assistant](https://lemonidas.github.io/pdf/InvitedCLA.pdf)
  - Catalin's [internship topic proposals for 2015](http://prosecco.gforge.inria.fr/personal/hritcu/students/topics/2015/quick-chick.pdf)
  - Catalin's [presentation at CoqPL 2015 workshop (2015-01-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Verified-Testing-CoqPL.pdf)
  - Zoe's [thesis defense at NTU Athens (2014-09-08)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/zoe-defense.pdf)
  - Maxime's [presentation at the Coq Workshop (2014-07-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Coq.pdf)
  - Catalin's [presentation at the Coq Working Group @ PPS (2014-03-19)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-PPS.pdf)

---

## Developer's corner

### Build dependencies

Dependencies are listed in [`coq-quickchick.opam`](./coq-quickchick.opam).

    # To get the dependencies, add the Coq opam repository if you haven't already
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install . --deps-only

### Build

    dune build

### Install from a checkout

For a local checkout, install the dependencies and package into the active opam
switch with:

    opam install . --deps-only
    dune build @install
    dune install coq-quickchick

For a normal user installation, `opam install .` performs the dependency
installation, build, and package installation together.

## Run tests

    dune runtest

### Run extra tests for quickChick tool

    dune install coq-quickchick  # Makes QuickChick available globally
    dune build @cram

