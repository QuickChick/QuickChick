QuickChick [![CircleCI](https://circleci.com/gh/QuickChick/QuickChick.svg?style=svg)](https://circleci.com/gh/QuickChick/QuickChick)
==========

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

[QuickChick: Property-Based Testing in Coq][sfqc] (Software Foundations, Volume 4)

[sfqc]: https://softwarefoundations.cis.upenn.edu/qc-current/index.html

## Installation

### From OPAM

    # Add the Coq opam repository (if you haven't already)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    # Install the coq-quickchick opam package
    opam install coq-quickchick

### From source

Dependencies are listed in [`coq-quickchick.opam`](./coq-quickchick.opam).

    # To get the dependencies, add the Coq opam repository if you haven't already
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install --deps-only

#### Build using Make

    make

    # To install the package:
    # (proceed with caution: this will clobber your `.opam` directory)
    make install

### Build using Dune

    make compat
    dune build

## Simple Examples

  - `examples/Tutorial.v`
  - `examples/RedBlack`
  - `examples/stlc`
  - `examples/ifc-basic` 

Running `make tests` in the top-level QuickChick folder will check and execute all of these.
If successful, you should see "success" at the end.

## Documentation

The public API of QuickChick is summarized in `BasicInterface.v`.

### Top-level Commands

- `QuickCheck c`
- `Sample g`
- `Derive Arbitrary for c`
- `Derive Show for c`
- `Derive ArbitrarySizedSuchThat for (fun x => p)`
- `Derive ArbitrarySizedSuchThat for (fun x => let (x1,x2...) := x in p)`
- `QuickCheckWith args c`
- `MutateCheck c p`
- `MutateCheckWith args c p`
- `MutateCheckMany c ps`
- `MutateCheckManyWith args c ps`

### More resources

Here is some more reading material:
  - Our POPL 2018 paper on [Generating Good Generators for Inductive Relations][mechanism for automatically deriving generators for inductive relations]
  - Our ITP 2015 paper on [Foundational Property-Based Testing](http://prosecco.gforge.inria.fr/personal/hritcu/publications/foundational-pbt.pdf)
  - Leo's invited talk at CLA on [Random Testing in the Coq Proof Assistant](https://lemonidas.github.io/pdf/InvitedCLA.pdf)
  - Catalin's [internship topic proposals for 2015](http://prosecco.gforge.inria.fr/personal/hritcu/students/topics/2015/quick-chick.pdf)
  - Catalin's [presentation at CoqPL 2015 workshop (2015-01-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Verified-Testing-CoqPL.pdf)
  - Zoe's [thesis defense at NTU Athens (2014-09-08)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/zoe-defense.pdf)
  - Maxime's [presentation at the Coq Workshop (2014-07-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Coq.pdf)
  - Catalin's [presentation at the Coq Working Group @ PPS (2014-03-19)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-PPS.pdf)
