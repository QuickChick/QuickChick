QuickChick
==========

[![CircleCI](https://circleci.com/gh/QuickChick/QuickChick/tree/8.7.svg?style=svg)](https://circleci.com/gh/QuickChick/QuickChick/tree/8.7)

### Description
 
  - Randomized property-based testing plugin for Coq; a clone of [Haskell QuickCheck]
  - Includes a [foundational verification framework for testing code]
  - Includes a [mechanism for automatically deriving generators for inductive relations]

[Haskell QuickCheck]:
https://hackage.haskell.org/package/QuickCheck

[foundational verification framework for testing code]:
http://prosecco.gforge.inria.fr/personal/hritcu/publications/foundational-pbt.pdf

[mechanism for automatically deriving generators for inductive relations]:
https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf

For more information on QuickChick, look at the tutorial available under the qc folder 
of the deep spec summer school:
https://github.com/DeepSpec/dsss17

### Current release dependencies:

  - Branch master: 
    * Coq 8.7
    * OCaml >= 4.04.0
    * mathcomp-ssreflect-1.6.4
    * coq-ext-lib-0.9.7

### Compilation and Installation

    # You need to add the Coq opam repository (if you haven't already)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install coq-quickchick

### Compilation and Installation (from source)

    # To get the dependencies, you still need to add the Coq opam repository (if you haven't already)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install coq-mathcomp-ssreflect coq-ext-lib

    # Then:
    make && make install

### Simple Examples

  - `examples/Tutorial.v`
  - `examples/RedBlack`
  - `examples/stlc`
  - `examples/ifc-basic` 

Running `make tests` in the top-level QuickChick folder will check and execute all of these.
If successful, you should see "success" at the end.

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


### Other tags

  - coq 8.4pl6:
    * OCaml 4.01.0 and Coq 8.4pl3 or OCaml 4.02.1 and Coq 8.4pl6
    * SSReflect 1.5 (http://ssr.msr-inria.inria.fr/FTP/)
  - coq 8.5-*:
    * Coq 8.5pl2 
    * OCaml 4.03.0
    * mathcomp-ssreflect v1.5 
    + 8.5-legacy contains the old typeclass hierarchy
    + 8.5-automation contains the new one
  - coq 8.6:
    * Coq 8.6
    * OCaml 4.03.0
    * mathcomp-ssreflect-1.6.1

### Documentation
The public API of QuickChick is summarized in BasicInterface.v.

The main documentation is the DeepSpec summer school tutorial:
- [DeepSpec QC repo](https://github.com/DeepSpec/dsss17/tree/master/qc).
Pretty soon this will become a software foundations volume!

Here is some more reading material:
  - Our POPL 2018 paper on [Generating Good Generators for Inductive Relations][mechanism for automatically deriving generators for inductive relations]
  - Our ITP 2015 paper on [Foundational Property-Based Testing](http://prosecco.gforge.inria.fr/personal/hritcu/publications/foundational-pbt.pdf)
  - Catalin's [internship topic proposals for 2015](http://prosecco.gforge.inria.fr/personal/hritcu/students/topics/2015/quick-chick.pdf)
  - Catalin's [presentation at CoqPL 2015 workshop (2015-01-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Verified-Testing-CoqPL.pdf)
  - Zoe's [thesis defense at NTU Athens (2014-09-08)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/zoe-defense.pdf)
  - Maxime's [presentation at the Coq Workshop (2014-07-18)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Coq.pdf)
  - Catalin's [presentation at the Coq Working Group @ PPS (2014-03-19)](http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-PPS.pdf)
