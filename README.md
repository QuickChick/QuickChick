QuickChick
==========

[![CircleCI](https://circleci.com/gh/QuickChick/QuickChick.svg?style=svg)](https://circleci.com/gh/QuickChick/QuickChick)

### Description
 
  - Randomized property-based testing plugin for Coq; a clone of [Haskell QuickCheck]
  - Includes a [foundational verification framework for testing code]
  - Includes a [mechanism for automatically deriving computation for inductive relations]

This is the branch that accompanies the PLDI 2022 paper: Computing Correctly with Inductive Relations.

## Installation instructions from source

- You need Coq 8.13.2 installed.
- Make sure you have the Coq opam repository (if you haven't already)

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update

- Install the coq-quickchick opam package dependencies

    opam install coq-quickchick --deps-only

- Compile the code

    make

- Install in your current switch (this will clobber any opam-installed QuickChick packages)
    
    make install
