QuickChick
==========

### Description
 
  - Randomized Property-Based Testing Plugin for Coq

### Known to work with

  - Coq 8.4pl4
  - OCaml 4.01.0
    - [CH 2014-09-13: Please note that OCaml 4.02.0 does not yet seem to work with Coq 8.4pl4 or with SSReflect 1.5.]
  - SSReflect 1.5

### Compilation and Installation

    make && make install

### Simple Examples

  - examples/Tests.v
  - examples/RedBlack
  - examples/ifc-basic (not quite finished)

### Larger Case Study

  - See https://github.com/QuickChick/IFC

### Documentation
Yes, we need some! Until then here are some reasonable surrogates:
  - QuickChick: A Coq Framework For Verified Property-Based Testing
    (http://prosecco.gforge.inria.fr/personal/hritcu/publications/verified-testing-draft.pdf)
  - Zoe's thesis defense at NTU Athens (2014-09-08)
    (http://prosecco.gforge.inria.fr/personal/hritcu/talks/zoe-defense.pdf)
  - Maxime's presentation at the Coq Workshop (2014-07-18)
    (http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-Coq.pdf)
  - Catalin's presentation at the Coq Working Group @ PPS (2014-03-19)
    (http://prosecco.gforge.inria.fr/personal/hritcu/talks/QuickChick-PPS.pdf)
