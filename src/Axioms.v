Require Import ZArith.
Require Import ssreflect ssrbool ssrnat.
        
Axiom RandomGen   : Type.
Axiom rndNext     : RandomGen   -> Z * RandomGen.
Axiom rndGenRange : RandomGen   -> Z * Z.
Axiom rndSplit    : RandomGen   -> RandomGen * RandomGen.
Axiom mkRandomGen : Z           -> RandomGen.

(* Primitive generator combinators and some basic soundness 
   assumptions about them *)
Axiom randomRBool : bool * bool -> RandomGen -> bool * RandomGen.
Axiom randomRBoolSound :
  forall s b1 b2,
    implb b1 (fst (randomRBool (b1, b2) s)) = true /\
    implb (fst (randomRBool (b1, b2) s)) b2 = true.
Axiom randomRNat  : nat  * nat  -> RandomGen -> nat * RandomGen.
Axiom ramdomRNatSound:
  forall s n1 n2,
    n1 <= (fst (randomRNat (n1, n2) s)) = true /\
    (fst (randomRNat (n1, n2) s)) <= n2.
Axiom randomRInt  : Z * Z    -> RandomGen -> Z * RandomGen.
Axiom ramdomRIntSound:
  forall s n1 n2,
    Z.leb n1 (fst (randomRInt (n1, n2) s)) = true /\
    Z.leb (fst (randomRInt (n1, n2) s)) n2 = true.

Axiom newStdGen   : RandomGen.
