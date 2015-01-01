Require Import ZArith.
Require Import ssreflect ssrbool ssrnat.
        
Axiom RandomGen   : Type.
Axiom randomSeedInhabitant : RandomGen.

Axiom rndNext     : RandomGen   -> Z * RandomGen.
Axiom rndGenRange : RandomGen   -> Z * Z.
Axiom rndSplit    : RandomGen   -> RandomGen * RandomGen.
Axiom mkRandomGen : Z           -> RandomGen.

Axiom rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).

(* Primitive generator combinators and some basic soundness 
   assumptions about them *)
Axiom randomRBool : bool * bool -> RandomGen -> bool * RandomGen.
Axiom randomRBoolCorrect :
  forall b b1 b2,
    implb b1 b = true /\ implb b b2 = true <->
    exists seed, (fst (randomRBool (b1, b2) seed)) = b.
Axiom randomRNat  : nat  * nat  -> RandomGen -> nat * RandomGen.
Axiom ramdomRNatCorrect:
  forall n n1 n2,
    n1 <= n /\ n <= n2 <->
    exists seed, (fst (randomRNat (n1, n2) seed)) = n.  
Axiom randomRInt  : Z * Z    -> RandomGen -> Z * RandomGen.
Axiom ramdomRIntCorrect:
  forall z z1 z2,
    Z.leb z1 z /\ Z.leb z z2 <->
    exists seed, (fst (randomRInt (z1, z2) seed)) = z.

Axiom newStdGen   : RandomGen.
