Require Import ZArith.
Require Import ssreflect ssrbool ssrnat.

Axiom RandomSeed : Type.
Axiom randomSeedInhabitant : RandomSeed.

Axiom randomNext     : RandomSeed -> Z * RandomSeed.
Axiom randomGenRange : RandomSeed -> Z * Z.
Axiom mkRandomSeed   : Z          -> RandomSeed.
Axiom newRandomSeed  : RandomSeed.

Axiom randomSplit    : RandomSeed   -> RandomSeed * RandomSeed.
Axiom randomSplitAssumption :
  forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).

(* Primitive generator combinators and some basic soundness
   assumptions about them *)
Axiom randomRBool : bool * bool -> RandomSeed -> bool * RandomSeed.
Axiom randomRBoolCorrect :
  forall b b1 b2,
    implb b1 b = true /\ implb b b2 = true <->
    exists seed, (fst (randomRBool (b1, b2) seed)) = b.
Axiom randomRNat  : nat  * nat  -> RandomSeed -> nat * RandomSeed.
Axiom ramdomRNatCorrect:
  forall n n1 n2,
    n1 <= n /\ n <= n2 <->
    exists seed, (fst (randomRNat (n1, n2) seed)) = n.
Axiom randomRInt  : Z * Z    -> RandomSeed -> Z * RandomSeed.
Axiom ramdomRIntCorrect:
  forall z z1 z2,
    Z.leb z1 z /\ Z.leb z z2 <->
    exists seed, (fst (randomRInt (z1, z2) seed)) = z.
