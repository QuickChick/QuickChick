Require Import ZArith.

Axiom RandomGen   : Type.
Axiom rndNext     : RandomGen   -> Z * RandomGen.
Axiom rndGenRange : RandomGen   -> Z * Z.
Axiom rndSplit    : RandomGen   -> RandomGen * RandomGen.
Axiom mkRandomGen : Z           -> RandomGen.
Axiom randomRBool : bool * bool -> RandomGen -> bool * RandomGen.
Axiom randomRNat  : nat  * nat  -> RandomGen -> nat  * RandomGen.
Axiom randomRInt  : Z    * Z    -> RandomGen -> Z    * RandomGen.
Axiom newStdGen   : RandomGen.
