Require Import ssreflect ssrbool ssrnat eqtype.
Require Import ZArith.

(* We axiomatize a random number generator
   (currently written in OCaml only) *)
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


Class OrdType (A: Type) :=
  {
    leq     : A -> A -> bool;
    refl    : forall a, leq a a;
    trans   : forall  a b c, leq b a -> leq a c -> leq b c;
    antisym : forall a b, leq a b -> leq b a -> a = b
  }.

Program Instance OrdBool : OrdType bool :=
  {
    leq b1 b2 := implb b1 b2
  }.
Next Obligation.
  by destruct a.
Qed.
Next Obligation.
  by destruct a; destruct b; destruct c.
Qed.
Next Obligation.
  by destruct a; destruct b.
Qed.

Program Instance OrdNat : OrdType nat :=
  {
    leq := ssrnat.leq;
    trans := leq_trans
  }.
Next Obligation.
  apply/eqP. by rewrite eqn_leq; apply/andP; split.
Qed.

Program Instance OrdZ : OrdType Z :=
  {
    leq := Z.leb;
    refl := Z.leb_refl;
    antisym := Zle_bool_antisym;
    trans := fun a b => Zle_bool_trans b a
  }.


Class Random (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a /\ leq a a2 <->
                            exists seed, fst (randomR (a1, a2) seed) = a
  }.

Program Instance RandomBool : Random bool :=
  {
    randomR := randomRBool;
    randomRCorrect := randomRBoolCorrect
  }.

Instance RandomNat : Random nat :=
  {
    randomR := randomRNat;
    randomRCorrect := ramdomRNatCorrect
  }.


Instance RandomZ : Random Z :=
  {
    randomR := randomRInt;
    randomRCorrect := ramdomRIntCorrect
  }.
