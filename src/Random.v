Require Import ssreflect ssrbool ssrnat eqtype.
Require Import ZArith.
Require Import Axioms.

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
    randomR : A * A -> RandomGen -> A * RandomGen;
    randomRSound :
      forall s (a1 a2: A), leq a1 (fst (randomR (a1, a2) s)) /\
                           leq (fst (randomR (a1, a2) s)) a2   
  }.


Program Instance Randombool : Random bool :=
  {
    randomR := randomRBool;
    randomRSound := randomRBoolSound
  }.

Instance Randomnat : Random nat :=
  {
    randomR := randomRNat;
    randomRSound := ramdomRNatSound
  }.


Instance RandomZ : Random Z :=
  {
    randomR := randomRInt;
    randomRSound := ramdomRIntSound
  }.