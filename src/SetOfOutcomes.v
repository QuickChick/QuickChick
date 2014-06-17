Require Import AbstractGen.
Require Import List ssreflect ssrbool ssrnat seq.


Definition Pred (A : Type) := A -> Prop.

(* Equivalence on sets of outcomes *) 
Definition peq {A} (m1 m2 : Pred A) := 
  forall A, m1 A <-> m2 A.

(* the set of outcomes m1 is a subset of m2 *) 
Definition pincl {A} (m1 m2 : Pred A) :=
  forall A, m1 A -> m2 A. 

Definition bindGen {A B} (m : Pred A) (f : A -> Pred B) : Pred B :=
  fun b => exists a, m a /\ f a b.

Definition returnGen {A} (a : A) : Pred A :=
  eq a.

Instance GenMonad : GenMonad Pred :=
  {
    bindGen := @bindGen;
    returnGen := @returnGen;
    choose A H p := 
      fun a => 
        (cmp (fst p) a = Lt \/
         cmp (fst p) a = Eq) /\
        (cmp (snd p) a = Gt \/
         cmp (snd p) a = Eq);
    sized A f := 
      fun a => exists n, f n a
  }.
