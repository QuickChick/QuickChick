Require Import AbstractGen.
Require Import List ssreflect ssrbool ssrnat seq.

Definition SO A := A -> Prop. 

Program Instance GenMonad : GenMonad SO :=
  {
    bindGen A B ma f := 
      fun b => exists a, ma a /\ f a b;
    returnGen A a := 
      eq a;
    choose A H p := 
      fun a => 
        (cmp (fst p) a = Lt \/
         cmp (fst p) a = Eq) /\
        (cmp (snd p) a = Gt \/
         cmp (snd p) a = Eq);
    sized A f := 
      fun a => exists n, f n a
  }.

(* Equivalence on sets of outcomes *) 
Definition SOeq {A} (m1 m2 : SO A) := 
  forall A, m1 A <-> m2 A.

(* the set of outcomes m1 is a subset of m2 *) 
Definition SOincl {A} (m1 m2 : SO A) :=
  forall A, m1 A -> m2 A. 


  
   
   
