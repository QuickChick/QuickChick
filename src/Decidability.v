Require Import Checker.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat.
Set Bullet Behavior "Strict Subproofs".

(* Class wrapper around "decidable" *)
Class Dec (P : Prop) : Type :=
  {
    dec : decidable P
  }.

(* Additional Checkable instance *)
Global Instance testDec {P} `{H : Dec P} : Checkable P :=
  {|
    checker p := _
  |}.
Proof.
  destruct H.
  destruct dec0.
  - exact (checker true).
  - exact (checker false).
Defined.

(* Lifting common decidable instances *)
Global Instance Dec_eq_nat (m n : nat) : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
Defined.

(* Everything that uses the Decidable Class *)
Require Import DecidableClass.

Instance dec_class_dec P (H : Decidable P): Dec P.
Proof.
  constructor; destruct H; destruct Decidable_witness.
  - left; auto.
    apply Decidable_spec; auto.
  - right => H; eauto.
    apply Decidable_spec in H.
    inversion H.
Defined.

(*
Example foo (m n : nat) := 
  match @dec (m = n) _ with 
    | left  _ => 0 
    | right _ => 1
  end.

(* Eval compute in foo 0 1. *)
Example bar (m n : nat) := 
  if (m=n)? then 0 else 1.

(* Eval compute in bar 0 1. *)
*)


(* Not sure about the level or binding, but good idea *)
Notation "P '?'" := (match (@dec P _) with 
                       | left _ => true
                       | right _ => false
                     end) (at level 100).

