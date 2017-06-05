Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Checker.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

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

Class Eq (A : Type) :=
  { 
    dec_eq : forall (x y : A), decidable (x = y)
  }.

Global Instance Eq__Dec {A} `{H : Eq A} (x y : A) : Dec (x = y) :=
  {|
    dec := _
  |}.
Proof.
  unfold decidable.
  apply H.
Defined.

(* Lifting common decidable instances *)
Global Instance Dec_eq_nat (m n : nat) : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
Defined.

Global Instance Dec_eq_opt (A : Type) (m n : option A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H.
Defined.

Global Instance Dec_eq_prod (A B : Type) (m n : A * B)
  `{_ : forall (x y : A), Dec (x = y)} 
  `{_ : forall (x y : B), Dec (x = y)} 
  : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H0. apply H.
Defined.

Global Instance Dec_eq_list (A : Type) (m n : list A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H.
Defined.

Global Instance Dec_ascii (m n : Ascii.ascii) : Dec (m = n).
Proof.
  constructor.
  unfold ssrbool.decidable.
  repeat (decide equality).
Defined.

Global Instance Dec_string (m n : string) : Dec (m = n).
Proof.
  constructor.
  unfold ssrbool.decidable.
  repeat (decide equality).
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

