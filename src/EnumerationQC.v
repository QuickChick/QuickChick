Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.
Require Import LazyList RoseTrees.
Require Import RandomQC.
Require Import List.
Import ListNotations.


Class EnumFromInterval (A : Type)  :=
  {
    (* Enumerate a range *)
    enumFromTo : A -> A -> LazyList A
  }.


(* Because of the termination checker, defining enumFromTo in terms of
   succ is actually quite painful *)

(*
Fixpoint enumFromTo {A : Type} `{EnumFromInterval A} (a1 : A) (a2 : A) : LazyList A :=
  if leq a1 a2 then lcons _ a1 (lazy (enumFromTo (succ a1) a2)) else lnil _.
*)


(* EnumFromInterval for bool *)
Definition enumFromToBool (b1 : bool) (b2 : bool) : LazyList bool
  := if b1 =? b2 then ret b1 else if b1 =? false then lcons _ b1 (lazy (lcons _ b2 (lazy (lnil _)))) else lnil _.

Program Instance EnumBool : EnumFromInterval bool :=
  {
    enumFromTo := enumFromToBool;
  }.


(* EnumFromInterval for nat *)
Fixpoint enumFromN (n : nat) (num : nat) : LazyList nat
  := match num with
     | 0 => lnil _
     | S num' => lcons _ n (lazy (enumFromN (S n) num'))
     end.

Fixpoint enumFromToNat (n1 : nat) (n2 : nat) : LazyList nat
  := enumFromN n1 (S (n2 - n1)).

Instance EnumNat : EnumFromInterval nat :=
  {
    enumFromTo := enumFromToNat;
  }.



Class EnumN (A : Type) :=
  {
    (* Enumerate up to "n" elements *)
    enumN : nat -> LazyList A
  }.


(* EnumN instance for bool *)
Definition enumN_bool (n : nat) : LazyList bool := lazy_take n (list_to_LazyList [false; true]).

Instance EnumN_bool : EnumN bool :=
  {
    enumN := enumN_bool;
  }.


(* EnumN instance for nat *)
Fixpoint enumN_nat_helper (n : nat) (acc : nat) : LazyList nat :=
  match n with
  | 0 => lnil _
  | S n' => lcons _ acc (lazy (enumN_nat_helper n' (S acc)))
  end.

Definition enumN_nat (n : nat) : LazyList nat := enumN_nat_helper n 0.

Instance EnumN_nat : EnumN nat :=
  {
    enumN := enumN_nat;
  }.
