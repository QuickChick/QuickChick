Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.
Require Import LazyList RoseTrees.
Require Import RandomQC.
Require Import List.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.


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


Definition Series (A : Type) : Type := nat -> RandomSeed -> LazyList A.

Class Serial (A : Type) :=
  {
    (* Enumerate up to "n" elements *)
    series : Series A
  }.

(* Union of two series *)
Definition series_sum {A : Type} (s1 s2 : Series A) : Series A
  := (fun n r =>
        let (r1, r2) := randomSplit r in
        lazy_append (s1 n r1) (s2 n r2)).

(* Product of two series *)
Definition series_prod {A B : Type} (s1 : Series A) (s2 : Series B) : Series (A * B)
  := (fun n r =>
        let (r1, r2) := randomSplit r in
        x <- s1 n r1;;
        y <- s2 n r2;;
        ret (x, y)).

(* Helper functions for generating G's for constructors of "n" arguments *)
Definition cons0 {A} (con : A) : Series A := (fun n r => ret con).
Definition cons1 {A B} (m : Series A) (con : A -> B) : Series B
  := (fun n r =>
        match n with
           | 0 => lnil _
           | S n' => a <- m n' r;;
                     ret (con a)
        end).

Definition cons2 {A B C} (ma : Series A) (mb : Series B) (con : A -> B -> C) : Series C
  := (fun n r =>
        match n with
        | 0 => lnil _
        | S n' =>
          p <- (series_prod ma mb) n' r ;;
          match p with
          | (a, b) => ret (con a b)
          end
        end).

Definition cons3 {A B C D} (ma : Series A) (mb : Series B) (mc : Series C) (con : A -> B -> C -> D) : Series D
  := (fun n r =>
        match n with
        | 0 => lnil _
        | S n' =>
          p <- (series_prod ma (series_prod mb mc)) n' r ;;
          match p with
          | (a, (b, c)) => ret (con a b c)
          end
        end).


(* Series instance for bool *)
Instance Serial_bool : Serial bool :=
  {
    series := series_sum (cons0 false) (cons0 true);
  }.


(* Series instance for nat *)
Fixpoint series_nat (n : nat) (r : RandomSeed) : LazyList nat :=
  series_sum (cons0 0) (cons1 series_nat S) n r.

Instance Serial_nat : Serial nat :=
  {
    series := series_nat
  }.


(* Series instance for lists *)
Fixpoint series_list {A : Type} `{Serial A} (n : nat) (r : RandomSeed) : LazyList (list A)
  := series_sum (cons0 nil) (cons2 series series_list cons) n r.
