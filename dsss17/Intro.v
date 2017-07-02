(** * Intro: Introduction *)

(* HIDEFROMHTML *)
(* NOW: Can we trim the import list (perhaps adding some thing to
   QuickChick.v)? *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import List ZArith. Import ListNotations.
(*
Import QcDefaultNotation. Open Scope qc_scope.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Import ListNotations.
*)
(* /HIDEFROMHTML *)

(** * First Taste *)

(** Consider the following definition of a function [remove], which
    takes a natural number [x] and a list of nats [l] and removes [x]
    from the list. *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

(** One possible specification for [remove] might be this property *)

Conjecture removeP : forall x l,  ~ (In x (remove x l)).

(** which says that [x] never occurs in the result of [remove x l] for
    any [x] and [l].  Sadly, this property is false, as we would
    eventually discover if we were to try to prove it. *)

(** A different way to discover the discrepancy between the definition
    and specification is this: *)

QuickChick removeP.

(** The [QuickChick] command takes a property (which must be "executable" 
    -- we'll see later exactly what this means) and attempts to falsify 
    it by running it on many randomly generated inputs, resulting in 
    output like this: 
<<
    0
    [0, 0]
    Failed! After 17 tests and 12 shrinks
>>
    This means that, if run [remove] with [x] being [0] and [l]
    the two-element list containing two zeros, then the property
    [removeP] fails. With this example in hand, we can see that the [then]
    branch of [remove] fails to make a recursive call, which means
    that only one occurence of [x] will be deleted. The last
    line of the output records that it took 17 tests to identify some
    fault-inducing input and 12 "shrinks" to reduce it to a minimal
    counterexample. *)

(* HIDE: Needs two or three little exercises here.  What can we write,
   using just the Dec instances that are there by default?
    - the insert function yields a list containing the inserted
      element and all of the original elements
    - reversing twice yields the original list (how can we get it
      wrong?)
    - 
*)

(* EX1 (insert) *)
(** Here is a somewhat mangled definition of a function for inserting a
   new element into a sorted list of numbers: *)

Fixpoint insert x l :=
  match l with
  | [] => [x]
  | y::t => if y <? x then insert x t else y::t
  end.

(** Write a property that says "inserting a number [x] into a list [l]
    always yields a list containing [x]."  Make sure QuickChick finds
    a counterexample. *)

(* SOLUTION *)
Conjecture insertP : forall x l,  In x (insert x l).
QuickCheck insertP.
(* /SOLUTION *)
(** [] *)

(* EX3 (insert2) *)
(** Write a property that says "inserting a number [x] into a list [l]
    yields a list containing every member of [l]."  Make sure
    QuickChick finds a counterexample. (N.b. There is a way to do this
    using just what we've seen, though it's arguably not the best
    way.) *)

(* SOLUTION *)
Conjecture insertP2 : forall x l y,  In y l -> In y (insert x l).
QuickCheck insertP2.
(* /SOLUTION *)
(** [] *)
(* NOW: Try a different version with a "forallProp" combinator. Not
   clear whether it belongs here or later. *)

(** * Overview *)

(** Property-based random testing involves four basic ingredients:

    - an _executable property_ like [removeP],
    - _generators_ for random elements of the types of the inputs to
      the property (here, numbers and lists of numbers),
    - _printers_ for converting data structures like numbers and lists
      to strings when reporting counterexamples, and
    - _shrinkers_, which are used to minimize counterexamples.

    We will delve into each of these in detail later on, but first we
    need to make a digression to explain Coq's support for
    _typeclasses_, which QuickChick uses extensively both internally
    and in its programmatic interface to users.  This is
    \CHAP{Typeclasses}. *)

(* NOW: Overview the rest of the chapters. *)
       