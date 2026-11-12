From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* Checking a negated conclusion multiplies the test fuel by a constant
   built from nat's constructors, which live in Coq.Init.Datatypes. The
   property is false; the test only needs the generated checker to compile. *)

Inductive mem : nat -> list nat -> Prop :=
| MemHere x l : mem x (x :: l)
| MemLater x y l : mem x l -> mem x (y :: l).

Theorem members_differ : forall n1 n2 l, mem n1 l -> mem n2 l -> n1 <> n2.
Proof. quickchick 3. Abort.
