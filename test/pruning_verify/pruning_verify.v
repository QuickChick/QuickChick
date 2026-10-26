From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* Connected hypotheses with a negated check, shaped like Cedar's TEqEntity,
   whose orderings are many and whose prefixes the bound must not overrate. *)

Inductive mem : nat -> list nat -> Prop :=
| MemHere x l : mem x (x :: l)
| MemLater x y l : mem x l -> mem x (y :: l).

Inductive defined : list nat -> list nat -> Prop :=
| Defined l : defined l l.

Inductive distinct_members : list nat -> nat -> nat -> Prop :=
| Distinct ets ns n1 n2 :
    defined ets ns -> mem n1 ns -> mem n2 ns -> n1 <> n2 ->
    distinct_members ets n1 n2.

QuickChick Derive Generator for (fun p => let '(n1, n2) := p in distinct_members ets n1 n2).
QuickChick Derive Enumerator for (fun n2 => distinct_members ets n1 n2).
QuickChick Derive Checker for (distinct_members ets n1 n2).
