From QuickChick Require Import QuickChick.
QC Scorer budget_aware.
Require Import List. Import ListNotations.

(* Connected hypotheses with a negated check, shaped like an entity-equality
   typing rule, whose orderings are many and whose prefixes the bound must not overrate. *)

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

(* A dense constructor: its BudgetAware scores tie on every field but the
   variable-dependency counts, which the look-ahead bounds. *)

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).

Inductive plus' : nat -> nat -> nat -> Prop :=
| plus_O n : plus' 0 n n
| plus_S n m p : plus' n m p -> plus' (S n) m (S p).

Inductive dense : list nat -> nat -> nat -> Prop :=
| Dense l a b x1 x2 x3 x4 x5 x6 : le' x1 a -> le' x1 x4 -> le' x1 x6 -> le' a x3 -> le' x1 x2 -> le' a b -> le' a x5 -> plus' a x1 x6 -> le' x4 x6 -> plus' x6 x5 b -> le' x1 x5 -> le' x2 x5 -> plus' x6 x3 a -> plus' x3 x2 x4 -> mem a l -> mem b l -> dense l a b.
QuickChick Derive Generator for (fun p => let '(a, b) := p in dense l a b).
