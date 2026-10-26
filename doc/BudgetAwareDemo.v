From QuickChick Require Import QuickChick.

(* Start Coq with QC_BUDGET_AWARE_DEMO=budget_root to print the six-field
   completed scores. This diagnostic does not change which schedule is used. *)
Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive finite : nat -> Prop := FiniteZero : finite 0.

Inductive budget_root : nat -> Prop :=
| BudgetRoot : forall x, loose x -> finite x -> budget_root x.

(* The finite producer can supply x before the loose producer checks it, or
   loose can supply x before finite checks it. The latter costs selectivity 1. *)
QuickChick Derive Generator for (fun x => budget_root x).
