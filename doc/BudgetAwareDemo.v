From QuickChick Require Import QuickChick.

(* BudgetAware, Specimen's six-field score, as a built-in scorer. *)
Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive finite : nat -> Prop := FiniteZero : finite 0.

Inductive budget_root : nat -> Prop :=
| BudgetRoot : forall x, loose x -> finite x -> budget_root x.

(* The finite producer can supply x before the loose producer checks it, or
   loose can supply x before finite checks it. The latter costs selectivity
   1, so BudgetAware produces x from finite and checks loose. *)
QC Scorer budget_aware.
QuickChick Derive Generator for (fun x => budget_root x).

Goal True.
  lazymatch (eval unfold GenSizedSuchThatbudget_root in GenSizedSuchThatbudget_root) with
  | context [@decOpt (loose _)] => exact I
  | _ => fail "BudgetAware did not check loose x"
  end.
Qed.

QC Scorer density.
