From QuickChick Require Import QuickChick.

(* Constructor-local names are scoped to their own rule, including when the
   same spelling has a different type in another rule. *)
Inductive scoped_checks : nat -> Prop :=
| CheckNats : forall (key x y : nat), x = y -> scoped_checks key
| CheckBools : forall (key : nat) (x y : bool), x = y -> scoped_checks key.

QCDerive DecOpt for (scoped_checks subject).

Definition scoped_dictionary (subject : nat) : DecOpt (scoped_checks subject) :=
  DecOptscoped_checks subject.

Example scoped_check_runs : decOpt (P := scoped_checks 0) 3 = Some true.
Proof. reflexivity. Qed.
