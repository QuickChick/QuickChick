From QuickChick Require Import QuickChick.

(* QuickChick Derive has the short form QC Derive, and both have a Legacy
   form that selects the deprecated engine. *)

Inductive short_tree := ShortLeaf | ShortNode : short_tree -> short_tree.
QC Derive (Arbitrary, Show) for short_tree.
Definition short_gen : GenSized short_tree := ltac:(typeclasses eauto).

Inductive long_tree := LongLeaf | LongNode : long_tree -> long_tree.
QuickChick Derive (Arbitrary, Show) for long_tree.
Definition long_gen : GenSized long_tree := ltac:(typeclasses eauto).

Inductive even : nat -> Prop :=
| EvenZero : even 0
| EvenStep n : even n -> even (S (S n)).

QC Derive Checker for (even n).
Example short_checker : @decOpt (even 4) _ 10 = Some true.
Proof. reflexivity. Qed.

(* The test command still accepts a term after QuickChick. *)
QuickChick (fun n : nat => Nat.eqb n n).
