(* A checker that enumerates list color, where color has no enumerator
   instance, derives one for color. The list enumerator it also derives
   requires it, so it is compiled with the checker. *)
From QuickChick Require Import QuickChick.
Inductive color := Red | Green.
Inductive has_list : nat -> Prop :=
| HasList : forall n (l : list color), List.length l = n -> has_list n.
QuickChick Derive Checker for (has_list n).
Example has_list_two : decOpt (P := has_list 2) 5 = Some true.
Proof. reflexivity. Qed.
