From QuickChick Require Import QuickChick.

(* A property whose instance arguments cannot be resolved reports the
   missing instance. [Fail] does not catch anomalies, so this fails if the
   unresolved instance reaches the kernel. *)

Inductive no_show := NoShow : nat -> no_show.

Definition gen_no_show : G no_show := ret (NoShow 0).
Definition holds (x : no_show) := true.

Fail QuickChick (forAll gen_no_show holds).
