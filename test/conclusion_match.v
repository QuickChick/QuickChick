From QuickChick Require Import QuickChick.
From Coq Require Import Arith.

(* A conclusion may compute an index with a match, such as an [if] over a
   sumbool, whose branches bind proofs anonymously. *)
Inductive Same : nat -> nat -> bool -> Prop :=
| S_ x y : Same x y (if Nat.eq_dec x y then true else false).

QuickChick Derive Checker for (Same x y b).
QuickChick Derive Generator for (fun b => Same x y b).

Example checks :
  (decOpt (P := Same 2 2 true) 5, decOpt (P := Same 2 3 true) 5,
   decOpt (P := Same 2 3 false) 5) = (Some true, Some false, Some true).
Proof. vm_compute. reflexivity. Qed.
