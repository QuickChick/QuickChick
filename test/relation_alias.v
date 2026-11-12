From QuickChick Require Import QuickChick.

(* A definition whose body is an inductive relation, such as
   [Definition Step := R], is read as that relation. *)
Inductive R : nat -> Prop := R0 : R 0 | RS n : R n -> R (S (S n)).
Definition Step := R.

Inductive Q : nat -> Prop := QS n : Step n -> Q (S n).
QuickChick Derive Checker for (Q n).

Example checks : (decOpt (P := Q 3) 5, decOpt (P := Q 2) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

Theorem step_even : forall n, Step n -> Nat.even n = true.
Proof. quickchick 3. Abort.
