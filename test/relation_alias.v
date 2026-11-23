From QuickChick Require Import QuickChick.

(* A definition whose body is an inductive relation, such as
   [Definition Step := R], is read as that relation, also through a chain
   of such definitions. *)
Inductive R : nat -> Prop := R0 : R 0 | RS n : R n -> R (S (S n)).
Definition Step := R.
Definition Step2 := Step.

Inductive Q : nat -> Prop := QS n : Step2 n -> Q (S n).
QuickChick Derive Checker for (Q n).

Example checks : (decOpt (P := Q 3) 5, decOpt (P := Q 2) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

Theorem step_even : forall n, Step n -> Nat.even n = true.
Proof. quickchick 3. Abort.

(* A chain ending in another constant is read as that constant: an alias of
   [not] is a negation. *)
Definition neg := not.
Inductive N : nat -> Prop := NS n : neg (R n) -> N n.
QuickChick Derive Checker for (N n).

Example neg_checks : (decOpt (P := N 1) 5, decOpt (P := N 2) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

(* An alias of a function is read as the function. *)
Definition isEven := Nat.even.
Inductive E : nat -> Prop := ES n : isEven n = true -> E n.
QuickChick Derive Checker for (E n).

Example fun_checks : (decOpt (P := E 2) 5, decOpt (P := E 3) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.
