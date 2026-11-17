From QuickChick Require Import QuickChick.

(* A universe-polymorphic relation with a type parameter derives a checker
   that works at each type. *)
Set Universe Polymorphism.
Inductive elaboration_accepts (A : Type) : A -> Prop :=
| ElaborationAccepts : forall x, elaboration_accepts A x.
QuickChick Derive Checker for (@elaboration_accepts A x).

Example accepts_bool :
  decOpt (P := elaboration_accepts bool true) 3 = Some true.
Proof. reflexivity. Qed.
Example accepts_nat :
  decOpt (P := elaboration_accepts nat 2) 3 = Some true.
Proof. reflexivity. Qed.

(* Exercise theorem declaration and extraction through the tactic. *)
Extract Constant defNumTests => "3".
Goal forall n : nat, n = n.
  quickchick 2.
  Check theorem.
Abort.
Fail Check theorem.
