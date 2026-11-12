From QuickChick Require Import QuickChick.

(* Exercise scheduled declarations with inferred typeclass arguments. *)
Set Universe Polymorphism.
Inductive elaboration_accepts (A : Type) : A -> Prop :=
| ElaborationAccepts : forall x, elaboration_accepts A x.
Derive Inductive Schedule elaboration_accepts derive "Check" opt "true".

Example accepts_bool :
  DecOpt_elaboration_accepts_II 3 bool true = Some true.
Proof. reflexivity. Qed.
Example accepts_nat :
  DecOpt_elaboration_accepts_II 3 nat 2 = Some true.
Proof. reflexivity. Qed.

(* Exercise theorem declaration and extraction through the tactic. *)
Extract Constant defNumTests => "3".
Goal forall n : nat, n = n.
  quickchick 2.
  Check theorem.
Abort.
Fail Check theorem.
