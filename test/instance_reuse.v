From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".

Inductive reused : bool -> Prop := Reused : reused true.
#[local] Instance fallback_checker (b : bool) : DecOpt (reused b) | 50 :=
  {| decOpt := fun _ => Some false |}.
#[local] Instance custom_checker (b : bool) : DecOpt (reused b) | 1 :=
  {| decOpt := fun _ => Some true |}.
Goal forall b, reused b.
  quickchick 2.
  Fail Check DecOpt_reused_I.
  lazymatch (eval unfold theorem in theorem) with
  | context [custom_checker _] => idtac
  | _ => fail "The selected test did not use the preferred checker"
  end.
Abort.
Fail Check theorem.

Inductive missing : bool -> Prop := Missing : missing true.
Goal forall b, missing b.
  quickchick 2.
  Check DecOpt_missing_I.
  let instance := constr:(_ : DecOpt (missing true)) in idtac.
  quickchick 2.
Abort.
Fail Check DecOpt_missing_I.
Fail Definition leaked_instance : DecOpt (missing true) := ltac:(typeclasses eauto).

(* An unrelated constant must never be accepted as a generated checker. *)
Inductive collision : bool -> Prop := Collision : collision true.
Definition DecOpt_collision_I := 0.
Fail Derive Inductive Schedule collision derive "Check" opt "true".

(* Standard instances are reused too. *)
Goal forall n : nat, n = n.
  quickchick 2.
  Fail Check GenSized_nat_.
Abort.

(* A bounded failed search is not evidence that the instance is absent. *)
Inductive bounded : bool -> Prop := Bounded : bounded true.
Set Typeclasses Depth 0.
Goal forall b, bounded b.
  Fail quickchick 2.
  Fail Check DecOpt_bounded_I.
Abort.
Unset Typeclasses Depth.


Inductive fresh_input := FirstInput | SecondInput.
QuickChick Derive Show for fresh_input.
Inductive accepts_input : fresh_input -> Prop := AcceptsInput : forall x, accepts_input x.
#[local] Instance input_checker (x : fresh_input) : DecOpt (accepts_input x) :=
  {| decOpt := fun _ => Some true |}.
Goal forall x, accepts_input x.
  quickchick 2.
  Check GenSized_fresh_input_.
  let instance := constr:(_ : GenSized fresh_input) in idtac.
  Fail Check DecOpt_accepts_input_I.
Abort.
Fail Check GenSized_fresh_input_.
Fail Definition leaked_generator : GenSized fresh_input := ltac:(typeclasses eauto).

Inductive proof_local : bool -> Prop := ProofLocal : proof_local true.
Goal forall b, proof_local b.
  pose (proof_checker := fun b => {| decOpt := fun _ => Some true |} : DecOpt (proof_local b)).
  quickchick 2.
  Fail Check DecOpt_proof_local_I.
Abort.
Fail Check theorem.

(* Completion, as well as Abort, removes temporary helpers and instances. *)
Inductive finishes : bool -> Prop := Finishes : forall b, finishes b.
Goal forall b, finishes b.
  quickchick 2.
  intros; constructor.
Qed.
Fail Check DecOpt_finishes_I.
Fail Definition leaked : DecOpt (finishes true) := ltac:(typeclasses eauto).
Inductive transparent : bool -> Prop := Transparent : forall b, transparent b.
Goal forall b, transparent b.
  quickchick 2.
  intros; constructor.
Defined.
Fail Check DecOpt_transparent_I.
Fail Definition leaked2 : DecOpt (transparent true) := ltac:(typeclasses eauto).
