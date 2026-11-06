From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".
Inductive accepts : bool -> Prop := Accepts : forall b, accepts b.
Goal forall b, accepts b.
  first [quickchick 2; fail 0 "rollback" | idtac].
  Fail Check theorem.
  Fail Check DecOpt_accepts_I.
  quickchick 2.
  QuickChick (theorem 3).
  quickchick 3.
  Check theorem0.
  QuickCheck (theorem 1).
  QuickChickWith (updMaxSuccess stdArgs 2) (theorem0 3).
  Undo.
  QuickChick (theorem 2).
  intros; constructor.
Qed.
Fail Check theorem.
Fail Check theorem0.
Fail Check DecOpt_accepts_I.

(* Definitions retained by a proof are local lets, not dangling constants. *)
Goal forall n : nat, n = n.
  quickchick 2.
  exact (let saved := theorem 2 in fun n => eq_refl n).
Defined.
Fail Check theorem.

(* Undo preparation itself, then prepare again under the same names. *)
Goal forall b, accepts b.
  quickchick 2.
  Undo.
  Fail Check theorem.
  Fail Check DecOpt_accepts_I.
  quickchick 2.
  QuickChick (theorem 2).
Abort.
Fail Check theorem.
Fail Definition leaked_checker : DecOpt (accepts true) := ltac:(typeclasses eauto).

(* A failed preparation after deriving dependencies leaves nothing behind. *)
Inductive unprintable := Unprintable.
Inductive accepts_unprintable : unprintable -> Prop :=
| AcceptsUnprintable : forall x, accepts_unprintable x.
Goal forall x, accepts_unprintable x.
  Fail quickchick 2.
  Fail Check theorem.
  Fail Check GenSized_unprintable_.
  Fail Check DecOpt_accepts_unprintable_I.
Abort.

(* Saved tests retain the selected checker when the local context changes. *)
Goal forall b, accepts b.
  pose (old_checker := fun b => {| decOpt := fun _ => Some false |} : DecOpt (accepts b)).
  quickchick 2.
  let body := eval unfold theorem in theorem in
  lazymatch body with
  | context [Some false] => idtac
  | _ => fail "Expected the original local checker"
  end.
  pose (new_checker := fun b => {| decOpt := fun _ => Some true |} : DecOpt (accepts b)).
  QuickChick (theorem 2).
  Fail Check theorem0.
Abort.
Fail Check theorem.

(* A retained test may contain freshly derived polymorphic helpers. *)
Inductive payload (A : Type) := Payload : A -> payload A.
Arguments Payload {A} _.
QuickChick Derive Show for payload.
Goal forall x : payload bool, True.
  quickchick 2.
  exact (let saved := theorem 2 in fun _ => I).
Defined.
Fail Check theorem.
Fail Check GenSized_payload_I.
