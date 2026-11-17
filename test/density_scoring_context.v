From QuickChick Require Import QuickChick.
(* A derived checker whose dependency needs a class instance: schedule
   listing works with and without that instance in the proof context. *)

Class ScoreContext (A : Type) := { score_context_value : bool }.

Inductive scored_child (A : Type) : A -> Prop :=
| ScoredChild : forall x, scored_child A x.

#[local] Instance scored_child_checker (A : Type) `{ScoreContext A} (x : A)
  : DecOpt (scored_child A x) :=
  {| decOpt := fun _ => Some score_context_value |}.

Inductive scored_parent (A : Type) : A -> Prop :=
| ScoredParent : forall x, scored_child A x -> scored_parent A x.

QuickChick Derive Checker for (@scored_parent A x).

Goal ScoreContext bool -> scored_parent bool true -> scored_parent bool true.
Proof.
  intros local_dictionary h.
  quickchick_schedules.
  exact h.
Qed.

Goal scored_parent bool true -> scored_parent bool true.
Proof.
  intro h.
  quickchick_schedules.
  exact h.
Qed.

