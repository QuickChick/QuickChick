From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Require Import List Arith Lia. Import ListNotations.

(* The built-in density_then_vars ranking written as a Rocq policy, from the
   proved builders: a maximum of flipped grade ranks, where a forced check
   counts as Checking, then the engine's variable uses, whose bound looks
   ahead at the uses every completion incurs. Its pruning bound is proved.
   Compiled by QC Scorer, it must choose the built-in's schedules. *)

Definition grade_rank (d : density) : nat :=
  match d with Checking => 0 | Backtracking => 1 | Neutral => 2 | Partial => 3 | Total => 4 end.

Definition prefers_dense (spec : spec_view) : bool :=
  match spec_mode spec with Generate | TestTheorem => true | _ => false end.

(* Lower is better, so a producer's rank is flipped. A positive check is
   graded Checking; a negative check keeps its grade. *)
Definition flipped (spec : spec_view) (d : density) : nat :=
  if prefers_dense spec then 4 - grade_rank d else grade_rank d.

Definition grade_score : step_scorer nat nat_max :=
  spec_step_scorer nat_max (fun spec _ step d =>
    match step with CheckStep _ true => flipped spec Checking | _ => flipped spec d end)
    (fun _ _ _ _ => ltac:(nat_order)).

(* A forced check grades the schedule Checking. *)
Definition forced_checks_count : check_floor nat nat_max grade_score.
Proof.
  refine {| floor_score := fun ctx => flipped (current_spec ctx) Checking |}.
  intros ctx ctx' prev source grade (Hspec & _). cbn. rewrite Hspec. nat_order.
Defined.

Definition density_policy : policy :=
  lex_policy (fold_policy nat_max grade_score (Some forced_checks_count) Extremal)
             uses_policy.

(* The policy's bound is proved, without axioms. *)
Goal match policy_bound_sound density_policy with Some _ => True | None => False end.
Proof. exact I. Qed.

(* The built-in and the compiled policy choose the same schedule. Each
   relation is derived under both; the generated instances must be equal. *)
Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive pinned : nat -> nat -> Prop :=
| PinZero : forall y, pinned 0 y
| PinOne : forall y, pinned 1 y.
Inductive root : nat -> nat -> Prop :=
| Root : forall x y, loose x -> pinned x y -> root x y.

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive between : nat -> nat -> nat -> Prop :=
| Between : forall a b c, le' a b -> le' b c -> between a b c.

QuickChick Derive Generator for (fun x y => root x y).
QuickChick Derive Generator for (fun b c => between a b c).
QuickChick Derive Checker for (between a b c).
QC Scorer density_policy.
QuickChick Derive Generator for (fun x y => root x y).
QuickChick Derive Generator for (fun b c => between a b c).
QuickChick Derive Checker for (between a b c).

Ltac same_instance i j :=
  let a := eval unfold i in i in
  let b := eval unfold j in j in
  first [constr_eq a b | fail "the compiled density policy chose another schedule"].

Goal True.
  same_instance GenSizedSuchThatroot GenSizedSuchThatroot0.
  same_instance GenSizedSuchThatbetween GenSizedSuchThatbetween0.
  same_instance DecOptbetween DecOptbetween0.
  exact I.
Qed.
