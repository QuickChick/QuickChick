From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Require Import List Arith Lia. Import ListNotations.

(* The built-in density_then_vars ranking written as a Rocq policy, from the
   proved builders: a maximum of flipped grade ranks, where a forced check
   counts as Checking, then a sum of variable uses. Its pruning bound is
   proved. Compiled by QC Scorer, it must choose the built-in's schedules. *)

Definition grade_rank (d : density) : nat :=
  match d with Checking => 0 | Backtracking => 1 | Neutral => 2 | Partial => 3 | Total => 4 end.

Definition prefers_dense (ctx : score_context nat) : bool :=
  match spec_mode (current_spec ctx) with Generate | TestTheorem => true | _ => false end.

(* Lower is better, so a producer's rank is flipped. A positive check is
   graded Checking; a negative check keeps its grade. *)
Definition flipped (ctx : score_context nat) (d : density) : nat :=
  if prefers_dense ctx then 4 - grade_rank d else grade_rank d.

Definition grade_score : step_scorer nat nat_max.
Proof.
  refine {| step_score := fun ctx _ step d =>
    match step with CheckStep _ true => flipped ctx Checking | _ => flipped ctx d end |}.
  intros. nat_order.
Defined.

(* A forced check grades the schedule Checking. *)
Definition forced_checks_count : check_floor nat nat_max grade_score.
Proof.
  refine {| floor_score := fun ctx => flipped ctx Checking |}.
  intros. unfold grade_score; cbn [step_score]. nat_order.
Defined.

Fixpoint argument_locals (t : term_view) : list nat :=
  match t with
  | TLocal i => [i]
  | TApply _ args => flat_map argument_locals args
  | _ => []
  end.

Definition distinct (ids : list nat) : list nat := nodup Nat.eq_dec ids.

(* As the engine counts them: a source's distinct variables, or a generated
   call's distinct variables per argument. *)
Definition source_locals (s : source_view) : list nat :=
  match source_category s, source_application s with
  | External, t => distinct (argument_locals t)
  | _, TApply _ args => flat_map (fun a => distinct (argument_locals a)) args
  | _, t => distinct (argument_locals t)
  end.

Fixpoint pattern_locals (p : pattern_view) : list nat :=
  match p with
  | PLocal i => [i]
  | PConstructor _ args => flat_map pattern_locals args
  | _ => []
  end.

Definition step_binds (step : step_view) : list nat :=
  match step with
  | Unconstrained l _ _ => [local_id l]
  | SuchThat ls _ _ => map local_id ls
  | MatchStep _ p => pattern_locals p
  | LetStep l _ => [local_id l]
  | CheckStep _ _ => []
  end.

(* Uses of variables that earlier steps bound. *)
Definition uses (prev : list step_view) (step : step_view) : nat :=
  let bound := flat_map step_binds prev in
  let count ids := List.length (filter (fun i => existsb (Nat.eqb i) bound) ids) in
  match step with
  | Unconstrained _ s _ | SuchThat _ s _ | CheckStep s _ => count (source_locals s)
  | LetStep _ value => count (distinct (argument_locals value))
  | MatchStep _ _ => 0
  end.

Definition uses_score : step_scorer nat nat_sum.
Proof. refine {| step_score := fun _ prev step _ => uses prev step |}. intros. nat_order. Defined.

Definition density_policy : policy :=
  lex_policy (fold_policy nat_max grade_score (Some forced_checks_count) Extremal)
             (fold_policy nat_sum uses_score None Additive).

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
