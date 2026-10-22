From QuickChick Require Import SchedulingPolicy QuickChick.
From Coq Require Import List.
Import ListNotations.

Inductive policy_quote_probe : nat -> Prop :=
| QuoteZero : policy_quote_probe 0
| QuoteSucc : forall n, policy_quote_probe n -> policy_quote_probe (S n).

Definition policy_quote_probe_score (view : term_view) : nat :=
  match view with
  | TProduct _ _ _ => 7
  | _ => 0
  end.

Record quote_cost := { quote_depth : nat; quote_weight : nat }.

Definition policy_quote_record_score (view : term_view) : quote_cost :=
  match view with
  | TProduct _ _ _ => {| quote_depth := 2; quote_weight := 3 |}
  | _ => {| quote_depth := 0; quote_weight := 1 |}
  end.

Definition policy_quote_step_score (step : step_view) : nat :=
  match step with
  | CheckStep _ _ => 1
  | SuchThat _ _ _ => 2
  | Unconstrained _ _ _ => 3
  | MatchStep _ _ => 4
  | LetStep _ _ => 5
  end.

Definition policy_quote_step_fields (step : step_view) : nat * nat * nat :=
  match step with
  | SuchThat outputs source _ =>
      (List.length outputs, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | Unconstrained _ source _ =>
      (1, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | CheckStep source _ =>
      (0, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | _ => (0, 0, 0)
  end.

Definition policy_quote_schedule_score (schedule : schedule_view)
    : nat * nat :=
  (List.length (schedule_steps schedule),
   match schedule_result schedule with Some _ => 1 | None => 0 end).

Definition policy_quote_match_links (schedule : schedule_view)
    : bool * bool :=
  match schedule_steps schedule, schedule_result schedule with
  | (SuchThat (output :: nil) _ _, _) ::
      (MatchStep input (PConstructor _ (PLocal payload :: nil)), _) :: _,
      Some (TLocal result) =>
      (Nat.eqb input (local_id output), Nat.eqb payload result)
  | _, _ => (false, false)
  end.

Definition policy_quote_schedule_view (schedule : schedule_view) := schedule.

Fixpoint policy_quote_grade_counts
    (steps : list (step_view * density)) : nat * nat :=
  match steps with
  | [] => (0, 0)
  | (_, grade) :: rest =>
      let '(backtracking, partial) := policy_quote_grade_counts rest in
      match grade with
      | Backtracking => (S backtracking, partial)
      | Partial => (backtracking, S partial)
      | _ => (backtracking, partial)
      end
  end.

Definition policy_quote_schedule_grades (schedule : schedule_view) :=
  policy_quote_grade_counts (schedule_steps schedule).

Derive Inductive Schedule policy_quote_probe derive "Check" opt "true".

Inductive policy_quote_param (A : Type) : list A -> Prop :=
| QuoteNil : policy_quote_param A nil
| QuoteCons : forall x xs, policy_quote_param A xs -> policy_quote_param A (x :: xs).

Derive Inductive Schedule policy_quote_param derive "Check" opt "true".

Inductive policy_quote_generated : nat -> Prop :=
| QuoteGenerated : forall n, policy_quote_generated n.

Derive Inductive Schedule policy_quote_generated 0 derive "Gen" opt "true".

Inductive policy_quote_premise : nat -> Prop :=
| QuoteFromPremise : forall n, policy_quote_probe n -> policy_quote_premise n.

Derive Inductive Schedule policy_quote_premise 0 derive "Gen" opt "true".

Inductive policy_quote_zero : nat -> Prop :=
| QuoteOnlyZero : policy_quote_zero 0.

Inductive policy_quote_pinned : nat -> Prop :=
| QuotePinned : forall n, policy_quote_zero n -> policy_quote_pinned n.

Derive Inductive Schedule policy_quote_pinned 0 derive "Gen" opt "true".

Inductive policy_quote_indexed : nat -> nat -> Prop :=
| QuoteIndexed : forall n, policy_quote_indexed n (S n).

Inductive policy_quote_with_input : nat -> nat -> Prop :=
| QuoteWithInput : forall x y,
    policy_quote_indexed x y -> policy_quote_with_input x y.

Derive Inductive Schedule policy_quote_with_input 1 derive "Gen" opt "true".

Inductive policy_quote_nested : nat -> Prop :=
| QuoteNested : forall n,
    policy_quote_probe (S n) -> policy_quote_nested n.

Derive Inductive Schedule policy_quote_nested 0 derive "Gen" opt "true".
