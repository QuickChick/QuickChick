From QuickChick Require Import SchedulingPolicy QuickChick.
From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

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

Definition policy_quote_candidate_cost (schedule : schedule_view) : quote_cost :=
  let '(backtracking, partial) :=
    policy_quote_grade_counts (schedule_steps schedule) in
  {| quote_depth := backtracking;
     quote_weight := partial + List.length (schedule_steps schedule) |}.

Definition policy_quote_compare_cost (left right : quote_cost) : comparison :=
  match Nat.compare (quote_depth left) (quote_depth right) with
  | Eq => Nat.compare (quote_weight left) (quote_weight right)
  | order => order
  end.

Definition policy_quote_bad_compare (_ _ : quote_cost) : nat := 0.

Definition policy_quote_name_ends (name suffix : string) : bool :=
  String.eqb
    (String.substring (String.length name - String.length suffix)
       (String.length suffix) name)
    suffix.

Definition policy_quote_is_list_nat
    (entry : spec_view * dependency_state quote_cost) : bool :=
  match spec_application (fst entry) with
  | TApply (TGlobal list_name) [TGlobal nat_name] =>
      andb (policy_quote_name_ends list_name "list")
           (policy_quote_name_ends nat_name "nat")
  | _ => false
  end.

Definition policy_quote_record_scorer : scorer quote_cost := {|
  score_step := fun _ step _ =>
    {| quote_depth := match step with
       | Unconstrained _ _ _ => 2
       | SuchThat _ _ _ => 3
       | _ => 1
       end;
       quote_weight := 1 |};
  score_schedule := fun context _ scores =>
    {| quote_depth := List.fold_left
         (fun total score => total + quote_depth score) scores 0;
       quote_weight := List.length (locals context) +
         List.length (original_inputs context) +
         List.length (spec_outputs (current_spec context)) +
         List.length (dependencies context) +
         (if List.existsb policy_quote_is_list_nat (dependencies context)
          then 10 else 0) |};
  score_leaf := fun _ _ _ => {| quote_depth := 0; quote_weight := 0 |};
  score_inductive := fun _ _ _ => {| quote_depth := 0; quote_weight := 0 |};
  compare_scores := policy_quote_compare_cost
|}.

Definition policy_quote_first_source (schedule : schedule_view) : term_view :=
  match schedule_steps schedule with
  | (SuchThat _ source _, _) :: _ => source_application source
  | (Unconstrained _ source _, _) :: _ => source_application source
  | (CheckStep source _, _) :: _ => source_application source
  | _ => TImplicitHole
  end.

Definition policy_quote_equal_sources (_ _ : term_view) : comparison := Eq.

Definition policy_quote_order_sensitive_cost
    (schedule : schedule_view) : quote_cost :=
  let priority := match policy_quote_first_source schedule with
    | TApply (TGlobal name) _ =>
      if policy_quote_name_ends name "policy_compare_c"
      then 0
      else if policy_quote_name_ends name "policy_compare_b"
      then 1 else 2
    | _ => 3
    end in
  {| quote_depth := priority;
     quote_weight := List.length (schedule_steps schedule) |}.

Polymorphic Record quote_poly_cost (A : Type) := {
  quote_poly_payload : A;
  quote_poly_rank : nat
}.
Arguments quote_poly_payload {A} _.
Arguments quote_poly_rank {A} _.

Definition policy_quote_poly_score (schedule : schedule_view)
    : quote_poly_cost (list nat) :=
  {| quote_poly_payload := [List.length (schedule_steps schedule)];
     quote_poly_rank := quote_depth (policy_quote_order_sensitive_cost schedule) |}.

Definition policy_quote_poly_compare
    (left right : quote_poly_cost (list nat)) : comparison :=
  Nat.compare (quote_poly_rank left) (quote_poly_rank right).

Derive Inductive Schedule policy_quote_probe derive "Check" opt "true".

Inductive policy_quote_param (A : Type) : list A -> Prop :=
| QuoteNil : policy_quote_param A nil
| QuoteCons : forall x xs, policy_quote_param A xs -> policy_quote_param A (x :: xs).

Derive Inductive Schedule policy_quote_param derive "Check" opt "true".

Inductive policy_quote_generated : nat -> Prop :=
| QuoteGenerated : forall n, policy_quote_generated n.

Derive Inductive Schedule policy_quote_generated 0 derive "Gen" opt "true".

Inductive policy_quote_list : list nat -> Prop :=
| QuoteList : forall xs, policy_quote_list xs.

Derive Inductive Schedule policy_quote_list 0 derive "Gen" opt "true".

Inductive policy_quote_missing (A : Type) : A -> Prop :=
| QuoteMissing : forall value, policy_quote_missing A value.

Derive Inductive Schedule policy_quote_missing 1 derive "Gen" opt "true".

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

Inductive policy_compare_a : nat -> Prop := CompareA : forall x, policy_compare_a x.
Inductive policy_compare_b : nat -> nat -> Prop :=
| CompareB : forall x y, policy_compare_b x y.
Inductive policy_compare_c : nat -> nat -> Prop :=
| CompareC : forall y z, policy_compare_c y z.

Inductive policy_compare_root : nat -> nat -> nat -> Prop :=
| CompareRoot : forall x y z,
    policy_compare_a x -> policy_compare_b x y ->
    policy_compare_c y z -> policy_compare_root x y z.

Derive Inductive Schedule policy_compare_root 0 1 2 derive "Gen" opt "true".
