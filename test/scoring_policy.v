From Coq Require Import List String Arith.
From QuickChick Require Import SchedulingPolicy.
Import ListNotations.
Open Scope string_scope.

Definition demo_spec : spec_view := {|
  spec_application := TApply (TGlobal "Demo.Rel") [TLocal 0];
  spec_outputs := [1];
  spec_mode := Generate;
  spec_constrained := true
|}.

Definition demo_source : source_view := {|
  source_category := External;
  source_application := TApply (TGlobal "Demo.Dep") [TLocal 0];
  source_inputs := [0];
  source_finite_pins := [0]
|}.

Record cost := { failures : nat; work : nat }.
Definition zero_cost : cost := {| failures := 0; work := 0 |}.
Definition add_cost (a b : cost) : cost := {|
  failures := failures a + failures b;
  work := work a + work b
|}.

Definition demo_scorer : scorer cost := {|
  score_step := fun _ step _ => match step with
    | CheckStep _ _ => {| failures := 1; work := 1 |}
    | _ => {| failures := 0; work := 1 |}
    end;
  (* Inspect the complete schedule: a match followed by a check is costlier
     than the same checks without a match. A step-only fold cannot express it. *)
  score_schedule := fun _ schedule scores =>
    let total := fold_left add_cost scores zero_cost in
    let matches := existsb (fun '(step, _) => match step with
      | MatchStep _ _ => true | _ => false end) (schedule_steps schedule) in
    if matches then add_cost total {| failures := 2; work := 0 |}
    else total;
  score_leaf := fun _ leaf scored => match scored with
    | [] => {| failures := 10; work := 0 |}
    | (_, score) :: _ =>
      match leaf_pattern leaf with
      | PConstructor _ _ => add_cost score {| failures := 0; work := 1 |}
      | _ => score
      end
    end;
  score_inductive := fun _ _ leaves =>
    fold_left add_cost (map snd leaves) zero_cost;
  compare_scores := fun a b =>
    match Nat.compare (failures a) (failures b) with
    | Eq => Nat.compare (work a) (work b)
    | result => result
    end
|}.

Definition demo_context : score_context cost := {|
  current_spec := demo_spec;
  locals := [{| local_id := 0; local_type := TGlobal "Coq.Init.Datatypes.nat" |}];
  original_inputs := [0];
  dependencies := [(demo_spec, Pending)]
|}.

Definition checked : schedule_view := {|
  schedule_steps := [(CheckStep demo_source true, Checking)];
  schedule_result := None
|}.

Definition matched : schedule_view := {|
  schedule_steps := [(MatchStep 0 PWild, Backtracking);
    (CheckStep demo_source true, Checking)];
  schedule_result := None
|}.

Example user_defined_score_is_typed :
  score_one_schedule demo_scorer demo_context checked =
    {| failures := 1; work := 1 |}.
Proof. vm_compute. reflexivity. Qed.

Example supplied_helper_matches_explicit_state :
  score_with_supplied_dependencies demo_scorer demo_spec [] [0]
    [demo_spec] checked =
  score_with_dependency_states demo_scorer demo_spec [] [0]
    [(demo_spec, SuppliedInstance)] checked.
Proof. reflexivity. Qed.

Example whole_schedule_can_inspect_steps :
  score_one_schedule demo_scorer demo_context matched =
    {| failures := 3; work := 2 |}.
Proof. vm_compute. reflexivity. Qed.

Definition covered : leaf_view := {|
  leaf_pattern := PConstructor "Demo.Zero" [];
  leaf_covering := ["Demo.Ctor"]
|}.
Definition missed : leaf_view := {|
  leaf_pattern := PWild;
  leaf_covering := []
|}.
Definition demo_inductive : inductive_view := {|
  inductive_spec := demo_spec;
  inductive_constructors := [{|
    constructor_name := "Demo.Ctor";
    constructor_recursive := false;
    constructor_schedule := checked
  |}];
  inductive_leaves := [covered; missed]
|}.

Example leaf_patterns_and_uncovered_leaves_are_visible :
  score_one_inductive demo_scorer demo_context demo_inductive =
    {| failures := 11; work := 2 |}.
Proof. vm_compute. reflexivity. Qed.

Definition demo_policy : policy := {|
  score_type := cost;
  policy_scorer := demo_scorer;
  lower_bound := fun _ _ => zero_cost;
  policy_grouping := None;
  policy_bound_sound := None
|}.

(* No cost is below zero, so the zero bound is admissible. *)
Example zero_bound_is_admissible :
  bound_admissible demo_scorer (fun _ _ => zero_cost).
Proof.
  intros ctx node s _. unfold no_worse.
  generalize (score_one_schedule demo_scorer ctx s). intros [f w]. simpl.
  destruct f; simpl; [destruct w|]; discriminate.
Qed.

Definition demo_node : search_node_view := {|
  node_steps := [{| committed_view := MatchStep 0 PWild;
                    committed_grade := Backtracking; committed_certain := true |}];
  node_forced_checks := 1;
  node_remaining := [(TApply (TGlobal "Demo.Remaining") [TLocal 0], true)];
  node_bound := [0]
|}.

(* A schedule below the node keeps its committed step and checks the forced
   hypothesis. *)
Example below_demo_node :
  completes demo_node {|
    schedule_steps := [(MatchStep 0 PWild, Backtracking); (CheckStep demo_source true, Checking)];
    schedule_result := None |}.
Proof.
  exists [(MatchStep 0 PWild, Backtracking)], [(CheckStep demo_source true, Checking)].
  repeat split; repeat constructor.
Qed.

Definition view_bound_policy : policy := {|
  score_type := cost;
  policy_scorer := demo_scorer;
  lower_bound := fun ctx node =>
    match node_remaining node, node_bound node, dependencies ctx with
    | _ :: _, _ :: _, _ :: _ => zero_cost
    | _, _, _ => {| failures := 1; work := 0 |}
    end;
  policy_grouping := None;
  policy_bound_sound := None
|}.

Example a_rocq_bound_can_inspect_search_state :
  lower_bound view_bound_policy demo_context demo_node = zero_cost.
Proof. vm_compute. reflexivity. Qed.

Example candidate_ids_break_score_ties :
  choose_best demo_scorer [(4, zero_cost); (1, zero_cost);
    (0, {| failures := 1; work := 0 |})] = Some (1, zero_cost).
Proof. vm_compute. reflexivity. Qed.

Example applied_arguments_remain_distinct :
  TApply (TGlobal "Coq.Init.Datatypes.list") [TLocal 0] <> TLocal 0.
Proof. discriminate. Qed.

Example dependency_states_remain_distinct :
  (Pending : dependency_state cost) <> Completed zero_cost.
Proof. discriminate. Qed.
