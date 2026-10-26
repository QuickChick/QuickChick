(* The scoring-policy interface: the views a policy sees and the contract
   its pruning bound must meet. QC Scorer compiles and selects a policy. *)
From Coq Require Import List String Arith.
Import ListNotations.

Set Universe Polymorphism.

(* A symbolic snapshot of a schedule. Local identifiers are unique within one
   snapshot; global names are qualified. Opaque handles preserve identity but
   deliberately do not reveal a term's structure. *)
Inductive pattern_view :=
| PWild
| PParameter
| PLocal (id : nat)
| PConstructor (name : string) (arguments : list pattern_view).

Inductive term_view :=
| TLocal (id : nat)
| TGlobal (name : string)
| TSort (name : string)
| TGenerated (name : string)
| TImplicitHole
| TApply (head : term_view) (arguments : list term_view)
| TArrow (domain codomain : term_view)
| TProduct (binder : nat) (domain body : term_view)
| TLambda (binder : nat) (domain body : term_view)
| TMatch (scrutinee : term_view) (branches : list (pattern_view * term_view))
| TNot (body : term_view)
| TOpaque (handle : nat).

Record local_view := {
  local_id : nat;
  local_type : term_view
}.

Inductive derive_mode := Generate | Enumerate | Check | TestTheorem.
Inductive producer_mode := Generator | Enumerator.
Inductive source_kind := External | SelfRecursive | MutualRecursive | DefinedSource.

Record source_view := {
  source_category : source_kind;
  source_application : term_view;
  source_inputs : list nat;
  source_finite_pins : list nat
}.

Inductive step_view :=
| Unconstrained (output : local_view) (source : source_view) (mode : producer_mode)
| SuchThat (outputs : list local_view) (source : source_view) (mode : producer_mode)
| CheckStep (source : source_view) (positive : bool)
| MatchStep (input : nat) (pattern : pattern_view)
| LetStep (output : local_view) (value : term_view).

(* Density is engine metadata. A policy may inspect it, but its own score type
   need not be a density or a number. *)
Inductive density := Checking | Backtracking | Neutral | Partial | Total.

Record schedule_view := {
  schedule_steps : list (step_view * density);
  schedule_result : option term_view
}.

Record spec_view := {
  spec_application : term_view;
  spec_outputs : list nat;
  spec_mode : derive_mode;
  spec_constrained : bool
}.

Inductive dependency_state (S : Type) :=
| SuppliedInstance
| Pending
| InProgress
| Completed (score : S).
Arguments SuppliedInstance {S}.
Arguments Pending {S}.
Arguments InProgress {S}.
Arguments Completed {S} _.

Record score_context (S : Type) := {
  current_spec : spec_view;
  locals : list local_view;
  original_inputs : list nat;
  dependencies : list (spec_view * dependency_state S)
}.
Arguments current_spec {S} _.
Arguments locals {S} _.
Arguments original_inputs {S} _.
Arguments dependencies {S} _.

Record constructor_view := {
  constructor_name : string;
  constructor_recursive : bool;
  constructor_schedule : schedule_view
}.

Record leaf_view := {
  leaf_pattern : pattern_view;
  leaf_covering : list string
}.

Record inductive_view := {
  inductive_spec : spec_view;
  inductive_constructors : list constructor_view;
  inductive_leaves : list leaf_view
}.

(* A node of the schedule search. Its committed steps begin every complete
   schedule below it, in order. A committed step's grade is [certain] unless
   it depends on a derivation still in progress, in which case a schedule
   below may grade it differently. [node_forced_checks] of the remaining
   hypotheses have all their arguments bound, so every schedule below checks
   them. *)
Record committed_step := {
  committed_view : step_view;
  committed_grade : density;
  committed_certain : bool
}.

(* The engine's variable uses: at each step, the variables of its source
   that earlier steps bound. A nonrecursive source counts its distinct
   variables; a generated call counts each argument's distinct variables. *)
Fixpoint argument_locals (t : term_view) : list nat :=
  match t with
  | TLocal i => [i]
  | TApply _ args => flat_map argument_locals args
  | _ => []
  end.

Definition distinct (ids : list nat) : list nat := nodup Nat.eq_dec ids.

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

Definition step_uses (prev : list step_view) (step : step_view) : nat :=
  let bound := flat_map step_binds prev in
  let count ids := List.length (filter (fun i => existsb (Nat.eqb i) bound) ids) in
  match step with
  | Unconstrained _ s _ | SuchThat _ s _ | CheckStep s _ => count (source_locals s)
  | LetStep _ value => count (distinct (argument_locals value))
  | MatchStep _ _ => 0
  end.

(* The uses of [steps], run after [prev]. *)
Fixpoint uses_after (prev : list step_view) (steps : list (step_view * density)) : nat :=
  match steps with
  | [] => 0
  | (step, _) :: rest => step_uses prev step + uses_after (prev ++ [step]) rest
  end.

Record search_node_view := {
  node_steps : list committed_step;
  node_forced_checks : nat;
  (* Every schedule below the node incurs at least this many further
     variable uses. *)
  node_future_uses : nat;
  node_remaining : list (term_view * bool);
  node_bound : list nat
}.

(* A positive check: what a forced hypothesis becomes. *)
Definition is_check (step : step_view) : bool :=
  match step with CheckStep _ true => true | _ => false end.

Definition count_checks (steps : list (step_view * density)) : nat :=
  List.length (filter (fun '(step, _) => is_check step) steps).

(* A step of a schedule below the node that comes from committed step [c]. *)
Definition kept (c : committed_step) (step : step_view * density) : Prop :=
  fst step = committed_view c /\
  (committed_certain c = true -> snd step = committed_grade c).

(* [s] is a complete schedule below [node]. *)
Definition completes (node : search_node_view) (s : schedule_view) : Prop :=
  exists committed extension,
    Forall2 kept (node_steps node) committed /\
    schedule_steps s = committed ++ extension /\
    node_forced_checks node <= count_checks extension /\
    node_future_uses node <= uses_after (map committed_view (node_steps node)) extension.

Record scorer (S : Type) := {
  score_step : score_context S -> step_view -> density -> S;
  score_schedule : score_context S -> schedule_view -> list S -> S;
  score_leaf : score_context S -> leaf_view -> list (string * S) -> S;
  score_inductive : score_context S -> inductive_view -> list (leaf_view * S) -> S;
  compare_scores : S -> S -> comparison
}.
Arguments score_step {S} _ _ _ _.
Arguments score_schedule {S} _ _ _ _.
Arguments score_leaf {S} _ _ _ _.
Arguments score_inductive {S} _ _ _ _.
Arguments compare_scores {S} _ _ _.

(* How a policy's score combines over footprint-disjoint hypothesis groups,
   which lets the plugin search each group separately and keep a Pareto set
   per group. The score of a schedule built from independent groups must be
   the [group_combine] of their scores, in any order, with [group_unit] as
   the score of no steps. [compare_scores] must be lexicographic over
   [group_fields], most significant first. An [Additive] field keeps its
   strict order and ties when both sides are combined with the same score
   (a sum); an [Extremal] field keeps only its non-strict order (a maximum
   or minimum). The plugin trusts these laws; QC_SCHEDULE_GROUPS=verify
   compares grouped with joint search. *)
Inductive field_kind := Additive | Extremal.

Record grouping (S : Type) := {
  group_unit : S;
  group_combine : S -> S -> S;
  group_fields : list (field_kind * (S -> S -> comparison))
}.
Arguments group_unit {S} _.
Arguments group_combine {S} _ _ _.
Arguments group_fields {S} _.

Definition score_one_schedule {S} (p : scorer S) (ctx : score_context S)
    (schedule : schedule_view) : S :=
  score_schedule p ctx schedule
    (map (fun '(step, grade) => score_step p ctx step grade)
      (schedule_steps schedule)).

(* Lower scores are better. *)
Definition no_worse {S} (p : scorer S) (a b : S) : Prop :=
  compare_scores p a b <> Gt.

(* A bound is admissible when no complete schedule below a node scores
   better than it. *)
Definition bound_admissible {S} (p : scorer S)
    (bound : score_context S -> search_node_view -> S) : Prop :=
  forall ctx node s, completes node s ->
    no_worse p (bound ctx node) (score_one_schedule p ctx s).

Record policy := {
  score_type : Type;
  policy_scorer : scorer score_type;
  lower_bound : score_context score_type -> search_node_view -> score_type;
  (* None: the plugin searches each constructor jointly. *)
  policy_grouping : option (grouping score_type);
  (* The plugin prunes with [lower_bound] only when this proof is given. *)
  policy_bound_sound : option (bound_admissible policy_scorer lower_bound)
}.

Definition proves_bound (p : policy) : bool :=
  match policy_bound_sound p with Some _ => true | None => false end.

Definition score_with_dependency_states {S} (p : scorer S)
    (spec : spec_view) (local_types : list local_view)
    (inputs : list nat) (deps : list (spec_view * dependency_state S))
    (schedule : schedule_view) : S :=
  score_one_schedule p {|
    current_spec := spec;
    locals := local_types;
    original_inputs := inputs;
    dependencies := deps
  |} schedule.

(* Compatibility helper for candidates whose source obligations all resolve
   to existing instances. General candidates need a typed policy score memo. *)
Definition score_with_supplied_dependencies {S} (p : scorer S)
    (spec : spec_view) (local_types : list local_view)
    (inputs : list nat) (supplied : list spec_view)
    (schedule : schedule_view) : S :=
  score_with_dependency_states p spec local_types inputs
    (map (fun dep => (dep, SuppliedInstance)) supplied) schedule.

Definition score_one_inductive {S} (p : scorer S) (ctx : score_context S)
    (inductive : inductive_view) : S :=
  let constructors := map (fun c =>
    (constructor_name c, score_one_schedule p ctx (constructor_schedule c)))
    (inductive_constructors inductive) in
  let leaves := map (fun leaf =>
    let covering := filter (fun '(name, _) =>
      existsb (String.eqb name) (leaf_covering leaf)) constructors in
    (leaf, score_leaf p ctx leaf covering)) (inductive_leaves inductive) in
  score_inductive p ctx inductive leaves.

Definition choose_best {S} (p : scorer S) (candidates : list (nat * S))
    : option (nat * S) :=
  fold_left (fun best candidate =>
    match best with
    | None => Some candidate
    | Some (id, score) =>
      match compare_scores p (snd candidate) score with
      | Lt => Some candidate
      | Eq => if Nat.ltb (fst candidate) id then Some candidate else best
      | Gt => best
      end
    end) candidates None.
