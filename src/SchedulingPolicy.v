(* Experimental policy interface. The plugin does not select these policies yet. *)
From Coq Require Import List String.
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

Record remaining_hypothesis_view := {
  hypothesis_id : nat;
  hypothesis_formula : term_view;
  hypothesis_output_groups : list (list nat)
}.

Record choice_view := {
  chosen_hypothesis : nat;
  chosen_outputs : list nat;
  chosen_position : nat
}.

Inductive binding_origin :=
| OriginalInput
| ForcedBy (hypothesis : nat)
| ProducedBy (hypothesis : nat)
| PatternBound (hypothesis : nat).

Record bound_local_view := {
  bound_id : nat;
  bound_origin : binding_origin
}.

(* The current schedule may be reconstructed after insertion; it is not
   assumed to be a prefix of every completed descendant. *)
Record search_node_view (S : Type) := {
  node_current : schedule_view;
  node_remaining : list remaining_hypothesis_view;
  node_choices : list choice_view;
  node_bound_locals : list bound_local_view;
  node_dependencies : list (spec_view * dependency_state S)
}.
Arguments node_current {S} _.
Arguments node_remaining {S} _.
Arguments node_choices {S} _.
Arguments node_bound_locals {S} _.
Arguments node_dependencies {S} _.

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

Record policy := {
  score_type : Type;
  policy_scorer : scorer score_type;
  lower_bound : score_context score_type -> search_node_view score_type -> score_type
}.

(* A search adapter must establish this against its actual descendant relation.
   Merely providing a callback does not certify that pruning is sound. *)
Definition admissible_bound (p : policy)
    (completion : score_context (score_type p) ->
      search_node_view (score_type p) -> score_type p -> Prop) : Prop :=
  forall ctx node final_score, completion ctx node final_score ->
    compare_scores (policy_scorer p) (lower_bound p ctx node) final_score <> Gt.

Definition score_one_schedule {S} (p : scorer S) (ctx : score_context S)
    (schedule : schedule_view) : S :=
  score_schedule p ctx schedule
    (map (fun '(step, grade) => score_step p ctx step grade)
      (schedule_steps schedule)).

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

(* Equality is retained so candidate identifiers can break score ties. *)
Definition strictly_prunable (p : policy) (incumbent : score_type p)
    (ctx : score_context (score_type p))
    (node : search_node_view (score_type p)) : bool :=
  match compare_scores (policy_scorer p) incumbent (lower_bound p ctx node) with
  | Lt => true
  | Eq | Gt => false
  end.

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
