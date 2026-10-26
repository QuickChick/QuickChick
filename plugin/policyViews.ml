(* OCaml mirror of the view types in theories SchedulingPolicy.v, exactly as
   Coq extracts them with QuickChick's settings (nat as int, string as char
   list). A compiled Rocq scoring policy is extracted with its view types
   mapped onto these, so the plugin and the policy share them. Keep this file
   in step with SchedulingPolicy.v; a mismatch makes policy compilation fail.
   [extraction_table] lists the Extract Inductive directives. *)

type comparison = Eq | Lt | Gt

type pattern_view =
| PWild
| PParameter
| PLocal of int
| PConstructor of char list * pattern_view list

type term_view =
| TLocal of int
| TGlobal of char list
| TSort of char list
| TGenerated of char list
| TImplicitHole
| TApply of term_view * term_view list
| TArrow of term_view * term_view
| TProduct of int * term_view * term_view
| TLambda of int * term_view * term_view
| TMatch of term_view * (pattern_view * term_view) list
| TNot of term_view
| TOpaque of int

type local_view = { local_id : int; local_type : term_view }

type derive_mode =
| Generate
| Enumerate
| Check
| TestTheorem

type producer_mode =
| Generator
| Enumerator

type source_kind =
| External
| SelfRecursive
| MutualRecursive
| DefinedSource

type source_view = { source_category : source_kind;
                     source_application : term_view;
                     source_inputs : int list; source_finite_pins : int list }

type step_view =
| Unconstrained of local_view * source_view * producer_mode
| SuchThat of local_view list * source_view * producer_mode
| CheckStep of source_view * bool
| MatchStep of int * pattern_view
| LetStep of local_view * term_view

type density =
| Checking
| Backtracking
| Neutral
| Partial
| Total

type schedule_view = { schedule_steps : (step_view * density) list;
                       schedule_result : term_view option }

type spec_view = { spec_application : term_view; spec_outputs : int list;
                   spec_mode : derive_mode; spec_constrained : bool }

type 's dependency_state =
| SuppliedInstance
| Pending
| InProgress
| Completed of 's

type 's score_context = { current_spec : spec_view; locals : local_view list;
                          original_inputs : int list;
                          dependencies : (spec_view * 's dependency_state)
                                         list }

type constructor_view = { constructor_name : char list;
                          constructor_recursive : bool;
                          constructor_schedule : schedule_view }

type leaf_view = { leaf_pattern : pattern_view; leaf_covering : char list list }

type inductive_view = { inductive_spec : spec_view;
                        inductive_constructors : constructor_view list;
                        inductive_leaves : leaf_view list }

type remaining_hypothesis_view = { hypothesis_id : int;
                                   hypothesis_formula : term_view;
                                   hypothesis_output_groups : int list list }

type choice_view = { chosen_hypothesis : int; chosen_outputs : int list;
                     chosen_position : int }

type binding_origin =
| OriginalInput
| ForcedBy of int
| ProducedBy of int
| PatternBound of int

type bound_local_view = { bound_id : int; bound_origin : binding_origin }

type 's search_node_view = { node_current : schedule_view;
                             node_remaining : remaining_hypothesis_view list;
                             node_choices : choice_view list;
                             node_bound_locals : bound_local_view list;
                             node_dependencies : (spec_view * 's
                                                 dependency_state) list }

(* (Rocq type, OCaml type, constructors, match function) *)
let extraction_table = [
  "QuickChick.SchedulingPolicy.pattern_view", "Quickchick_plugin.PolicyViews.pattern_view", ["Quickchick_plugin.PolicyViews.PWild"; "Quickchick_plugin.PolicyViews.PParameter"; "Quickchick_plugin.PolicyViews.PLocal"; "Quickchick_plugin.PolicyViews.PConstructor"], None;
  "QuickChick.SchedulingPolicy.term_view", "Quickchick_plugin.PolicyViews.term_view", ["Quickchick_plugin.PolicyViews.TLocal"; "Quickchick_plugin.PolicyViews.TGlobal"; "Quickchick_plugin.PolicyViews.TSort"; "Quickchick_plugin.PolicyViews.TGenerated"; "Quickchick_plugin.PolicyViews.TImplicitHole"; "Quickchick_plugin.PolicyViews.TApply"; "Quickchick_plugin.PolicyViews.TArrow"; "Quickchick_plugin.PolicyViews.TProduct"; "Quickchick_plugin.PolicyViews.TLambda"; "Quickchick_plugin.PolicyViews.TMatch"; "Quickchick_plugin.PolicyViews.TNot"; "Quickchick_plugin.PolicyViews.TOpaque"], None;
  "QuickChick.SchedulingPolicy.local_view", "Quickchick_plugin.PolicyViews.local_view", ["(fun (a0, a1) -> { Quickchick_plugin.PolicyViews.local_id = a0; Quickchick_plugin.PolicyViews.local_type = a1 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.local_id r.Quickchick_plugin.PolicyViews.local_type)");
  "QuickChick.SchedulingPolicy.derive_mode", "Quickchick_plugin.PolicyViews.derive_mode", ["Quickchick_plugin.PolicyViews.Generate"; "Quickchick_plugin.PolicyViews.Enumerate"; "Quickchick_plugin.PolicyViews.Check"; "Quickchick_plugin.PolicyViews.TestTheorem"], None;
  "QuickChick.SchedulingPolicy.producer_mode", "Quickchick_plugin.PolicyViews.producer_mode", ["Quickchick_plugin.PolicyViews.Generator"; "Quickchick_plugin.PolicyViews.Enumerator"], None;
  "QuickChick.SchedulingPolicy.source_kind", "Quickchick_plugin.PolicyViews.source_kind", ["Quickchick_plugin.PolicyViews.External"; "Quickchick_plugin.PolicyViews.SelfRecursive"; "Quickchick_plugin.PolicyViews.MutualRecursive"; "Quickchick_plugin.PolicyViews.DefinedSource"], None;
  "QuickChick.SchedulingPolicy.source_view", "Quickchick_plugin.PolicyViews.source_view", ["(fun (a0, a1, a2, a3) -> { Quickchick_plugin.PolicyViews.source_category = a0; Quickchick_plugin.PolicyViews.source_application = a1; Quickchick_plugin.PolicyViews.source_inputs = a2; Quickchick_plugin.PolicyViews.source_finite_pins = a3 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.source_category r.Quickchick_plugin.PolicyViews.source_application r.Quickchick_plugin.PolicyViews.source_inputs r.Quickchick_plugin.PolicyViews.source_finite_pins)");
  "QuickChick.SchedulingPolicy.step_view", "Quickchick_plugin.PolicyViews.step_view", ["Quickchick_plugin.PolicyViews.Unconstrained"; "Quickchick_plugin.PolicyViews.SuchThat"; "Quickchick_plugin.PolicyViews.CheckStep"; "Quickchick_plugin.PolicyViews.MatchStep"; "Quickchick_plugin.PolicyViews.LetStep"], None;
  "QuickChick.SchedulingPolicy.density", "Quickchick_plugin.PolicyViews.density", ["Quickchick_plugin.PolicyViews.Checking"; "Quickchick_plugin.PolicyViews.Backtracking"; "Quickchick_plugin.PolicyViews.Neutral"; "Quickchick_plugin.PolicyViews.Partial"; "Quickchick_plugin.PolicyViews.Total"], None;
  "QuickChick.SchedulingPolicy.schedule_view", "Quickchick_plugin.PolicyViews.schedule_view", ["(fun (a0, a1) -> { Quickchick_plugin.PolicyViews.schedule_steps = a0; Quickchick_plugin.PolicyViews.schedule_result = a1 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.schedule_steps r.Quickchick_plugin.PolicyViews.schedule_result)");
  "QuickChick.SchedulingPolicy.spec_view", "Quickchick_plugin.PolicyViews.spec_view", ["(fun (a0, a1, a2, a3) -> { Quickchick_plugin.PolicyViews.spec_application = a0; Quickchick_plugin.PolicyViews.spec_outputs = a1; Quickchick_plugin.PolicyViews.spec_mode = a2; Quickchick_plugin.PolicyViews.spec_constrained = a3 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.spec_application r.Quickchick_plugin.PolicyViews.spec_outputs r.Quickchick_plugin.PolicyViews.spec_mode r.Quickchick_plugin.PolicyViews.spec_constrained)");
  "QuickChick.SchedulingPolicy.dependency_state", "Quickchick_plugin.PolicyViews.dependency_state", ["Quickchick_plugin.PolicyViews.SuppliedInstance"; "Quickchick_plugin.PolicyViews.Pending"; "Quickchick_plugin.PolicyViews.InProgress"; "Quickchick_plugin.PolicyViews.Completed"], None;
  "QuickChick.SchedulingPolicy.score_context", "Quickchick_plugin.PolicyViews.score_context", ["(fun (a0, a1, a2, a3) -> { Quickchick_plugin.PolicyViews.current_spec = a0; Quickchick_plugin.PolicyViews.locals = a1; Quickchick_plugin.PolicyViews.original_inputs = a2; Quickchick_plugin.PolicyViews.dependencies = a3 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.current_spec r.Quickchick_plugin.PolicyViews.locals r.Quickchick_plugin.PolicyViews.original_inputs r.Quickchick_plugin.PolicyViews.dependencies)");
  "QuickChick.SchedulingPolicy.constructor_view", "Quickchick_plugin.PolicyViews.constructor_view", ["(fun (a0, a1, a2) -> { Quickchick_plugin.PolicyViews.constructor_name = a0; Quickchick_plugin.PolicyViews.constructor_recursive = a1; Quickchick_plugin.PolicyViews.constructor_schedule = a2 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.constructor_name r.Quickchick_plugin.PolicyViews.constructor_recursive r.Quickchick_plugin.PolicyViews.constructor_schedule)");
  "QuickChick.SchedulingPolicy.leaf_view", "Quickchick_plugin.PolicyViews.leaf_view", ["(fun (a0, a1) -> { Quickchick_plugin.PolicyViews.leaf_pattern = a0; Quickchick_plugin.PolicyViews.leaf_covering = a1 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.leaf_pattern r.Quickchick_plugin.PolicyViews.leaf_covering)");
  "QuickChick.SchedulingPolicy.inductive_view", "Quickchick_plugin.PolicyViews.inductive_view", ["(fun (a0, a1, a2) -> { Quickchick_plugin.PolicyViews.inductive_spec = a0; Quickchick_plugin.PolicyViews.inductive_constructors = a1; Quickchick_plugin.PolicyViews.inductive_leaves = a2 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.inductive_spec r.Quickchick_plugin.PolicyViews.inductive_constructors r.Quickchick_plugin.PolicyViews.inductive_leaves)");
  "QuickChick.SchedulingPolicy.remaining_hypothesis_view", "Quickchick_plugin.PolicyViews.remaining_hypothesis_view", ["(fun (a0, a1, a2) -> { Quickchick_plugin.PolicyViews.hypothesis_id = a0; Quickchick_plugin.PolicyViews.hypothesis_formula = a1; Quickchick_plugin.PolicyViews.hypothesis_output_groups = a2 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.hypothesis_id r.Quickchick_plugin.PolicyViews.hypothesis_formula r.Quickchick_plugin.PolicyViews.hypothesis_output_groups)");
  "QuickChick.SchedulingPolicy.choice_view", "Quickchick_plugin.PolicyViews.choice_view", ["(fun (a0, a1, a2) -> { Quickchick_plugin.PolicyViews.chosen_hypothesis = a0; Quickchick_plugin.PolicyViews.chosen_outputs = a1; Quickchick_plugin.PolicyViews.chosen_position = a2 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.chosen_hypothesis r.Quickchick_plugin.PolicyViews.chosen_outputs r.Quickchick_plugin.PolicyViews.chosen_position)");
  "QuickChick.SchedulingPolicy.binding_origin", "Quickchick_plugin.PolicyViews.binding_origin", ["Quickchick_plugin.PolicyViews.OriginalInput"; "Quickchick_plugin.PolicyViews.ForcedBy"; "Quickchick_plugin.PolicyViews.ProducedBy"; "Quickchick_plugin.PolicyViews.PatternBound"], None;
  "QuickChick.SchedulingPolicy.bound_local_view", "Quickchick_plugin.PolicyViews.bound_local_view", ["(fun (a0, a1) -> { Quickchick_plugin.PolicyViews.bound_id = a0; Quickchick_plugin.PolicyViews.bound_origin = a1 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.bound_id r.Quickchick_plugin.PolicyViews.bound_origin)");
  "QuickChick.SchedulingPolicy.search_node_view", "Quickchick_plugin.PolicyViews.search_node_view", ["(fun (a0, a1, a2, a3, a4) -> { Quickchick_plugin.PolicyViews.node_current = a0; Quickchick_plugin.PolicyViews.node_remaining = a1; Quickchick_plugin.PolicyViews.node_choices = a2; Quickchick_plugin.PolicyViews.node_bound_locals = a3; Quickchick_plugin.PolicyViews.node_dependencies = a4 })"], (Some "(fun f r -> f r.Quickchick_plugin.PolicyViews.node_current r.Quickchick_plugin.PolicyViews.node_remaining r.Quickchick_plugin.PolicyViews.node_choices r.Quickchick_plugin.PolicyViews.node_bound_locals r.Quickchick_plugin.PolicyViews.node_dependencies)");
  "Coq.Init.Datatypes.comparison", "Quickchick_plugin.PolicyViews.comparison", ["Quickchick_plugin.PolicyViews.Eq"; "Quickchick_plugin.PolicyViews.Lt"; "Quickchick_plugin.PolicyViews.Gt"], None;
]
