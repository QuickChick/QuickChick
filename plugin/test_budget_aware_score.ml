module N = Quickchick_plugin.NewGenericLib
module B = Quickchick_plugin.BudgetAwareScore
module U = Quickchick_plugin.NewUnifyQC

let v = N.var_of_string
let relation name args =
  N.DTyCtr (N.ty_ctr_of_string name, args)
let variable name = N.DTyVar (v name)
let src name args = N.SrcNonrec (relation name args)

let gen_key = {
  B.relation = N.ty_ctr_of_string "Root";
  output_indices = [0]; derive_sort = N.D_Gen;
}
let check_key = { gen_key with B.derive_sort = N.D_Check }
let dep_key = {
  B.relation = N.ty_ctr_of_string "Dep";
  output_indices = [0]; derive_sort = N.D_Check;
}
let enum_key = { dep_key with B.derive_sort = N.D_Enum }
let dep_score = { B.empty with density = B.Checking }
let enum_score = { B.empty with density = B.Partial; fabrication = 5 }
let pinned_relation : N.rocq_relation =
  let pin = N.ty_ctr_of_string "Pinned" in
  (pin, [],
   [N.constructor_of_string "zero",
      N.DTyCtr (pin, [N.DCtr (N.constructor_of_string "O", [])]);
    N.constructor_of_string "one",
      N.DTyCtr (pin, [N.DCtr (N.constructor_of_string "S",
        [N.DCtr (N.constructor_of_string "O", [])])])],
   N.DTyCtr (N.ty_ctr_of_string "nat", []))
let pinned_positions = B.finite_pins_of_relation pinned_relation
let check_pin_lookup () =
  let calls = ref 0 in
  let pinned = N.ty_ctr_of_string "Pinned" in
  let missing = N.ty_ctr_of_string "Missing" in
  let lookup = B.finite_pins_with_lookup (fun name ->
    incr calls;
    if N.ty_ctr_eq name pinned then Some pinned_relation else None) in
  assert (lookup pinned = [0]);
  assert (lookup pinned = [0]);
  assert (lookup missing = []);
  assert (lookup missing = []);
  assert (!calls = 2);
  let failing = B.finite_pins_with_lookup (fun _ -> failwith "unavailable") in
  assert (failing pinned = [])
let unpinned_positions =
  let name = N.ty_ctr_of_string "Unpinned" in
  B.finite_pins_of_relation (name, [],
    [N.constructor_of_string "zero",
       N.DTyCtr (name, [N.DCtr (N.constructor_of_string "O", [])]);
     N.constructor_of_string "any",
       N.DProd ((v "n", relation "nat" []),
         N.DTyCtr (name, [variable "n"]))],
    relation "nat" [])
let context inputs = {
  B.input_vars = List.map v inputs;
  finite_pins = (fun name ->
    if N.ty_ctr_eq name (N.ty_ctr_of_string "Pinned") then
      pinned_positions else []);
  completed_dependency = (fun request ->
    if request.B.key = dep_key then Some dep_score
    else if request.B.key = enum_key then Some enum_score
    else None);
}

let tuple score =
  (score.B.selectivity, B.density_rank score.B.density,
   score.B.fabrication, B.locality_rank score.B.locality,
   score.B.input_check_deps, score.B.var_deps)

let tuple_string (a, b, c, d, e, f) =
  Printf.sprintf "%d,%d,%d,%d,%d,%d" a b c d e f

let check label expected context key steps =
  match B.score_schedule context key steps with
  | Error message -> failwith (label ^ ": " ^ message)
  | Ok score ->
    if tuple score <> expected then
      failwith (Printf.sprintf "%s: expected %s, got %s" label
        (tuple_string expected) (tuple_string (tuple score)));
    Printf.printf "%s: %s\n" label (tuple_string (tuple score))

let check_scheduler_adapter () =
  let nat = relation "nat" [] in
  let x = v "input_x" and y = v "output_y" in
  let rx = v "result_x" and ry = v "result_y" in
  let root = N.ty_ctr_of_string "BudgetRoot" in
  let typ = N.DProd ((x, nat), N.DProd ((y, nat),
    N.DArrow (relation "BudgetRel" [variable "input_x"; variable "output_y"],
      N.DTyCtr (root, [variable "input_x"; variable "output_y"])))) in
  let prepared = ref None in
  let candidates = U.type_to_schedules
    ~on_prepared:(fun inputs -> prepared := Some inputs)
    typ (Some root) (Some (N.ty_ctr_of_string "BudgetCtor"))
    [rx, nat; ry, nat] [ry] N.D_Gen true in
  let inputs = match !prepared with
    | Some inputs -> inputs | None -> failwith "prepared inputs were not reported" in
  assert (List.mem rx inputs);
  assert (not (List.mem ry inputs));
  assert (candidates <> []);
  List.iter (fun (((_, _), matches, eqs) as candidate) ->
    assert (matches = [] && eqs = []);
    let ctx = { (context []) with B.input_vars = inputs } in
    match B.score_candidate ctx { gen_key with B.relation = root } candidate with
    | Ok _ -> ()
    | Error message -> failwith ("real scheduler: " ^ message)) candidates

let check_applied_dependencies () =
  let args_a = [N.DTyParam (v "A"); variable "y"] in
  let args_b = [N.DTyParam (v "B"); variable "y"] in
  let step args = N.S_ST ([v "y", relation "Nat" []],
    src "Applied" args, N.PS_E) in
  let requests = B.required_dependencies check_key
    [step args_a; step args_b] in
  assert (List.length requests = 4);
  assert (List.for_all (fun request ->
    request.B.key.output_indices = [1] &&
    (request.B.applied_args = args_a || request.B.applied_args = args_b))
    requests);
  let selected = { B.key = { B.relation = N.ty_ctr_of_string "Applied";
      output_indices = [1]; derive_sort = N.D_Check };
    applied_args = args_a } in
  let ctx = { (context []) with B.completed_dependency =
    (fun request -> if request = selected then Some dep_score else None) } in
  let first = B.step_score ctx check_key (step args_a) in
  let second = B.step_score ctx check_key (step args_b) in
  match first, second with
  | Ok first, Ok second ->
    assert (first.B.density = B.Checking);
    assert (second.B.density = B.Partial)
  | _ -> failwith "applied dependency scoring failed"

let check_candidate_preludes () =
  let x = v "match_x" and y = v "match_y" in
  let matched = N.S_Match (x, N.PVar y) in
  let candidate = (([], N.CheckerSchedule),
    [x, N.PVar y], [x, y]) in
  (match B.candidate_steps candidate with
   | [first; N.S_Check (_, true)] -> assert (first = matched)
   | _ -> failwith "candidate prelude was not materialized");
  let ctx = context [] in
  (match B.score_candidate ctx check_key candidate with
   | Ok score -> assert (score.B.density = B.Checking)
   | Error message -> failwith message);
  let nat = relation "nat" [] in
  let root = N.ty_ctr_of_string "MatchedBudgetRoot" in
  let result_x = v "matched_result_x" and result_y = v "matched_result_y" in
  let typ = N.DProd ((x, nat), N.DTyCtr (root, [
    N.DCtr (N.constructor_of_string "Coq.Init.Datatypes.S", [variable "match_x"]);
    variable "match_x"])) in
  let candidates = U.type_to_schedules typ (Some root)
    (Some (N.ty_ctr_of_string "MatchedBudgetCtor"))
    [result_x, nat; result_y, nat] [result_y] N.D_Gen true in
  assert (List.exists (fun (_, matches, _) -> matches <> []) candidates);
  List.iter (fun candidate ->
    match B.score_candidate (context [])
      { gen_key with B.relation = root } candidate with
    | Ok _ -> ()
    | Error message -> failwith ("matched candidate: " ^ message)) candidates

let () =
  check_pin_lookup ();
  check_scheduler_adapter ();
  check_applied_dependencies ();
  check_candidate_preludes ();
  assert (pinned_positions = [0]);
  Printf.printf "pinned-positions: [%s]\n"
    (String.concat ", " (List.map string_of_int pinned_positions));
  assert (unpinned_positions = []);
  print_endline "unpinned-positions: []";
  let higher_order = N.ty_ctr_of_string "HigherOrder" in
  assert (B.finite_pins_of_relation
    (higher_order, [], [N.constructor_of_string "intro",
       N.DTyCtr (higher_order,
         [N.DApp (variable "f", [N.DCtr (N.constructor_of_string "O", [])])])],
     relation "nat" []) = []);
  check "mixed-check" (0, 3, 0, 1, 1, 2) (context ["x"]) gen_key
    [N.S_Check (src "Rel" [variable "x"; variable "y"; variable "y"], true)];
  check "type-parameter" (0, 3, 0, 1, 1, 1) (context ["T"]) gen_key
    [N.S_Check (src "Rel" [N.DTyParam (v "T"); variable "x"], true)];
  check "checker-arbitrary" (0, 0, 1, 1, 0, 0) (context []) check_key
    [N.S_UC (v "y", src "Nat" [], N.PS_E)];
  check "checker-dependency" (0, 3, 5, 1, 0, 0) (context []) check_key
    [N.S_ST ([v "y", relation "Nat" []], src "Dep" [variable "y"], N.PS_E)];
  check "generator-dependency" (0, 1, 0, 1, 0, 0) (context []) gen_key
    [N.S_ST ([v "y", relation "Nat" []], src "Dep" [variable "y"], N.PS_G)];
  check "recursive" (0, 1, 0, 0, 0, 0) (context []) gen_key
    [N.S_ST ([v "y", relation "Nat" []],
       N.SrcRec (v "rec", [variable "y"]), N.PS_G)];
  check "same-relation" (0, 1, 0, 2, 0, 0) (context []) gen_key
    [N.S_ST ([v "y", relation "Nat" []], src "Root" [variable "y"], N.PS_G)];
  check "loose-pinned" (1, 3, 0, 1, 0, 1) (context []) gen_key
    [N.S_UC (v "v", src "Nat" [], N.PS_G);
     N.S_Check (src "Pinned" [variable "v"], true)];
  check "loose-two-pins" (1, 3, 0, 1, 0, 2) (context []) gen_key
    [N.S_UC (v "v", src "Nat" [], N.PS_G);
     N.S_Check (src "Pinned" [variable "v"], true);
     N.S_Check (src "Pinned" [variable "v"], true)];
  check "finite-producer" (0, 1, 0, 1, 0, 0) (context []) gen_key
    [N.S_ST ([v "v", relation "Nat" []],
       src "Pinned" [variable "v"], N.PS_G)];
  let loose = match B.score_schedule (context []) gen_key
    [N.S_UC (v "v", src "Nat" [], N.PS_G);
     N.S_Check (src "Pinned" [variable "v"], true)] with
    | Ok score -> score | Error message -> failwith message in
  let finite = match B.score_schedule (context []) gen_key
    [N.S_ST ([v "v", relation "Nat" []],
       src "Pinned" [variable "v"], N.PS_G)] with
    | Ok score -> score | Error message -> failwith message in
  let report label expected score =
    assert (tuple score = expected);
    Printf.printf "%s: %s\n" label (tuple_string (tuple score)) in
  let best_leaf = B.best_of [loose; finite] in
  report "best-leaf" (0, 1, 0, 1, 0, 0) best_leaf;
  report "uncovered" (0, 1, 0, 0, 0, 0) (B.best_of []);
  report "inductive" (0, 1, 0, 1, 0, 0)
    (B.inductive_score [[loose; finite]; []]);
  assert (B.compare
    { B.empty with selectivity = 0; fabrication = 5 }
    { B.empty with selectivity = 1 } < 0);
  assert (tuple (B.best_of []) = (0, 1, 0, 0, 0, 0))
