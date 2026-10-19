module N = Quickchick_plugin.NewGenericLib

let v = N.var_of_string
let relation name vars =
  N.DTyCtr (N.ty_ctr_of_string name, List.map (fun x -> N.DTyVar (v x)) vars)

let name_of_source = function
  | N.SrcNonrec (N.DTyCtr (name, _)) -> Some (N.ty_ctr_to_string name)
  | _ -> None

let source_order schedule =
  List.filter_map (function
    | N.S_ST (_, source, _) | N.S_Check (source, _) -> name_of_source source
    | _ -> None) schedule

let owner_key order =
  let footprint = function
    | "A" -> ["x"] | "B" -> ["y"] | "C" -> ["x"; "z"]
    | "D" -> ["x"; "y"] | "E" -> ["y"; "z"] | _ -> [] in
  List.map (fun variable ->
    List.find_opt (fun name -> List.mem variable (footprint name)) order)
    ["x"; "y"; "z"]

let mode_signature schedule =
  let relation_modes = List.filter_map (function
    | N.S_ST (outputs, source, _) ->
      Option.map (fun name ->
        (name, List.map (fun (var, _) -> N.var_to_string var) outputs
          |> List.sort compare)) (name_of_source source)
    | N.S_Check (source, _) ->
      Option.map (fun name -> (name, [])) (name_of_source source)
    | _ -> None) schedule |> List.sort compare in
  let unconstrained = List.filter_map (function
    | N.S_UC (var, _, _) -> Some (N.var_to_string var)
    | _ -> None) schedule |> List.sort compare in
  relation_modes, unconstrained

let quotient_signatures schedules =
  List.map (fun schedule ->
    owner_key (source_order schedule), mode_signature schedule) schedules
  |> List.sort_uniq compare

let quotient_signatures_for footprints schedules =
  let owner_key order =
    List.map (fun variable ->
      List.find_opt (fun name ->
        List.mem variable (List.assoc name footprints)) order)
      ["x"; "y"; "z"] in
  List.map (fun schedule ->
    owner_key (source_order schedule), mode_signature schedule) schedules
  |> List.sort_uniq compare

let variable_uses schedule =
  let source_vars = function
    | N.SrcNonrec term -> N.variables_in_hypothesis term
    | N.SrcRec (_, args) | N.SrcMutrec (_, args) | N.SrcDef (_, args) ->
      List.concat_map N.variables_in_hypothesis args in
  let rec visit bound = function
    | [] -> 0
    | step :: rest ->
      let source, added = match step with
        | N.S_UC (var, src, _) -> Some src, [var]
        | N.S_ST (outputs, src, _) -> Some src, List.map fst outputs
        | N.S_Check (src, _) -> Some src, []
        | N.S_Match (_, pat) -> None, N.pat_vars pat
        | N.S_Let (var, term) -> Some (N.SrcNonrec term), [var] in
      let here = match source with
        | None -> 0
        | Some src -> List.length (List.filter (fun var ->
          List.mem var bound) (source_vars src)) in
      here + visit (added @ bound) rest in
  visit [] schedule

let same_variable_uses_per_signature key schedules =
  let groups = List.map (fun schedule ->
    key schedule, variable_uses schedule) schedules in
  let keys = List.map fst groups |> List.sort_uniq compare in
  List.for_all (fun signature ->
    let scores = List.filter_map (fun (k, score) ->
      if k = signature then Some score else None) groups
      |> List.sort_uniq compare in
    List.length scores = 1) keys

let test_small_footprints nat rec_call =
  let variables = List.map (fun x -> (v x, nat)) ["x"; "y"; "z"] in
  let vars_of_mask mask =
    List.filteri (fun i _ -> mask land (1 lsl i) <> 0) ["x"; "y"; "z"] in
  let check_case footprints =
    let hypotheses = List.map (fun (name, vars) ->
      relation name vars) footprints in
    let complete = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~reduce_orderings:false
      variables hypotheses [] rec_call N.D_Gen in
    let reduced = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 variables hypotheses [] rec_call N.D_Gen in
    assert (quotient_signatures_for footprints complete =
            quotient_signatures_for footprints reduced);
    let signature schedule =
      let key = quotient_signatures_for footprints [schedule] in
      List.hd key in
    assert (same_variable_uses_per_signature signature complete) in
  let cases = ref 0 in
  for a = 1 to 7 do
    for b = 1 to 7 do
      for c = 1 to 7 do
        let footprints = ["A", vars_of_mask a; "B", vars_of_mask b;
                          "C", vars_of_mask c] in
        check_case footprints;
        incr cases
      done
    done
  done;
  Printf.printf "typed three-hypothesis footprint cases=%d passed\n" !cases;
  let four_cases = ref 0 in
  for a = 1 to 7 do
    for b = 1 to 7 do
      for c = 1 to 7 do
        for d = 1 to 7 do
          check_case ["A", vars_of_mask a; "B", vars_of_mask b;
                      "C", vars_of_mask c; "D", vars_of_mask d];
          incr four_cases
        done
      done
    done
  done;
  Printf.printf "typed four-hypothesis footprint cases=%d passed\n" !four_cases

let () =
  let hypotheses = [
    relation "A" ["x"];
    relation "B" ["y"];
    relation "C" ["x"; "z"];
    relation "D" ["x"; "y"];
    relation "E" ["y"; "z"];
  ] in
  let nat = N.DTyCtr (N.ty_ctr_of_string "nat", []) in
  let variables = List.map (fun x -> (v x, nat)) ["x"; "y"; "z"] in
  let rec_call = (N.ty_ctr_of_string "Never", []) in
  let complete_stats = N.empty_prefix_search_stats () in
  let complete = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~reduce_orderings:false ~stats:complete_stats
      variables hypotheses [] rec_call N.D_Gen in
  let reduced_stats = N.empty_prefix_search_stats () in
  let reduced = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~stats:reduced_stats
      variables hypotheses [] rec_call N.D_Gen in
  let wanted = ["B"; "E"; "C"; "A"; "D"] in
  let legacy = N.possible_schedules_with_legacy_pruning
      ~max_schedules:100000 variables hypotheses [] rec_call N.D_Gen in
  assert (List.exists (fun schedule -> source_order schedule = wanted) complete);
  assert (not (List.exists (fun schedule -> source_order schedule = wanted) legacy));
  let unique_owners schedules =
    List.map (fun schedule -> owner_key (source_order schedule)) schedules
    |> List.sort_uniq compare in
  assert (List.length (unique_owners complete) = 16);
  assert (List.length (unique_owners reduced) = 16);
  assert (List.length (List.map source_order reduced |> List.sort_uniq compare) = 16);
  assert (complete_stats.completed_prefixes = 288);
  assert (reduced_stats.completed_prefixes = 32);
  assert (reduced_stats.visited_nodes < complete_stats.visited_nodes);
  assert (reduced_stats.processed_mode_choices <
          complete_stats.processed_mode_choices);
  let early_stats = N.empty_prefix_search_stats () in
  ignore (N.possible_schedules_with_advanced_pruning
    ~max_schedules:2 ~stats:early_stats
    variables hypotheses [] rec_call N.D_Gen);
  assert (early_stats.completed_prefixes = 3);
  assert (early_stats.visited_nodes < reduced_stats.visited_nodes);
  assert (early_stats.processed_mode_choices <
          reduced_stats.processed_mode_choices);
  Printf.printf "prefix work: exhaustive nodes=%d leaves=%d modes=%d; POR nodes=%d leaves=%d modes=%d; early nodes=%d leaves=%d modes=%d\n"
    complete_stats.visited_nodes complete_stats.completed_prefixes
    complete_stats.processed_mode_choices
    reduced_stats.visited_nodes reduced_stats.completed_prefixes
    reduced_stats.processed_mode_choices
    early_stats.visited_nodes early_stats.completed_prefixes
    early_stats.processed_mode_choices;
  assert (quotient_signatures complete = quotient_signatures reduced);
  assert (same_variable_uses_per_signature
    (fun schedule -> List.hd (quotient_signatures [schedule])) complete);
  assert (List.length (unique_owners legacy) < 16);
  let distinct_orders schedules =
    List.map source_order schedules |> List.sort_uniq compare in
  let class_sizes =
    List.map (fun key ->
      List.length (List.filter (fun schedule ->
        owner_key (source_order schedule) = key) complete))
      (unique_owners complete) in
  let order_class_sizes =
    List.map (fun key ->
      List.length (List.filter (fun order -> owner_key order = key)
        (distinct_orders complete))) (unique_owners complete) in
  let canonical_orders =
    List.map (fun key ->
      List.find (fun order -> owner_key order = key)
        (distinct_orders complete)) (unique_owners complete) in
  let canonical_candidates =
    List.filter (fun schedule ->
      List.mem (source_order schedule) canonical_orders) complete in
  Printf.printf "distinct orders=%d, candidates/class min=%d max=%d, orders/class min=%d max=%d\n"
    (List.length (distinct_orders complete))
    (List.fold_left min max_int class_sizes)
    (List.fold_left max 0 class_sizes)
    (List.fold_left min max_int order_class_sizes)
    (List.fold_left max 0 order_class_sizes);
  Printf.printf "canonical-order candidates=%d\n"
    (List.length canonical_candidates);
  Printf.printf "sleep-set candidates=%d, distinct orders=%d\n"
    (List.length reduced)
    (List.length (distinct_orders reduced));
  Printf.printf "typed five-hypothesis schedule retained (%d candidates, %d owner maps; legacy %d)\n"
    (List.length complete) (List.length (unique_owners complete))
    (List.length (unique_owners legacy));
  let fixed_checks = N.possible_schedules_with_advanced_pruning
      ~reduce_orderings:false
      [v "x", nat] [relation "F" ["x"]; relation "G" ["x"]]
      [v "x"] rec_call N.D_Check in
  let orders = List.map source_order fixed_checks |> List.sort_uniq compare in
  assert (orders = [["F"; "G"]; ["G"; "F"]]);
  let independent_names =
    List.init 10 (fun i -> "I" ^ string_of_int i) in
  let independent_variables =
    List.map (fun name -> v name, nat) independent_names in
  let independent_stats = N.empty_prefix_search_stats () in
  let independent_schedules = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~stats:independent_stats
      independent_variables
      (List.map (fun name -> relation name [name]) independent_names)
      (List.map fst independent_variables) rec_call N.D_Check in
  assert (List.length independent_schedules = 1);
  assert (independent_stats.completed_prefixes = 1);
  Printf.printf "ten independent checks: nodes=%d leaves=%d modes=%d\n"
    independent_stats.visited_nodes independent_stats.completed_prefixes
    independent_stats.processed_mode_choices;
  assert (independent_stats.visited_nodes = 11);
  assert (independent_stats.processed_mode_choices = 10);
  let x_type = N.DTyCtr (N.ty_ctr_of_string "T", [N.DTyVar (v "y")]) in
  let typed_dependency = N.possible_schedules_with_advanced_pruning
      [v "x", x_type; v "y", nat]
      [relation "H" ["x"]; relation "J" ["y"]]
      [] rec_call N.D_Gen in
  let typed_orders = List.map source_order typed_dependency
    |> List.sort_uniq compare in
  assert (typed_orders = [["H"; "J"]; ["J"; "H"]]);
  let nested = N.DTyCtr (N.ty_ctr_of_string "K", [
    N.DCtr (N.constructor_of_string "Wrap", [N.DTyVar (v "x")])]) in
  let nonplain = N.possible_schedules_with_advanced_pruning
      [v "x", nat; v "y", nat]
      [nested; relation "J" ["y"]] [] rec_call N.D_Gen in
  assert (List.length (List.map source_order nonplain
    |> List.sort_uniq compare) = 2);
  test_small_footprints nat rec_call
