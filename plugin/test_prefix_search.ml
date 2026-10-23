module N = Quickchick_plugin.NewGenericLib
module U = Quickchick_plugin.NewUnifyQC
module Ranking = Quickchick_plugin.ScheduleRanking

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

let owner_key_for footprints order =
  List.map (fun variable ->
    List.find_opt (fun name ->
      List.mem variable (List.assoc name footprints)) order)
    ["x"; "y"; "z"]

let quotient_signatures_for footprints schedules =
  List.map (fun schedule ->
    owner_key_for footprints (source_order schedule), mode_signature schedule) schedules
  |> List.sort_uniq compare

let canonical_order_for_key footprints key =
  let names = List.map fst footprints in
  let edges = List.concat_map (fun (variable, owner) ->
    match owner with
    | None -> []
    | Some first ->
      List.filter_map (fun (name, vars) ->
        if name <> first && List.mem variable vars then
          Some (first, name) else None) footprints)
    (List.combine ["x"; "y"; "z"] key) in
  let rec build prefix remaining = match remaining with
    | [] -> List.rev prefix
    | _ ->
      let ready = List.find (fun name ->
        not (List.exists (fun (before, after) ->
          after = name && List.mem before remaining) edges)) remaining in
      build (ready :: prefix) (List.filter ((<>) ready) remaining) in
  build [] names

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

(* A small mode-dependent dependency model. D's producing mode is treated as
   cycle-dependent in the prefix bound; its grade is known at completed leaves.
   Other grades stand in for certified direct or acyclic call summaries. *)
let model_step_grade ~prefer_dense = function
  | N.S_UC _ | N.S_Let _ -> 4
  | N.S_Check _ -> 0
  | N.S_Match _ -> 1
  | N.S_ST (_, N.SrcRec _, _) -> 3
  | N.S_ST (_, source, _) ->
    (match name_of_source source with
     | Some "D" -> 3
     | Some ("A" | "C") when not prefer_dense -> 2
     | Some _ when not prefer_dense -> 1
     | _ -> 4)

let model_known_grade ~prefer_dense = function
  | N.S_ST (_, source, _) when name_of_source source = Some "D" -> None
  | step -> Some (model_step_grade ~prefer_dense step)

(* Test-only certificate for plain, nonrecursive relation calls whose arguments
   are distinct direct variables. Source rewriting invalidates this shortcut. *)
let direct_variable_use_bound footprints schedule =
  let processed = source_order schedule in
  let remaining = List.filter (fun (name, _) ->
    not (List.mem name processed)) footprints in
  let bound = List.concat_map (function
    | N.S_UC (var, _, _) -> [N.var_to_string var]
    | N.S_ST (outputs, _, _) ->
      List.map (fun (var, _) -> N.var_to_string var) outputs
    | N.S_Match (_, pat) -> List.map N.var_to_string (N.pat_vars pat)
    | N.S_Let (var, _) -> [N.var_to_string var]
    | N.S_Check _ -> []) schedule in
  variable_uses schedule +
  List.fold_left (fun total variable ->
    let mentions = List.fold_left (fun count (_, vars) ->
      if List.mem variable vars then count + 1 else count) 0 remaining in
    total + if List.mem variable bound then mentions
      else max 0 (mentions - 1)) 0 ["x"; "y"; "z"]

let model_features ~prefer_dense ~terminal ~footprints schedule =
  let grades = List.map
    (if terminal then fun step -> Some (model_step_grade ~prefer_dense step)
     else model_known_grade ~prefer_dense) schedule in
  Ranking.prefix_bound ~prefer_dense ~known_grades:grades
    ~variable_uses:(if terminal then variable_uses schedule
      else direct_variable_use_bound footprints schedule)

let best_features ~prefer_dense ~footprints policy schedules =
  match schedules with
  | [] -> failwith "empty schedule set"
  | first :: rest ->
    List.fold_left (fun best schedule ->
      let score = model_features ~prefer_dense ~terminal:true ~footprints schedule in
      if Ranking.compare ~prefer_dense policy score best < 0 then score
      else best)
      (model_features ~prefer_dense ~terminal:true ~footprints first) rest

let positive_checks schedule =
  List.fold_left (fun count -> function
    | N.S_Check (_, true) -> count + 1
    | _ -> count) 0 schedule

(* Plain positive relations only: each future producer consumes a distinct
   variable, so no more than the remaining unbound variables can produce. *)
let check_count_bound footprints schedule =
  let processed = source_order schedule |> List.length in
  let modes, unconstrained = mode_signature schedule in
  let bound_vars = unconstrained @ List.concat_map snd modes
    |> List.sort_uniq compare in
  let mentioned = List.concat_map snd footprints |> List.sort_uniq compare in
  let unbound = List.length (List.filter (fun var ->
    not (List.mem var bound_vars)) mentioned) in
  positive_checks schedule +
    max 0 (List.length footprints - processed - unbound)

let same_variable_uses_per_signature key schedules =
  let groups = List.map (fun schedule ->
    key schedule, variable_uses schedule) schedules in
  let keys = List.map fst groups |> List.sort_uniq compare in
  List.for_all (fun signature ->
    let scores = List.filter_map (fun (k, score) ->
      if k = signature then Some score else None) groups
      |> List.sort_uniq compare in
    List.length scores = 1) keys

let is_path_prefix prefix path =
  let rec loop prefix path = match prefix, path with
    | [], _ -> true
    | x :: xs, y :: ys when x = y -> loop xs ys
    | _ -> false in
  loop prefix path

let is_schedule_prefix prefix schedule =
  let rec loop prefix schedule = match prefix, schedule with
    | [], _ -> true
    | x :: xs, y :: ys when x = y -> loop xs ys
    | _ -> false in
  loop prefix schedule

(* Converting a constrained output allocates a fresh match variable each
   time. Prefix observation and leaf conversion therefore differ only by
   alpha-renaming of these variables, even when the typed steps are stable. *)
let alpha_normalize_schedule schedule =
  let match_variables = List.filter_map (function
    | N.S_Match (name, _) -> Some name
    | _ -> None) schedule in
  let renaming = List.mapi (fun index name ->
    name, v ("qc_alpha_" ^ string_of_int index)) match_variables in
  let rename name = match List.assoc_opt name renaming with
    | Some canonical -> canonical | None -> name in
  let rec rename_pat = function
    | N.PCtr (ctor, args) -> N.PCtr (ctor, List.map rename_pat args)
    | N.PVar name -> N.PVar (rename name)
    | N.PParam -> N.PParam
    | N.PWild -> N.PWild in
  let rec rename_term = function
    | N.DArrow (a, b) -> N.DArrow (rename_term a, rename_term b)
    | N.DLambda (name, ty, body) ->
      N.DLambda (rename name, rename_term ty, rename_term body)
    | N.DProd ((name, ty), body) ->
      N.DProd ((rename name, rename_term ty), rename_term body)
    | N.DTyParam name -> N.DTyParam name
    | N.DTyCtr (ctor, args) -> N.DTyCtr (ctor, List.map rename_term args)
    | N.DCtr (ctor, args) -> N.DCtr (ctor, List.map rename_term args)
    | N.DTyVar name -> N.DTyVar (rename name)
    | N.DApp (head, args) ->
      N.DApp (rename_term head, List.map rename_term args)
    | N.DMatch (scrutinee, branches) ->
      N.DMatch (rename_term scrutinee,
        List.map (fun (pat, body) -> rename_pat pat, rename_term body) branches)
    | N.DNot body -> N.DNot (rename_term body)
    | N.DHole -> N.DHole in
  let rename_source = function
    | N.SrcNonrec ty -> N.SrcNonrec (rename_term ty)
    | N.SrcRec (name, args) ->
      N.SrcRec (rename name, List.map rename_term args)
    | N.SrcMutrec (name, args) ->
      N.SrcMutrec (rename name, List.map rename_term args)
    | N.SrcDef (name, args) ->
      N.SrcDef (rename name, List.map rename_term args) in
  List.map (function
    | N.S_UC (name, source, sort) ->
      N.S_UC (rename name, rename_source source, sort)
    | N.S_ST (outputs, source, sort) ->
      N.S_ST (List.map (fun (name, ty) -> rename name, rename_term ty) outputs,
        rename_source source, sort)
    | N.S_Check (source, polarity) ->
      N.S_Check (rename_source source, polarity)
    | N.S_Match (name, pat) -> N.S_Match (rename name, rename_pat pat)
    | N.S_Let (name, body) -> N.S_Let (rename name, rename_term body)) schedule

let converted_prefix_pairs = ref 0
let alpha_only_prefix_pairs = ref 0

let check_converted_prefixes observations =
  let leaves = List.filter (fun (_, terminal, _) -> terminal) observations in
  List.iter (fun (path, terminal, prefix) ->
    if not terminal then begin
      (match List.rev prefix with
       | [] | (N.S_ST _ | N.S_Check _ | N.S_Match _ | N.S_Let _) :: _ -> ()
       | N.S_UC _ :: _ ->
         failwith "converted open prefix ends in an unconstrained step");
      let descendants = List.filter (fun (leaf_path, _, _) ->
        is_path_prefix path leaf_path) leaves in
      assert (descendants <> []);
      List.iter (fun (_, _, completed) ->
        incr converted_prefix_pairs;
        if not (is_schedule_prefix prefix completed) then begin
          assert (variable_uses prefix =
            variable_uses (alpha_normalize_schedule prefix));
          assert (variable_uses completed =
            variable_uses (alpha_normalize_schedule completed));
          incr alpha_only_prefix_pairs;
        end;
        if not (is_schedule_prefix
          (alpha_normalize_schedule prefix)
          (alpha_normalize_schedule completed)) then
          failwith (Printf.sprintf "converted prefix changed: path=%d prefix=[%s] complete=[%s]"
            (List.length path)
            (String.concat "; " (List.map N.schedule_step_to_string prefix))
            (String.concat "; " (List.map N.schedule_step_to_string completed)))) descendants
    end) observations

let check_prefix_use_bounds observations =
  let leaves = List.filter (fun (_, terminal, _) -> terminal) observations in
  let first_leaf_score =
    match List.find_opt (fun (_, terminal, _) -> terminal)
      (List.rev observations) with
    | Some (_, _, score) -> score
    | None -> assert false in
  let checked = ref 0 in
  let tight = ref 0 in
  let positive = ref 0 in
  let beats_first = ref 0 in
  let total_gap = ref 0 in
  List.iter (fun (path, terminal, bound) ->
    if not terminal then begin
      let descendants = List.filter (fun (leaf_path, _, _) ->
        is_path_prefix path leaf_path) leaves in
      assert (descendants <> []);
      incr checked;
      if bound > 0 then incr positive;
      let minimum = List.fold_left (fun acc (_, _, completed_uses) ->
        min acc completed_uses) max_int descendants in
      if bound = minimum then incr tight;
      if bound > first_leaf_score then incr beats_first;
      total_gap := !total_gap + minimum - bound;
      List.iter (fun (_, _, completed_uses) ->
        assert (bound <= completed_uses)) descendants
    end) observations;
  !checked, !tight, !positive, !beats_first, !total_gap,
  first_leaf_score

let simulate_strict_pruning observations =
  let incumbent = ref None in
  let pruned_paths = ref [] in
  let visited = ref 0 in
  let scored_leaves = ref 0 in
  List.iter (fun (path, terminal, bound) ->
    if not (List.exists (fun pruned -> is_path_prefix pruned path)
      !pruned_paths) then begin
      incr visited;
      if terminal then begin
        incr scored_leaves;
        incumbent := Some (match !incumbent with
          | None -> bound | Some old -> min old bound)
      end else match !incumbent with
        | Some old when old < bound ->
          pruned_paths := path :: !pruned_paths
        | _ -> ()
    end) (List.rev observations);
  !visited, !scored_leaves, List.length !pruned_paths, !incumbent

let test_unifier_prefix_boundary nat =
  let x = v "unify_x" and y = v "unify_y" in
  let rx = v "result_x" and ry = v "result_y" in
  let root = N.DTyCtr (N.ty_ctr_of_string "PrefixRoot",
    [N.DTyVar x; N.DTyVar y]) in
  let typ = N.DProd ((x,nat), N.DProd ((y,nat),
    N.DArrow (relation "P" ["unify_x"],
      N.DArrow (relation "Q" ["unify_x";"unify_y"], root)))) in
  let observations = ref [] in
  let candidates = U.type_to_schedules
    ~on_prefix:(fun path terminal triple ->
      observations := (path, terminal, triple) :: !observations)
    typ (Some (N.ty_ctr_of_string "PrefixRoot"))
    (Some (N.ty_ctr_of_string "PrefixCtor"))
    [rx,nat;ry,nat] [rx;ry] N.D_Gen true in
  assert (candidates <> []);
  let views = List.map (fun (path, terminal, ((steps,_), matches, eqs)) ->
    assert (List.for_all (fun ((_,_), ms, es) ->
      ms = matches && es = eqs) candidates);
    path, terminal, steps) !observations in
  check_converted_prefixes views;
  let terminal_steps = List.filter_map (function
    | _, true, steps -> Some (alpha_normalize_schedule steps)
    | _ -> None) views |> List.sort_uniq compare in
  let returned_steps = List.map (fun ((steps,_),_,_) ->
    alpha_normalize_schedule steps) candidates |> List.sort_uniq compare in
  assert (terminal_steps = returned_steps);
  let matched = N.DTyCtr (N.ty_ctr_of_string "PrefixRoot", [
    N.DCtr (N.constructor_of_string "Coq.Init.Datatypes.S", [N.DTyVar x]);
    N.DTyVar x]) in
  let matched_observations = ref [] in
  let matched_candidates = U.type_to_schedules
    ~on_prefix:(fun path terminal triple ->
      matched_observations := (path, terminal, triple) :: !matched_observations)
    (N.DProd ((x,nat), matched))
    (Some (N.ty_ctr_of_string "PrefixRoot"))
    (Some (N.ty_ctr_of_string "MatchedCtor"))
    [rx,nat;ry,nat] [ry] N.D_Gen true in
  assert (matched_candidates <> []);
  assert (List.exists (fun (_, matches, _) -> matches <> []) matched_candidates);
  assert (List.for_all (fun (_, _, (_, matches, eqs)) ->
    List.exists (fun (_, candidate_matches, candidate_eqs) ->
      matches = candidate_matches && eqs = candidate_eqs)
      matched_candidates) !matched_observations);
  check_converted_prefixes
    (List.map (fun (path, terminal, ((steps,_),_,_)) ->
      path, terminal, steps) !matched_observations);
  Printf.printf "post-unification prefix correspondence: leaves=%d; match prelude present\n"
    (List.length terminal_steps)

let test_small_footprints nat rec_call =
  let variables = List.map (fun x -> (v x, nat)) ["x"; "y"; "z"] in
  let vars_of_mask mask =
    List.filteri (fun i _ -> mask land (1 lsl i) <> 0) ["x"; "y"; "z"] in
  let check_case ?(verify_bounds=false) footprints =
    let hypotheses = List.map (fun (name, vars) ->
      relation name vars) footprints in
    let observations = ref [] in
    let structural_observations = ref [] in
    let converted_observations = ref [] in
    let observer = if verify_bounds then
      Some (fun path terminal stable ->
        converted_observations :=
          (path, terminal, stable) :: !converted_observations;
        observations :=
          (path, terminal, variable_uses stable) :: !observations;
        structural_observations :=
          (path, terminal,
           if terminal then variable_uses stable else
             direct_variable_use_bound footprints stable)
          :: !structural_observations)
      else None in
    let complete = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~reduce_orderings:false
      ?on_prefix:observer
      variables hypotheses [] rec_call N.D_Gen in
    if verify_bounds then begin
      check_converted_prefixes !converted_observations;
      ignore (check_prefix_use_bounds !observations);
      ignore (check_prefix_use_bounds !structural_observations);
      let check_observations = ref [] in
      ignore (N.possible_schedules_with_advanced_pruning
        ~max_schedules:100000 ~maximal_outputs:true ~reduce_orderings:false
        ~on_prefix:(fun path terminal schedule ->
          check_observations := (path, terminal,
            if terminal then positive_checks schedule
            else check_count_bound footprints schedule)
            :: !check_observations)
        variables hypotheses [] rec_call N.D_Gen);
      ignore (check_prefix_use_bounds !check_observations)
    end;
    let reduced = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 variables hypotheses [] rec_call N.D_Gen in
    assert (quotient_signatures_for footprints complete =
            quotient_signatures_for footprints reduced);
    let keys = List.map (fun schedule ->
      owner_key_for footprints (source_order schedule)) complete
      |> List.sort_uniq compare in
    let canonical_orders = List.map (canonical_order_for_key footprints) keys in
    let canonical = List.filter (fun schedule ->
      List.mem (source_order schedule) canonical_orders) complete in
    assert (quotient_signatures_for footprints complete =
            quotient_signatures_for footprints canonical);
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
        check_case ~verify_bounds:true footprints;
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
          check_case ~verify_bounds:true
            ["A", vars_of_mask a; "B", vars_of_mask b;
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
  let direct_footprints =
    ["A", ["x"]; "B", ["y"]; "C", ["x"; "z"];
     "D", ["x"; "y"]; "E", ["y"; "z"]] in
  let complete_stats = N.empty_prefix_search_stats () in
  let complete_observations = ref [] in
  let complete_converted_observations = ref [] in
  let complete_structural_bounds = ref [] in
  let check_floor_observations = ref [] in
  let complete = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~reduce_orderings:false ~stats:complete_stats
      ~on_prefix_with_floor:(fun path terminal floor stable ->
        check_floor_observations :=
          (path, terminal, floor, stable) :: !check_floor_observations)
      ~on_prefix:(fun path terminal stable ->
        complete_converted_observations :=
          (path, terminal, stable) :: !complete_converted_observations;
        complete_observations :=
          (path, terminal, variable_uses stable) :: !complete_observations;
        complete_structural_bounds :=
          (path, terminal,
           if terminal then variable_uses stable else
             direct_variable_use_bound direct_footprints stable)
          :: !complete_structural_bounds)
      variables hypotheses [] rec_call N.D_Gen in
  check_converted_prefixes !complete_converted_observations;
  let completed_checks = List.filter_map (fun (path, terminal, _, stable) ->
    if terminal then Some (path, positive_checks stable) else None)
    !check_floor_observations in
  let useful_floors = ref 0 in
  List.iter (fun (path, terminal, floor, stable) ->
    if not terminal then begin
      if floor > 0 then incr useful_floors;
      List.iter (fun (leaf_path, checks) ->
        if is_path_prefix path leaf_path then
          assert (positive_checks stable + floor <= checks))
        completed_checks
    end) !check_floor_observations;
  assert (!useful_floors > 0);
  let reduced_stats = N.empty_prefix_search_stats () in
  let reduced_observations = ref [] in
  let reduced_structural_bounds = ref [] in
  let reduced = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~stats:reduced_stats
      ~on_prefix:(fun path terminal stable ->
        reduced_observations :=
          (path, terminal, variable_uses stable) :: !reduced_observations;
        reduced_structural_bounds :=
          (path, terminal,
           if terminal then variable_uses stable else
             direct_variable_use_bound direct_footprints stable)
          :: !reduced_structural_bounds)
      variables hypotheses [] rec_call N.D_Gen in
  let all_bound_counts = check_prefix_use_bounds !complete_observations in
  let por_bound_counts = check_prefix_use_bounds !reduced_observations in
  let all_structural_counts =
    check_prefix_use_bounds !complete_structural_bounds in
  let por_structural_counts =
    check_prefix_use_bounds !reduced_structural_bounds in
  let show_counts label (checked, tight, positive, beats_first, total_gap, first_leaf) =
    Printf.printf "%s variable-use bounds: checked=%d tight=%d positive=%d first=%d prunable=%d mean-gap=%.2f\n"
      label checked tight positive first_leaf beats_first
      (float_of_int total_gap /. float_of_int checked) in
  show_counts "exhaustive" all_bound_counts;
  show_counts "POR" por_bound_counts;
  show_counts "exhaustive structural" all_structural_counts;
  show_counts "POR structural" por_structural_counts;
  let all_pruning = simulate_strict_pruning !complete_structural_bounds in
  let por_pruning = simulate_strict_pruning !reduced_structural_bounds in
  let show_pruning label (visited, leaves, pruned, optimum) =
    Printf.printf "%s simulated strict pruning: nodes=%d leaves=%d cuts=%d optimum=%s\n"
      label visited leaves pruned
      (match optimum with None -> "none" | Some score -> string_of_int score) in
  show_pruning "exhaustive" all_pruning;
  show_pruning "POR" por_pruning;
  assert (let _, _, _, optimum = all_pruning in optimum = Some 5);
  assert (let _, _, _, optimum = por_pruning in optimum = Some 5);
  let incumbent = ref None in
  let bounded_stats = N.empty_prefix_search_stats () in
  let bounded = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~stats:bounded_stats
    ~on_prefix:(fun _ terminal schedule ->
      if terminal then
        let score = variable_uses schedule in
        incumbent := Some (match !incumbent with
          | None -> score | Some old -> min old score))
    ~should_prune_prefix:(fun _ schedule ->
      match !incumbent with
      | None -> false
      | Some score -> score < direct_variable_use_bound
          direct_footprints schedule)
    variables hypotheses [] rec_call N.D_Gen in
  assert (!incumbent = Some 5);
  assert (bounded_stats.visited_nodes = 71);
  assert (bounded_stats.completed_prefixes = 16);
  assert (List.length bounded = 16);
  Printf.printf "actual variable-only bounded search: nodes=%d leaves=%d\n"
    bounded_stats.visited_nodes bounded_stats.completed_prefixes;
  let leaf_uses observations =
    List.filter_map (fun (_, terminal, score) ->
      if terminal then Some score else None) observations
    |> List.sort_uniq compare in
  Printf.printf "completed variable-use values: exhaustive=%s POR=%s\n"
    (String.concat "," (List.map string_of_int
      (leaf_uses !complete_observations)))
    (String.concat "," (List.map string_of_int
      (leaf_uses !reduced_observations)));
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
  let owner_graph_orders =
    List.map (canonical_order_for_key direct_footprints)
      (unique_owners complete) in
  let owner_graph_candidates = List.filter (fun schedule ->
    List.mem (source_order schedule) owner_graph_orders) complete in
  assert (quotient_signatures complete =
          quotient_signatures owner_graph_candidates);
  let canonical_candidates =
    List.filter (fun schedule ->
      List.mem (source_order schedule) canonical_orders) complete in
  let maximal_simple schedule =
    let modes, unconstrained = mode_signature schedule in
    let rec check bound = function
      | [] -> true
      | name :: rest ->
        let expected = List.filter (fun var -> not (List.mem var bound))
          (match name with
           | "A" -> ["x"] | "B" -> ["y"] | "C" -> ["x"; "z"]
           | "D" -> ["x"; "y"] | "E" -> ["y"; "z"]
           | _ -> []) |> List.sort compare in
        let actual = List.assoc name modes in
        expected = actual && check (actual @ bound) rest in
    unconstrained = [] && check [] (source_order schedule) in
  let maximal_candidates = List.filter maximal_simple complete in
  let maximal_reduced = List.filter maximal_simple reduced in
  let maximal_search = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~reduce_orderings:false ~maximal_outputs:true
    variables hypotheses [] rec_call N.D_Gen in
  let maximal_stats = N.empty_prefix_search_stats () in
  let maximal_por = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~maximal_outputs:true ~stats:maximal_stats
    variables hypotheses [] rec_call N.D_Gen in
  assert (maximal_search = maximal_candidates);
  assert (maximal_por = maximal_reduced);
  Printf.printf "maximal direct-variable candidates=%d classes=%d\n"
    (List.length maximal_candidates)
    (List.length (unique_owners maximal_candidates));
  assert (List.length maximal_candidates = 120);
  assert (List.length maximal_reduced = 16);
  assert (List.length (unique_owners maximal_candidates) = 16);
  let check_conservative_model prefer_dense ds =
  List.iter (fun policy ->
    let observations = ref [] in
    let oracle = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~reduce_orderings:false ~maximal_outputs:true
      ~on_prefix:(fun path terminal schedule ->
        observations := (path, terminal, schedule) :: !observations)
      variables hypotheses [] rec_call ds in
    let leaves = List.filter (fun (_, terminal, _) -> terminal)
      !observations in
    List.iter (fun (path, terminal, schedule) ->
      if not terminal then begin
        let bound = model_features ~prefer_dense ~terminal:false
          ~footprints:direct_footprints schedule in
        List.iter (fun (leaf_path, _, completed) ->
          if is_path_prefix path leaf_path then
            let actual = model_features ~prefer_dense ~terminal:true
              ~footprints:direct_footprints completed in
            assert (not (Ranking.can_prune ~prefer_dense policy
              ~incumbent:actual ~bound))) leaves
      end) !observations;
    let incumbent = ref None in
    let stats = N.empty_prefix_search_stats () in
    let bounded = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 ~maximal_outputs:true ~stats
      ~on_prefix:(fun _ terminal schedule ->
        if terminal then begin
          let score = model_features ~prefer_dense ~terminal:true
            ~footprints:direct_footprints schedule in
          incumbent := Some (match !incumbent with
            | None -> score
            | Some old when Ranking.compare ~prefer_dense policy score old < 0 -> score
            | Some old -> old)
        end)
      ~should_prune_prefix:(fun _ schedule ->
        match !incumbent with
        | None -> false
        | Some best -> Ranking.can_prune ~prefer_dense policy
            ~incumbent:best
            ~bound:(model_features ~prefer_dense ~terminal:false
              ~footprints:direct_footprints schedule))
      variables hypotheses [] rec_call ds in
    let optimum = best_features ~prefer_dense
      ~footprints:direct_footprints policy oracle in
    let matches_optimum schedule =
      let score = model_features ~prefer_dense ~terminal:true
        ~footprints:direct_footprints schedule in
      not (Ranking.can_prune ~prefer_dense policy ~incumbent:score ~bound:optimum)
      && not (Ranking.can_prune ~prefer_dense policy ~incumbent:optimum ~bound:score) in
    assert (match !incumbent with Some _ -> true | None -> false);
    assert (List.sort_uniq compare
      (List.map mode_signature (List.filter matches_optimum
        (if prefer_dense then maximal_reduced else oracle))) =
      List.sort_uniq compare
      (List.map mode_signature (List.filter matches_optimum bounded)));
    Printf.printf "conservative typed bound %s %s: oracle=%d bounded=%d nodes=%d\n"
      (if prefer_dense then "generator" else "checker")
      (Ranking.to_string policy) (List.length oracle)
      (List.length bounded)
      stats.visited_nodes) [
      Ranking.RankDensityThenVars;
      Ranking.RankDensityCountsThenVars;
      Ranking.RankDensityOnly;
      Ranking.RankVarsThenDensity;
      Ranking.RankVarsOnly] in
  check_conservative_model true N.D_Gen;
  check_conservative_model false N.D_Check;
  (* Give each typed relation mode a fixed synthetic recursive-call grade.
     The proof in test/pruning_bounds.v then predicts that the committed
     density/count/use key is no worse than every completed descendant. *)
  let counted_key schedule =
    let modes, unconstrained = mode_signature schedule in
    assert (unconstrained = []);
    let grades = List.map (fun (name, outputs) ->
      if outputs = [] then 0
      else if name = "D" then 3
      else 4) modes in
    let worst = List.fold_left min 4 grades in
    let c, b, n, p, t = Ranking.histogram_of_ranks grades in
    [4 - worst; c; b; n; p; t; variable_uses schedule] in
  let counted_observations = ref [] in
  ignore (N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~reduce_orderings:false ~maximal_outputs:true
    ~on_prefix:(fun path terminal schedule ->
      counted_observations :=
        (path, terminal, counted_key schedule) :: !counted_observations)
    variables hypotheses [] rec_call N.D_Gen);
  let counted_leaves = List.filter (fun (_, terminal, _) -> terminal)
    !counted_observations in
  let counted_nodes = ref 0 in
  List.iter (fun (path, terminal, bound) ->
    if not terminal then begin
      incr counted_nodes;
      let descendants = List.filter (fun (leaf_path, _, _) ->
        is_path_prefix path leaf_path) counted_leaves in
      assert (descendants <> []);
      List.iter (fun (_, _, completed) ->
        assert (Stdlib.compare bound completed <= 0)) descendants
    end) !counted_observations;
  Printf.printf "typed counted-density bounds: nodes=%d leaves=%d\n"
    !counted_nodes (List.length counted_leaves);
  Printf.printf "distinct orders=%d, candidates/class min=%d max=%d, orders/class min=%d max=%d\n"
    (List.length (distinct_orders complete))
    (List.fold_left min max_int class_sizes)
    (List.fold_left max 0 class_sizes)
    (List.fold_left min max_int order_class_sizes)
    (List.fold_left max 0 order_class_sizes);
  Printf.printf "canonical-order candidates=%d\n"
    (List.length canonical_candidates);
  Printf.printf "maximal-output candidates=%d exhaustive, %d POR\n"
    (List.length maximal_candidates) (List.length maximal_reduced);
  Printf.printf "maximal-output POR work: nodes=%d leaves=%d modes=%d\n"
    maximal_stats.visited_nodes maximal_stats.completed_prefixes
    maximal_stats.processed_mode_choices;
  (* Model the checker's max-aggregated density cost with mode-dependent
     dependency scores. D is costly only when asked to produce. This
     checks the bound against real typed search descendants, without claiming
     that these synthetic dependency costs are plugin memo results. *)
  let mode_cost name outputs =
    if name = "D" then
      (match List.length outputs with 0 -> 0 | 1 -> 2 | _ -> 3)
    else 0 in
  let density_cost schedule =
    let modes, _ = mode_signature schedule in
    List.fold_left (fun worst (name, outputs) ->
      max worst (mode_cost name outputs)) 0 modes in
  let density_observations = ref [] in
  let observed_maximal = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~maximal_outputs:true ~reduce_orderings:false
    ~on_prefix:(fun path terminal schedule ->
      density_observations :=
        (path, terminal, density_cost schedule) :: !density_observations)
    variables hypotheses [] rec_call N.D_Check in
  assert (List.length observed_maximal = List.length maximal_search);
  ignore (check_prefix_use_bounds !density_observations);
  let exact_optimum = List.fold_left (fun best schedule ->
    min best (density_cost schedule)) max_int observed_maximal in
  let density_incumbent = ref None in
  let density_stats = N.empty_prefix_search_stats () in
  let density_bounded = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~maximal_outputs:true ~stats:density_stats
    ~on_prefix:(fun _ terminal schedule ->
      if terminal then
        let cost = density_cost schedule in
        density_incumbent := Some (match !density_incumbent with
          | None -> cost | Some old -> min old cost))
    ~should_prune_prefix:(fun _ schedule ->
      match !density_incumbent with
      | None -> false
      | Some best -> best < density_cost schedule)
    variables hypotheses [] rec_call N.D_Check in
  assert (!density_incumbent = Some exact_optimum);
  assert (density_stats.visited_nodes < maximal_stats.visited_nodes);
  assert (density_stats.completed_prefixes < maximal_stats.completed_prefixes);
  let optimal_modes schedules =
    List.filter (fun schedule -> density_cost schedule = exact_optimum) schedules
    |> List.map mode_signature |> List.sort_uniq compare in
  assert (optimal_modes maximal_por = optimal_modes density_bounded);
  Printf.printf "maximal-output checker density model: optimum=%d bounded nodes=%d leaves=%d cuts=%d\n"
    exact_optimum density_stats.visited_nodes density_stats.completed_prefixes
    (List.length maximal_por - List.length density_bounded);
  (* Counting positive checks distinguishes schedules whose worst generator
     density is already Checking. Every remaining producer must bind at least
     one distinct variable, so at most the number of unbound variables can
     avoid becoming a check. This fixture has only plain positive relations. *)
  let check_observations = ref [] in
  let counted_exhaustive = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~maximal_outputs:true ~reduce_orderings:false
    ~on_prefix:(fun path terminal schedule ->
      check_observations :=
        (path, terminal,
         if terminal then positive_checks schedule
         else check_count_bound direct_footprints schedule) :: !check_observations)
    variables hypotheses [] rec_call N.D_Gen in
  assert (counted_exhaustive = maximal_search);
  ignore (check_prefix_use_bounds !check_observations);
  let best_checks = List.fold_left (fun best schedule ->
    min best (positive_checks schedule)) max_int counted_exhaustive in
  let check_incumbent = ref None in
  let check_stats = N.empty_prefix_search_stats () in
  let check_bounded = N.possible_schedules_with_advanced_pruning
    ~max_schedules:100000 ~maximal_outputs:true ~stats:check_stats
    ~on_prefix:(fun _ terminal schedule ->
      if terminal then
        let checks = positive_checks schedule in
        check_incumbent := Some (match !check_incumbent with
          | None -> checks | Some old -> min old checks))
    ~should_prune_prefix:(fun _ schedule ->
      match !check_incumbent with
      | None -> false
      | Some best -> best < check_count_bound direct_footprints schedule)
    variables hypotheses [] rec_call N.D_Gen in
  assert (!check_incumbent = Some best_checks);
  assert (best_checks = 2);
  assert (List.map mode_signature
    (List.filter (fun schedule -> positive_checks schedule = best_checks)
      maximal_por) |> List.sort_uniq compare =
    (List.map mode_signature check_bounded |> List.sort_uniq compare));
  Printf.printf "maximal-output check-count bound: optimum=%d nodes=%d leaves=%d\n"
    best_checks check_stats.visited_nodes check_stats.completed_prefixes;
  Printf.printf "sleep-set candidates=%d, distinct orders=%d\n"
    (List.length reduced)
    (List.length (distinct_orders reduced));
  Printf.printf "typed five-hypothesis schedule retained (%d candidates, %d owner maps; legacy %d)\n"
    (List.length complete) (List.length (unique_owners complete))
    (List.length (unique_owners legacy));
  let fixed_prefixes = ref [] in
  let fixed_checks = N.possible_schedules_with_advanced_pruning
      ~reduce_orderings:false
      ~on_prefix:(fun path terminal schedule ->
        fixed_prefixes := (path, terminal, schedule) :: !fixed_prefixes)
      [v "x", nat] [relation "F" ["x"]; relation "G" ["x"]]
      [v "x"] rec_call N.D_Check in
  check_converted_prefixes !fixed_prefixes;
  let orders = List.map source_order fixed_checks |> List.sort_uniq compare in
  assert (orders = [["F"; "G"]; ["G"; "F"]]);
  let fixed_maximal = N.possible_schedules_with_advanced_pruning
      ~reduce_orderings:false ~maximal_outputs:true
      [v "x", nat] [relation "F" ["x"]; relation "G" ["x"]]
      [v "x"] rec_call N.D_Check in
  assert (List.map source_order fixed_maximal |> List.sort_uniq compare = orders);
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
  let typed_prefixes = ref [] in
  let typed_dependency = N.possible_schedules_with_advanced_pruning
      ~on_prefix:(fun path terminal schedule ->
        typed_prefixes := (path, terminal, schedule) :: !typed_prefixes)
      [v "x", x_type; v "y", nat]
      [relation "H" ["x"]; relation "J" ["y"]]
      [] rec_call N.D_Gen in
  check_converted_prefixes !typed_prefixes;
  let typed_orders = List.map source_order typed_dependency
    |> List.sort_uniq compare in
  assert (typed_orders = [["H"; "J"]; ["J"; "H"]]);
  let typed_dependency_maximal = N.possible_schedules_with_advanced_pruning
      ~maximal_outputs:true
      [v "x", x_type; v "y", nat]
      [relation "H" ["x"]; relation "J" ["y"]]
      [] rec_call N.D_Gen in
  assert (List.map source_order typed_dependency_maximal
    |> List.sort_uniq compare = typed_orders);
  let nested = N.DTyCtr (N.ty_ctr_of_string "K", [
    N.DCtr (N.constructor_of_string "Wrap", [N.DTyVar (v "x")])]) in
  let nested_prefixes = ref [] in
  let nonplain = N.possible_schedules_with_advanced_pruning
      ~on_prefix:(fun path terminal schedule ->
        nested_prefixes := (path, terminal, schedule) :: !nested_prefixes)
      [v "x", nat; v "y", nat]
      [nested; relation "J" ["y"]] [] rec_call N.D_Gen in
  check_converted_prefixes !nested_prefixes;
  assert (List.length (List.map source_order nonplain
    |> List.sort_uniq compare) = 2);
  let negative_prefixes = ref [] in
  let negative = N.possible_schedules_with_advanced_pruning
      ~on_prefix:(fun path terminal schedule ->
        negative_prefixes := (path, terminal, schedule) :: !negative_prefixes)
      [v "x", nat]
      [N.DNot (relation "NotH" ["x"]); relation "PosH" ["x"]]
      [v "x"] rec_call N.D_Check in
  check_converted_prefixes !negative_prefixes;
  assert (negative <> []);
  let double_nested = N.DTyCtr (N.ty_ctr_of_string "K2", [
    N.DCtr (N.constructor_of_string "Wrap", [N.DTyVar (v "x")]);
    N.DCtr (N.constructor_of_string "Wrap", [N.DTyVar (v "y")])]) in
  let double_prefixes = ref [] in
  let double_schedules = N.possible_schedules_with_advanced_pruning
      ~on_prefix:(fun path terminal schedule ->
        double_prefixes := (path, terminal, schedule) :: !double_prefixes)
      [v "x", nat; v "y", nat]
      [double_nested] [] rec_call N.D_Gen in
  check_converted_prefixes !double_prefixes;
  assert (double_schedules <> []);
  assert (List.exists (fun schedule ->
    List.length (List.filter (function N.S_Match _ -> true | _ -> false)
      schedule) = 2) double_schedules);
  let nested_floors = ref [] in
  ignore (N.possible_schedules_with_advanced_pruning
    ~reduce_orderings:false
    ~on_prefix_with_floor:(fun path terminal floor stable ->
      nested_floors := (path, terminal, floor, stable) :: !nested_floors)
    [v "x", nat; v "y", nat]
    [relation "Bind" ["x"; "y"]; double_nested]
    [] rec_call N.D_Gen);
  let nested_leaves = List.filter_map (fun (path, terminal, _, stable) ->
    if terminal then Some (path, positive_checks stable) else None)
    !nested_floors in
  assert (List.exists (fun (_, terminal, floor, _) ->
    not terminal && floor > 0) !nested_floors);
  List.iter (fun (path, terminal, floor, stable) ->
    if not terminal then List.iter (fun (leaf_path, checks) ->
      if is_path_prefix path leaf_path then
        assert (positive_checks stable + floor <= checks)) nested_leaves)
    !nested_floors;
  test_unifier_prefix_boundary nat;
  test_small_footprints nat rec_call;
  Printf.printf "converted prefix pairs=%d alpha-renamed=%d\n"
    !converted_prefix_pairs !alpha_only_prefix_pairs;
  assert (!alpha_only_prefix_pairs > 0)

(* Self-recursive steps keep only inputs; the full request interleaves the
   step's outputs back at the derivation's output positions. *)
let () =
  let rel = N.ty_ctr_of_string "R" in
  let var x = N.DTyVar (v x) in
  let nat = N.DTyCtr (N.ty_ctr_of_string "nat", []) in
  let producer = N.S_ST ([v "o1", nat; v "o2", nat],
    N.SrcRec (v "rec", [var "a"; var "b"]), N.PS_G) in
  assert (N.recursive_request (rel, [1; 3]) producer =
          Some (N.DTyCtr (rel, [var "a"; var "o1"; var "b"; var "o2"])));
  assert (N.recursive_request (rel, [0]) producer = None);
  let checker = N.S_Check (N.SrcRec (v "rec", [var "a"; var "b"]), true) in
  assert (N.recursive_request (rel, []) checker =
          Some (N.DTyCtr (rel, [var "a"; var "b"])));
  let other = N.S_ST ([v "o1", nat], N.SrcNonrec (N.DTyCtr (rel, [var "o1"])), N.PS_G) in
  assert (N.recursive_request (rel, [0]) other = None)
