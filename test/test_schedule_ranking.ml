open Quickchick_plugin.ScheduleRanking

let policies =
  [RankDensityThenVars; RankDensityCountsThenVars; RankDensityOnly;
   RankVarsThenDensity; RankVarsOnly]

(* Independent lexicographic model of the completed-schedule ranking. *)
let key prefer_dense policy f =
  let density = if prefer_dense then -f.density_rank else f.density_rank in
  let c, b, n, p, t = f.density_counts in
  let counts = if prefer_dense then [c;b;n;p;t] else [t;p;n;b;c] in
  match policy with
  | RankDensityThenVars -> [density; f.variable_uses; f.candidate_id]
  | RankDensityCountsThenVars -> [density] @ counts @ [f.variable_uses; f.candidate_id]
  | RankDensityOnly -> [density; f.candidate_id]
  | RankVarsThenDensity -> [f.variable_uses; density; f.candidate_id]
  | RankVarsOnly -> [f.variable_uses; f.candidate_id]

let () =
  assert (histogram_of_ranks [0;0;3;4;3] = (2,0,0,2,1));
  assert (histogram_to_string (histogram_of_ranks [0;0;3;4;3]) = "2,0,0,2,1");
  assert (try ignore (histogram_of_ranks [5]); false with Invalid_argument _ -> true);
  let histograms =
    List.map histogram_of_ranks
      [[]; [0]; [0;3]; [0;3;3]; [0;0;3]; [0;0;3;4];
       [4]; [4;3]; [4;3;3]; [4;4;3]] in
  let fixtures = List.concat_map (fun density_rank ->
    List.concat_map (fun density_counts ->
      List.concat_map (fun variable_uses ->
        List.init 3 (fun candidate_id ->
          {density_rank; density_counts; variable_uses; candidate_id}))
        [0;1;2;3]) histograms) [0;1;2;3;4] in
  List.iter (fun policy ->
    assert (scorer_of_name (to_string policy) = Some (Feature policy));
    List.iter (fun prefer_dense ->
      List.iter (fun a -> List.iter (fun b ->
        let actual = compare ~prefer_dense policy a b in
        let expected = Stdlib.compare (key prefer_dense policy a) (key prefer_dense policy b) in
        assert (Int.compare actual 0 = Int.compare expected 0)) fixtures) fixtures;
      let unique = List.mapi (fun candidate_id f -> {f with candidate_id}) fixtures in
      let ordered = List.sort (compare ~prefer_dense policy) (List.rev unique) in
      assert (ordered = List.sort (compare ~prefer_dense policy) unique);
      assert (ordered = List.sort (fun a b -> Stdlib.compare
        (key prefer_dense policy a) (key prefer_dense policy b)) unique)) [true;false]) policies;
  List.iter (fun (name, expected) ->
      assert (scorer_of_name name = Some (Feature expected)))
    ["density-first", RankDensityThenVars;
     "density-counts-then-vars", RankDensityCountsThenVars;
     "density-only", RankDensityOnly;
     "var_density", RankVarsThenDensity; "vars_density", RankVarsThenDensity;
     "vars-first", RankVarsThenDensity; "var_only", RankVarsOnly;
     "vars-only", RankVarsOnly; "density", RankDensityThenVars];
  (* An unknown name is not a scorer; the command reports it. *)
  assert (scorer_of_name "unknown" = None);
  assert (scorer_of_name "budget_aware" = Some BudgetAware);
  assert (scorer_of_name "cardinality" = Some Cardinality);
  assert (List.for_all (fun name -> scorer_of_name name <> None) (scorer_names ()));
  let grades = [0;1;2;3;4] in
  let possibilities = [None; Some 0; Some 1; Some 2; Some 3; Some 4] in
  List.iter (fun policy -> List.iter (fun prefer_dense ->
    List.iter (fun first -> List.iter (fun second ->
      let prefix = [first; second] in
      let bound = prefix_bound ~prefer_dense ~known_grades:prefix
        ~variable_uses:2 in
      let resolutions = function
        | Some grade -> [grade]
        | None -> grades in
      List.iter (fun a -> List.iter (fun b ->
        List.iter (fun suffix ->
          let completed_grades = [a;b;suffix] in
          let completed =
            { density_rank = List.fold_left
                (if prefer_dense then min else max)
                (if prefer_dense then 4 else 0) completed_grades;
              density_counts = histogram_of_ranks completed_grades;
              variable_uses = 2 + suffix mod 3;
              candidate_id = 17 } in
          assert (not (can_prune ~prefer_dense policy
            ~incumbent:completed ~bound));
          assert (can_prune ~prefer_dense policy
            ~incumbent:bound ~bound:completed =
            (Stdlib.compare
               (key prefer_dense policy bound)
               (key prefer_dense policy {completed with candidate_id = 0}) < 0))) grades)
        (resolutions second)) (resolutions first)) possibilities)
      possibilities) [true;false]) policies;
  let equal = prefix_bound ~prefer_dense:true
    ~known_grades:[None] ~variable_uses:0 in
  assert (not (can_prune ~prefer_dense:true RankDensityCountsThenVars
    ~incumbent:{equal with candidate_id = -1} ~bound:equal))

(* Group combinations: compare against brute force over every combination,
   using the independent [key] model on complete features. Each complete
   schedule also carries shared steps scored as one more fixed group. *)
let () =
  let state = ref 12345 in
  let next bound =
    state := (!state * 1103515245 + 12345) land 0x3fffffff;
    !state mod bound in
  let random_group () =
    let ranks = List.init (next 3) (fun _ -> next 5) in
    { group_density = 0; group_counts = histogram_of_ranks ranks;
      group_uses = next 4 }, ranks in
  let with_density prefer_dense (g, ranks) =
    { g with group_density = List.fold_left
        (if prefer_dense then min else max)
        (if prefer_dense then 4 else 0) ranks } in
  let complete prefer_dense parts =
    let ranks = List.concat_map snd parts in
    { density_rank = List.fold_left (if prefer_dense then min else max)
        (if prefer_dense then 4 else 0) ranks;
      density_counts = histogram_of_ranks ranks;
      variable_uses = List.fold_left (fun n (g, _) -> n + g.group_uses) 0 parts;
      candidate_id = 0 } in
  let rec product = function
    | [] -> [[]]
    | xs :: rest -> List.concat_map (fun x ->
        List.map (fun tail -> x :: tail) (product rest)) xs in
  let checked = ref 0 in
  for _ = 1 to 4000 do
    let groups = List.init (1 + next 3) (fun _ ->
      List.init (1 + next 4) (fun _ ->
        if next 6 = 0 then None else Some (random_group ()))) in
    let shared = random_group () in
    List.iter (fun policy -> List.iter (fun prefer_dense ->
      let parts = List.map (List.map (Option.map (fun g ->
        with_density prefer_dense g, snd g))) groups in
      let shared = with_density prefer_dense shared, snd shared in
      let feature_lists = List.map (List.map (Option.map fst)) parts in
      let chosen = select_group_combinations ~prefer_dense policy feature_lists in
      let usable = List.map (fun group ->
        List.mapi (fun i x -> i, x) group
        |> List.filter_map (fun (i, x) -> Option.map (fun x -> i, x) x)) parts in
      let score choice =
        key prefer_dense policy (complete prefer_dense
          (shared :: List.map2 (fun group i -> List.assoc i group) usable choice)) in
      let all = product (List.map (List.map fst) usable) in
      (match all with
       | [] -> assert (chosen = [])
       | _ ->
         let best = List.fold_left (fun b c -> min b (score c)) (score (List.hd all)) all in
         assert (chosen <> []);
         assert (List.length chosen <= 5);
         assert (List.for_all (fun c -> List.mem c all) chosen);
         assert (List.exists (fun c -> score c = best) chosen));
      incr checked) [true; false]) policies
  done;
  Printf.printf "group combinations: %d brute-force comparisons\n" !checked
