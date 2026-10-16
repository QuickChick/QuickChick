open Quickchick_plugin.ScheduleRanking

let policies = [RankDensityThenVars; RankDensityOnly; RankVarsThenDensity; RankVarsOnly]

(* Independent lexicographic model of the public ranking contract. *)
let key prefer_dense policy f =
  let density = if prefer_dense then -f.density_rank else f.density_rank in
  match policy with
  | RankDensityThenVars -> density, f.variable_uses, f.candidate_id
  | RankDensityOnly -> density, 0, f.candidate_id
  | RankVarsThenDensity -> f.variable_uses, density, f.candidate_id
  | RankVarsOnly -> f.variable_uses, 0, f.candidate_id

let () =
  let fixtures = List.concat_map (fun density_rank ->
    List.concat_map (fun variable_uses ->
      List.init 3 (fun candidate_id -> {density_rank; variable_uses; candidate_id}))
      [0;1;2;3]) [0;1;2;3;4] in
  List.iter (fun policy ->
    assert (of_string (to_string policy) = policy);
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
  List.iter (fun (name, expected) -> assert (of_string name = expected))
    ["density-first", RankDensityThenVars; "density-only", RankDensityOnly;
     "var_density", RankVarsThenDensity; "vars_density", RankVarsThenDensity;
     "vars-first", RankVarsThenDensity; "var_only", RankVarsOnly;
     "vars-only", RankVarsOnly; "unknown", RankDensityThenVars]
