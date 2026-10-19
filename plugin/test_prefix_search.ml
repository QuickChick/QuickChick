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
  let complete = N.possible_schedules_with_advanced_pruning
      ~max_schedules:100000 variables hypotheses [] rec_call N.D_Gen in
  let wanted = ["B"; "E"; "C"; "A"; "D"] in
  let legacy = N.possible_schedules_with_legacy_pruning
      ~max_schedules:100000 variables hypotheses [] rec_call N.D_Gen in
  assert (List.exists (fun schedule -> source_order schedule = wanted) complete);
  assert (not (List.exists (fun schedule -> source_order schedule = wanted) legacy));
  let unique_owners schedules =
    List.map (fun schedule -> owner_key (source_order schedule)) schedules
    |> List.sort_uniq compare in
  assert (List.length (unique_owners complete) = 16);
  assert (List.length (unique_owners legacy) < 16);
  Printf.printf "typed five-hypothesis schedule retained (%d candidates, %d owner maps; legacy %d)\n"
    (List.length complete) (List.length (unique_owners complete))
    (List.length (unique_owners legacy));
  let fixed_checks = N.possible_schedules_with_advanced_pruning
      [v "x", nat] [relation "F" ["x"]; relation "G" ["x"]]
      [v "x"] rec_call N.D_Check in
  let orders = List.map source_order fixed_checks |> List.sort_uniq compare in
  assert (orders = [["F"; "G"]; ["G"; "F"]])
