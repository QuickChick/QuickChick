(*
  Benchmark for advanced schedule pruning in newGenericLib
  
  Based on the Lean benchmark structure - tests exact hypothesis dependencies
  and measures schedule quality with/without pruning.
*)

module NGL = Quickchick_plugin.NewGenericLib

(* Test helper *)
let var_of_string s = Names.Id.of_string s

(* Hypothesis structure matching Lean: (name, var_deps, info) *)
type hypothesis = {
  name: string;
  var_deps: string list list;
}

(* Schedule quality scoring - matching pre_schedule_score *)
type schedule_score = {
  checks: int;      (* Number of check steps *)
  length: int;      (* Total length: checks + produces + unconstrained vars *)
  unconstrained: int; (* Number of unconstrained variable generations *)
}

let score_to_int score =
  (* Lexicographic comparison: checks first, then length, then unconstrained *)
  score.checks * 1000000 + score.length * 1000 + score.unconstrained

let score_schedule (schedule : NGL.schedule_step list) : schedule_score =
  List.fold_left (fun acc step ->
    match step with
    | NGL.S_Check (_, _) -> 
      { acc with checks = acc.checks + 1; length = acc.length + 1 }
    | NGL.S_ST (_, _, _) -> 
      { acc with length = acc.length + 1 }
    | NGL.S_UC (_, _, _) -> 
      { acc with unconstrained = acc.unconstrained + 1; length = acc.length + 1 }
    | NGL.S_Match (_, _) -> 
      { acc with length = acc.length + 1 }
    | NGL.S_Let (_, _) -> 
      { acc with length = acc.length + 1 }
  ) { checks = 0; length = 0; unconstrained = 0 } schedule

let score_list (schedules : NGL.schedule_step list list) : schedule_score list =
  List.map score_schedule schedules

let find_min_score (scores : schedule_score list) : schedule_score option =
  match scores with
  | [] -> None
  | s :: rest ->
    Some (List.fold_left (fun best s ->
      if score_to_int s < score_to_int best then s else best
    ) s rest)

let avg_score (scores : schedule_score list) : float =
  if List.length scores = 0 then 0.0
  else
    let total = List.fold_left (fun sum s -> sum + score_to_int s) 0 scores in
    float_of_int total /. float_of_int (List.length scores)

(* Moderately complex benchmark hypotheses with varied patterns *)
(* let bench_hyps : hypothesis list =
  [
    (* Simple single dependencies *)
    { name = "H1"; var_deps = [["a"]] };
    { name = "H2"; var_deps = [["b"]] };
    
    (* Chain: a -> c -> d *)
    { name = "H3"; var_deps = [["a"]; ["c"]] };
    { name = "H4"; var_deps = [["c"]; ["d"]] };
    
    (* Convergence: a,b -> e *)
    { name = "H5"; var_deps = [["a"; "e"]] };
    { name = "H6"; var_deps = [["b"; "e"]] };
    
    (* Divergence: d -> f,g *)
    { name = "H7"; var_deps = [["d"]; ["f"]] };
    { name = "H8"; var_deps = [["d"]; ["g"]] };
  ]

let bench_vars = ["a"; "b"; "c"; "d"; "e"; "f"; "g"] *)

let bench_hyps =
  [
    {name = "typing"; var_deps = [["G"];["e"];["t"]]};
    {name = "step"; var_deps = [["e"];["e'"]]}
  ]

let bench_vars = ["G";"e";"t";"e'"]

(* Turn a list of variable names into a rocq_constr argument *)
let rocq_arg_of_strings (vars : string list) : NGL.rocq_constr =
  match vars with
  | [] -> NGL.DHole
  | [v] -> NGL.DTyVar (var_of_string v)
  | vs ->
      let rc_vars = List.map (fun v -> NGL.DTyVar (var_of_string v)) vs in
      NGL.DCtr (NGL.constructor_of_string "C", rc_vars)

(* Convert our hypothesis record into a rocq_type *)
let hypothesis_to_rocq (h : hypothesis) : NGL.rocq_type =
  let args = List.map rocq_arg_of_strings h.var_deps in
  NGL.DTyCtr (NGL.ty_ctr_of_string h.name, args)

(* Main test *)
let () =
  NGL.debug_mode := true;  (* Enable debug output *)
  Printf.printf "\n=== Schedule Quality Analysis ===\n\n";
  Printf.printf "Hypotheses:\n";
  List.iter (fun h ->
    let vars = String.concat ", " (List.flatten h.var_deps) in
    Printf.printf "  %s: [%s]\n" h.name vars
  ) bench_hyps;
  Printf.printf "\nVariables: %s\n\n" (String.concat ", " bench_vars);
  
  (* Generate schedules *)
  let type_params = [] in

  (* Create hypothesis types from the string-based definitions *)
  let hypotheses = List.map hypothesis_to_rocq bench_hyps in
  let rec_call = (NGL.ty_ctr_of_string "L", [0]) in
  
  (* Create variables with nat type *)
  let nat_type = NGL.DTyCtr (NGL.ty_ctr_of_string "nat", []) in
  let variables = List.map (fun var_name ->
    (var_of_string var_name, nat_type)
  ) bench_vars in
  
  (* Advanced pruning schedules *)
  let advanced_schedules =
    NGL.possible_schedules_with_advanced_pruning variables hypotheses [] rec_call NGL.D_Gen
  in
  
  Printf.printf "Advanced Pruning Schedules (%d):\n" (List.length advanced_schedules);
  (if List.length advanced_schedules = 0 then
    Printf.printf "  (No schedules generated - algorithm too restrictive)\n"
  else (
    List.iteri (fun i sched ->
      if i < 5 then (  (* Only print first 5 *)
        Printf.printf "  Schedule %d:\n" (i+1);
        List.iter (fun step ->
          Printf.printf "    %s\n" (NGL.schedule_step_to_string step)
        ) sched
      )
    ) advanced_schedules;
    if List.length advanced_schedules > 5 then
      Printf.printf "  ... (%d more schedules)\n" (List.length advanced_schedules - 5)
  ));
  Printf.printf "\n";
  
  let advanced_scores = score_list advanced_schedules in
  let advanced_best = find_min_score advanced_scores in
  let advanced_avg = avg_score advanced_scores in
  

  Printf.printf "Advanced - Count: %d, Best Score: {checks=%d, length=%d, unconstrained=%d}, Avg Score: %.1f\n\n"
    (List.length advanced_schedules)
    (match advanced_best with Some s -> s.checks | None -> 0)
    (match advanced_best with Some s -> s.length | None -> 0)
    (match advanced_best with Some s -> s.unconstrained | None -> 0)
    advanced_avg;
  
  
  Printf.printf "  Advanced: %d schedules\n" (List.length advanced_schedules);