(* Ranking complete schedules is separate from candidate generation. This module
   does not justify, or supply bounds for, the structural pruning in search. *)
type policy =
  | RankDensityThenVars
  | RankDensityOnly
  | RankVarsThenDensity
  | RankVarsOnly

type features = { density_rank : int; variable_uses : int; candidate_id : int }

let of_string = function
  | "density_then_vars" | "density-vars" | "density-first" -> RankDensityThenVars
  | "density_only" | "density-only" -> RankDensityOnly
  | "var_density" | "vars_density" | "vars_then_density" | "vars-density" | "vars-first" -> RankVarsThenDensity
  | "var_only" | "vars_only" | "vars-only" -> RankVarsOnly
  | _ -> RankDensityThenVars

let current () =
  match Sys.getenv_opt "QC_SCHEDULE_RANKING" with
  | Some name -> of_string name
  | None -> RankDensityThenVars

let to_string = function
  | RankDensityThenVars -> "density_then_vars"
  | RankDensityOnly -> "density_only"
  | RankVarsThenDensity -> "vars_then_density"
  | RankVarsOnly -> "vars_only"

(* The four built-in feature policies ignore the order of independent steps:
   density is an extremum of step densities, and variable uses count inputs
   bound before each step. The typed scheduler only commutes plain relation
   steps whose unbound footprints, including variable-type dependencies, are
   disjoint. A future policy observing step order must return false here unless
   it supplies its own commutation law. Candidate IDs are assigned after POR. *)
let preserves_independent_swaps = function
  | RankDensityThenVars | RankDensityOnly
  | RankVarsThenDensity | RankVarsOnly ->
    (match Sys.getenv_opt "QC_SCHEDULE_POR" with
     | Some ("0" | "false" | "no") -> false
     | _ -> true)

let compare ~prefer_dense policy a b =
  let density () =
    if prefer_dense then Stdlib.compare b.density_rank a.density_rank
    else Stdlib.compare a.density_rank b.density_rank in
  let variables () = Stdlib.compare a.variable_uses b.variable_uses in
  let then_compare first second = if first = 0 then second () else first in
  let result = match policy with
    | RankDensityThenVars -> then_compare (density ()) variables
    | RankDensityOnly -> density ()
    | RankVarsThenDensity -> then_compare (variables ()) density
    | RankVarsOnly -> variables () in
  then_compare result (fun () -> Stdlib.compare a.candidate_id b.candidate_id)
