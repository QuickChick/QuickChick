(* Ranking complete schedules is separate from candidate generation. This module
   does not justify, or supply bounds for, the structural pruning in search. *)
type policy =
  | RankDensityThenVars
  | RankDensityCountsThenVars
  | RankDensityOnly
  | RankVarsThenDensity
  | RankVarsOnly

(* Counts are for the selected schedule's annotated call sites, in ascending
   grade order. A recursive dependency contributes one grade at its call site;
   its internal steps are not expanded into the caller's histogram. *)
type density_histogram = int * int * int * int * int

type features = {
  density_rank : int;
  density_counts : density_histogram;
  variable_uses : int;
  candidate_id : int;
}

let empty_histogram = (0, 0, 0, 0, 0)

let histogram_of_ranks ranks =
  List.fold_left (fun (checking, backtracking, neutral, partial, total) -> function
    | 0 -> (checking + 1, backtracking, neutral, partial, total)
    | 1 -> (checking, backtracking + 1, neutral, partial, total)
    | 2 -> (checking, backtracking, neutral + 1, partial, total)
    | 3 -> (checking, backtracking, neutral, partial + 1, total)
    | 4 -> (checking, backtracking, neutral, partial, total + 1)
    | _ -> invalid_arg "ScheduleRanking.histogram_of_ranks: grade outside 0..4")
    empty_histogram ranks

let histogram_to_string (c, b, n, p, t) =
  Printf.sprintf "%d,%d,%d,%d,%d" c b n p t

let compare_histogram ~prefer_dense (c, b, n, p, t) (c', b', n', p', t') =
  if prefer_dense then Stdlib.compare (c, b, n, p, t) (c', b', n', p', t')
  else Stdlib.compare (t, p, n, b, c) (t', p', n', b', c')

let of_string = function
  | "density_then_vars" | "density-vars" | "density-first" -> RankDensityThenVars
  | "density_counts_then_vars" | "density-counts-then-vars" -> RankDensityCountsThenVars
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
  | RankDensityCountsThenVars -> "density_counts_then_vars"
  | RankDensityOnly -> "density_only"
  | RankVarsThenDensity -> "vars_then_density"
  | RankVarsOnly -> "vars_only"

(* These built-in feature policies ignore the order of independent steps:
   density is an extremum of step densities, and variable uses count inputs
   bound before each step. The typed scheduler only commutes plain relation
   steps whose unbound footprints, including variable-type dependencies, are
   disjoint. A future policy observing step order must return false here unless
   it supplies its own commutation law. Candidate IDs are assigned after POR. *)
let preserves_independent_swaps = function
  | RankDensityThenVars | RankDensityCountsThenVars | RankDensityOnly
  | RankVarsThenDensity | RankVarsOnly ->
    (match Sys.getenv_opt "QC_SCHEDULE_POR" with
     | Some ("0" | "false" | "no") -> false
     | _ -> true)

let compare_without_id ~prefer_dense policy a b =
  let density () =
    if prefer_dense then Stdlib.compare b.density_rank a.density_rank
    else Stdlib.compare a.density_rank b.density_rank in
  let variables () = Stdlib.compare a.variable_uses b.variable_uses in
  let counts () = compare_histogram ~prefer_dense a.density_counts b.density_counts in
  let then_compare first second = if first = 0 then second () else first in
  let result = match policy with
    | RankDensityThenVars -> then_compare (density ()) variables
    | RankDensityCountsThenVars ->
      then_compare (density ()) (fun () -> then_compare (counts ()) variables)
    | RankDensityOnly -> density ()
    | RankVarsThenDensity -> then_compare (variables ()) density
    | RankVarsOnly -> variables () in
  result

let compare ~prefer_dense policy a b =
  let result = compare_without_id ~prefer_dense policy a b in
  if result = 0 then Stdlib.compare a.candidate_id b.candidate_id else result

(* None is a call whose grade has not been certified. Give it the best rank
   for this derivation direction and no histogram count. Committed variable
   uses are already incurred; future steps can only add to them. *)
let prefix_bound ~prefer_dense ~known_grades ~variable_uses =
  let floor = if prefer_dense then 4 else 0 in
  let grades = List.filter_map Fun.id known_grades in
  let density_rank = List.fold_left
    (if prefer_dense then min else max) floor grades in
  { density_rank;
    density_counts = histogram_of_ranks grades;
    variable_uses;
    candidate_id = 0 }

(* Strict comparison preserves equal-score candidates and their ID tie order. *)
let can_prune ~prefer_dense policy ~incumbent ~bound =
  compare_without_id ~prefer_dense policy incumbent bound < 0

(* Independent hypothesis groups contribute separable features: the density
   rank combines by min (dense) or max, while histograms and variable uses
   add. Histograms and uses form a translation-invariant lexicographic order,
   so only the density extremum can absorb one group's advantage. *)
type group_features = {
  group_density : int;
  group_counts : density_histogram;
  group_uses : int;
}

let group_features_of (f : features) =
  { group_density = f.density_rank; group_counts = f.density_counts;
    group_uses = f.variable_uses }

let add_histogram (c, b, n, p, t) (c', b', n', p', t') =
  (c + c', b + b', n + n', p + p', t + t')

let density_identity ~prefer_dense = if prefer_dense then 4 else 0

let combine_density ~prefer_dense = if prefer_dense then min else max

(* Order on the additive fields that the policy compares after density.
   Vars-first policies compare uses first, so their order is total. *)
let compare_additive ~prefer_dense policy a b =
  match policy with
  | RankDensityThenVars -> Stdlib.compare a.group_uses b.group_uses
  | RankDensityCountsThenVars ->
    let c = compare_histogram ~prefer_dense a.group_counts b.group_counts in
    if c <> 0 then c else Stdlib.compare a.group_uses b.group_uses
  | RankDensityOnly -> 0
  | RankVarsThenDensity | RankVarsOnly -> Stdlib.compare a.group_uses b.group_uses

let density_first = function
  | RankDensityThenVars | RankDensityCountsThenVars | RankDensityOnly -> true
  | RankVarsThenDensity | RankVarsOnly -> false

let compare_density ~prefer_dense a b =
  if prefer_dense then Stdlib.compare b a else Stdlib.compare a b

(* [dominates a b]: for every context, combining with [a] scores no worse
   than combining with [b]. *)
let dominates ~prefer_dense policy a b =
  let density = compare_density ~prefer_dense a.group_density b.group_density in
  let additive = compare_additive ~prefer_dense policy a b in
  match policy with
  | RankDensityThenVars | RankDensityCountsThenVars | RankDensityOnly ->
    density <= 0 && additive <= 0
  | RankVarsThenDensity -> additive < 0 || (additive = 0 && density <= 0)
  | RankVarsOnly -> additive <= 0

(* Keep, per group, one candidate (the lowest index) for each feature vector
   not strictly dominated by another. Combinations are formed by a dynamic
   program over the combined density, keeping the best additive sum per
   density value. The result has at most one combination per reachable
   density, each listing one candidate index per group. Scores among these
   still need the caller's complete ranking, which includes shared steps. *)
let select_group_combinations ~prefer_dense policy
    (groups : group_features option list list) : int list list =
  let pareto candidates =
    let indexed = List.filteri (fun _ (_, f) -> f <> None)
      (List.mapi (fun i f -> i, f) candidates)
      |> List.map (fun (i, f) -> i, Option.get f) in
    let distinct = List.fold_left (fun kept (i, f) ->
      if List.exists (fun (_, g) -> g = f) kept then kept else kept @ [i, f])
      [] indexed in
    List.filter (fun (_, f) ->
      not (List.exists (fun (_, g) ->
        g <> f && dominates ~prefer_dense policy g f
        && not (dominates ~prefer_dense policy f g)) distinct)) distinct in
  let fronts = List.map pareto groups in
  if List.exists (fun front -> front = []) fronts then [] else
  let zero = { group_density = density_identity ~prefer_dense;
               group_counts = empty_histogram; group_uses = 0 } in
  let combine a b =
    { group_density = combine_density ~prefer_dense a.group_density b.group_density;
      group_counts = add_histogram a.group_counts b.group_counts;
      group_uses = a.group_uses + b.group_uses } in
  let key f = if density_first policy then f.group_density else 0 in
  let better (f, choice) (g, other) =
    let c = if density_first policy then compare_additive ~prefer_dense policy f g
      else
        let a = compare_additive ~prefer_dense policy f g in
        if a <> 0 then a else compare_density ~prefer_dense f.group_density g.group_density in
    c < 0 || (c = 0 && Stdlib.compare choice other < 0) in
  let states = List.fold_left (fun states front ->
    List.fold_left (fun next (f, choice) ->
      List.fold_left (fun next (i, g) ->
        let candidate = (combine f g, choice @ [i]) in
        let k = key (fst candidate) in
        match List.assoc_opt k next with
        | Some current when not (better candidate current) -> next
        | _ -> (k, candidate) :: List.remove_assoc k next) next front)
      [] states |> List.map snd) [zero, []] fronts in
  List.map snd states |> List.sort_uniq Stdlib.compare
