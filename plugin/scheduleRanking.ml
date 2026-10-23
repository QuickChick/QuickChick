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

let compare_density ~prefer_dense a b =
  if prefer_dense then Stdlib.compare b a else Stdlib.compare a b

(* Each built-in ranking as a grouped policy: density is extremal, while
   histograms and variable uses add. *)
let group_policy ~prefer_dense policy : group_features GroupedScore.policy =
  let open GroupedScore in
  let density = Extremal, (fun a b ->
    compare_density ~prefer_dense a.group_density b.group_density) in
  let counts = Additive, (fun a b ->
    compare_histogram ~prefer_dense a.group_counts b.group_counts) in
  let uses = Additive, (fun a b -> Stdlib.compare a.group_uses b.group_uses) in
  { unit = { group_density = density_identity ~prefer_dense;
             group_counts = empty_histogram; group_uses = 0 };
    combine = (fun a b ->
      { group_density = (if prefer_dense then min else max) a.group_density b.group_density;
        group_counts = add_histogram a.group_counts b.group_counts;
        group_uses = a.group_uses + b.group_uses });
    fields = match policy with
      | RankDensityThenVars -> [density; uses]
      | RankDensityCountsThenVars -> [density; counts; uses]
      | RankDensityOnly -> [density]
      | RankVarsThenDensity -> [uses; density]
      | RankVarsOnly -> [uses] }

let dominates ~prefer_dense policy =
  GroupedScore.dominates (group_policy ~prefer_dense policy)

let select_group_combinations ~prefer_dense policy groups =
  GroupedScore.select_combinations (group_policy ~prefer_dense policy) groups
