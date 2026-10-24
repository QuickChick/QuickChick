(** Comparison of complete schedules. Search pruning needs a separate bound. *)
type policy =
  | RankDensityThenVars
  | RankDensityCountsThenVars
  | RankDensityOnly
  | RankVarsThenDensity
  | RankVarsOnly

type density_histogram = int * int * int * int * int

type features = {
  density_rank : int;
  density_counts : density_histogram;
  variable_uses : int;
  candidate_id : int;
}

(** Count completed step annotations once per call site. Grades are numbered
    Checking=0 through Total=4; recursive callees are not expanded. *)
val histogram_of_ranks : int list -> density_histogram
val histogram_to_string : density_histogram -> string

(** Includes the existing environment aliases; unknown names select the default. *)
val of_string : string -> policy

val current : unit -> policy
val to_string : policy -> string

(** Whether independent typed steps preserve the policy's score features.
    Candidate-ID tie-breaking is applied to retained representatives. *)
val preserves_independent_swaps : policy -> bool

(** Smaller results rank first; candidate id breaks all feature ties. *)
val compare : prefer_dense:bool -> policy -> features -> features -> int

(** Conservative append-only bound. [None] is an unresolved call: it takes
    the best density rank and contributes no histogram count. The use count
    includes only uses already incurred by committed steps. *)
val prefix_bound : prefer_dense:bool -> known_grades:int option list ->
  variable_uses:int -> features

(** Prune only when a completed incumbent is strictly better than the bound;
    candidate IDs are deliberately excluded from this comparison. *)
val can_prune : prefer_dense:bool -> policy -> incumbent:features ->
  bound:features -> bool

(** Prune when the incumbent is at least as good as the bound. Exact when
    candidate IDs follow search order and the node is explored after the
    incumbent was found, so the incumbent also wins every tie. *)
val can_prune_after : prefer_dense:bool -> policy -> incumbent:features ->
  bound:features -> bool

(** Features of one independent hypothesis group, scored on its own. *)
type group_features = {
  group_density : int;
  group_counts : density_histogram;
  group_uses : int;
}

val group_features_of : features -> group_features

(** The ranking as a grouped policy over separately scored groups. *)
val group_policy : prefer_dense:bool -> policy -> group_features GroupedScore.policy

(** [dominates a b]: combining with [a] is never worse than with [b], under
    every context of other groups and shared steps. *)
val dominates : prefer_dense:bool -> policy -> group_features ->
  group_features -> bool

(** For per-group candidate features ([None] marks an unusable candidate),
    return candidate index combinations, one index per group, that include a
    combination achieving the best complete score. At most one combination
    is returned per combined density value. Ties between equal-scoring
    combinations are broken by the lowest indices, not global candidate ids. *)
val select_group_combinations : prefer_dense:bool -> policy ->
  group_features option list list -> int list list
