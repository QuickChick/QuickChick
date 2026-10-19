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
