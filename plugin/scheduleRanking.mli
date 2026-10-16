(** Comparison of complete schedules. Search pruning needs a separate bound. *)
type policy =
  | RankDensityThenVars
  | RankDensityOnly
  | RankVarsThenDensity
  | RankVarsOnly

type features = { density_rank : int; variable_uses : int; candidate_id : int }

(** Includes the existing environment aliases; unknown names select the default. *)
val of_string : string -> policy

val current : unit -> policy
val to_string : policy -> string

(** Smaller results rank first; candidate id breaks all feature ties. *)
val compare : prefer_dense:bool -> policy -> features -> features -> int
