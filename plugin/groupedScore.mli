(** Combining scores of independent hypothesis groups.

    A policy ranks complete schedules lexicographically by [fields], most
    significant first. Its scorer must be separable: a schedule built from
    footprint-disjoint groups and shared steps scores as the [combine] of
    their separate scores, in any order. Each field must combine fieldwise:
    - [Additive]: combining both sides with the same score preserves the
      field's strict order and its ties (for example, sums).
    - [Extremal]: combining preserves non-strict order only (max or min). *)

type kind = Additive | Extremal

type 's policy = {
  unit : 's;
  combine : 's -> 's -> 's;
  fields : (kind * ('s -> 's -> int)) list;
}

val compare : 's policy -> 's -> 's -> int

(** Under the laws above, [dominates p a b] implies that [combine a c] ranks
    no worse than [combine b c] for every [c]. *)
val dominates : 's policy -> 's -> 's -> bool

(** For per-group candidate scores ([None] marks an unusable candidate),
    return index combinations, one index per group, including one that
    achieves the best complete score. One combination is returned per class
    of equal extremal fields. Returns [] when a group has no usable candidate. *)
val select_combinations : 's policy -> 's option list list -> int list list

(** Check the combination and field laws on sample scores. Passing is
    evidence for those samples, not a proof. *)
val check_laws : 's policy -> 's list -> (unit, string) result
