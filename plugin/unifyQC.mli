type name_provider = { next_name : unit -> string; }
val mk_name_provider : string -> name_provider
module Unknown :
  sig
    type t = GenericLib.var
    val to_string : GenericLib.var -> string
    val from_string : string -> GenericLib.var
    val from_var : 'a -> 'a
    val from_id : Names.Id.t -> GenericLib.var
    val undefined : GenericLib.var
  end
module UnknownOrd :
  sig
    type t = Unknown.t
    val compare : GenericLib.var -> GenericLib.var -> int
  end
type unknown = Unknown.t
type range =
    Ctr of GenericLib.constructor * range list
  | Unknown of unknown
  | Undef of GenericLib.dep_type
  | FixedInput
  | Parameter of GenericLib.ty_param
  | RangeHole
val is_parameter : range -> bool
val range_to_string : range -> string
module UM : CMap.ExtS with type key = Unknown.t and module Set := Set.Make(UnknownOrd)
type umap = range UM.t
val umfind : UM.key -> 'a UM.t -> 'a
val lookup : unknown -> umap -> range option
module OrdTSS :
  sig type t = unknown * unknown val compare : 'a -> 'a -> int end
module EqSet : Set.S with type elt = OrdTSS.t
val eq_set_add : unknown -> unknown -> EqSet.t -> EqSet.t
module OrdTyp :
  sig type t = GenericLib.dep_type val compare : 'a -> 'a -> int end
module ArbSet : Set.S with type elt = OrdTyp.t
type unknown_provider = { next_unknown : unit -> Unknown.t; }
val unk_provider : unknown_provider
val raiseMatch :
  umap ->
  GenericLib.constructor ->
  range list -> EqSet.t -> (umap * GenericLib.matcher_pat * EqSet.t) option
val unify :
  umap ->
  range ->
  range ->
  EqSet.t ->
  (umap * range * EqSet.t * (unknown * GenericLib.matcher_pat) list) option
val fixRange : UM.key -> range -> range UM.t -> range UM.t
val fixVariable : UM.key -> range UM.t -> range UM.t
val convert_to_range : GenericLib.dep_type -> range option
val is_fixed : range UM.t -> GenericLib.dep_type -> bool option
val range_to_coq_expr : range UM.t -> range -> GenericLib.coq_expr
val dt_to_coq_expr :
  range UM.t -> GenericLib.dep_type -> GenericLib.coq_expr
val is_dep_type : GenericLib.dep_type -> bool
type check = (GenericLib.coq_expr -> GenericLib.coq_expr) * int
module CMap : CMap.ExtS with type key = GenericLib.OrdDepType.t and module Set := Set.Make(GenericLib.OrdDepType)

type cmap = check list CMap.t
val lookup_checks : CMap.key -> 'a CMap.t -> 'a option
val handle_equalities :
  GenericLib.coq_expr ->
  EqSet.t ->
  (GenericLib.coq_expr -> 'a -> 'a -> 'a -> 'a) -> 'a -> 'a -> 'a -> 'a
type mode =
    Recursive of (Unknown.t * GenericLib.dep_type) list *
      (Unknown.t * GenericLib.dep_type) list * range list
  | NonRecursive of (Unknown.t * GenericLib.dep_type) list
val mode_analysis :
  GenericLib.ty_ctr ->
  GenericLib.ty_ctr ->
  range list -> range UM.t -> range list -> range UM.t -> mode
val isTyParam : GenericLib.dep_type -> bool
val warn_uninstantiated_variables : ?loc:Loc.t -> GenericLib.var list -> unit
val handle_branch :
  string list ->
  GenericLib.dep_type ->
  GenericLib.coq_expr ->
  'b ->
  'b ->
  (GenericLib.coq_expr -> 'b) ->
  'a ->
  (int -> GenericLib.coq_expr -> 'a) ->
  (bool -> 'a -> string -> (GenericLib.var -> 'b) -> 'b) ->
  (int -> unknown list option -> GenericLib.coq_expr list -> 'a) ->
  (bool -> 'a -> string -> (GenericLib.var -> 'b) -> 'b) ->
  (bool ->
   'a ->
   string -> ((GenericLib.coq_expr -> GenericLib.coq_expr) * int) list -> 'a) ->
  (int -> GenericLib.coq_expr -> 'b -> 'b -> 'b -> 'b) ->
  (GenericLib.var -> GenericLib.matcher_pat -> 'b -> 'b -> 'b) ->
  (string -> GenericLib.coq_expr -> (GenericLib.var -> 'b) -> 'b) ->
  (GenericLib.var -> GenericLib.var list -> 'b -> 'b) ->
  GenericLib.ty_ctr ->
  range UM.t ->
  GenericLib.dep_type UM.t ->
  range list -> Unknown.t -> GenericLib.dep_ctr -> 'b * bool

