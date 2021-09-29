val sizeM : GenericLib.coq_expr
val succ_zero : GenericLib.coq_expr -> GenericLib.coq_expr
val base_ctrs :
  GenericLib.ty_ctr ->
  ('a * GenericLib.coq_type) list -> ('a * GenericLib.coq_type) list
val sized_decl :
  GenericLib.ty_ctr ->
  (GenericLib.constructor * GenericLib.coq_type) list -> GenericLib.coq_expr
val gen_args :
  GenericLib.coq_type ->
  GenericLib.ty_ctr -> int -> string list * string list
val dropIH :
  GenericLib.coq_type -> GenericLib.ty_ctr -> 'a list -> 'a list * 'a list
val zeroEqProof :
  GenericLib.ty_ctr ->
  (GenericLib.constructor * GenericLib.coq_type) list ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.var list -> GenericLib.coq_expr
val succEqProof :
  GenericLib.ty_ctr ->
  (GenericLib.constructor * GenericLib.coq_type) list ->
  GenericLib.coq_expr ->
  (GenericLib.var -> GenericLib.coq_expr) ->
  GenericLib.coq_expr -> GenericLib.var list -> GenericLib.coq_expr
val sizeEqType :
  GenericLib.ty_ctr ->
  (GenericLib.constructor * GenericLib.coq_type) list ->
  GenericLib.coq_expr -> GenericLib.var list -> GenericLib.coq_expr
