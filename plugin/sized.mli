val sizeM : RocqExpr.coq_expr
val succ_zero : RocqExpr.coq_expr -> RocqExpr.coq_expr
val base_ctrs :
  RocqExpr.ty_ctr ->
  ('a * RocqExpr.coq_type) list -> ('a * RocqExpr.coq_type) list
val sized_decl :
  (RocqExpr.ty_ctr * RocqExpr.ty_param list * RocqExpr.ctr_rep list) list ->
  (RocqExpr.ty_ctr -> RocqExpr.var list -> RocqExpr.coq_expr) * ((RocqExpr.var * RocqExpr.arg list * RocqExpr.var * RocqExpr.coq_expr * RocqExpr.coq_expr) list)
val gen_args :
  RocqExpr.coq_type ->
  RocqExpr.ty_ctr -> int -> string list * string list
val dropIH :
  RocqExpr.coq_type -> RocqExpr.ty_ctr -> 'a list -> 'a list * 'a list
val zeroEqProof :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.coq_type) list ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.var list -> RocqExpr.coq_expr
val succEqProof :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.coq_type) list ->
  RocqExpr.coq_expr ->
  (RocqExpr.var -> RocqExpr.coq_expr) ->
  RocqExpr.coq_expr -> RocqExpr.var list -> RocqExpr.coq_expr
val sizeEqType :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.coq_type) list ->
  RocqExpr.coq_expr -> RocqExpr.var list -> RocqExpr.coq_expr
