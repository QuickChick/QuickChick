val sizeM : RocqExpr.rocq_expr
val succ_zero : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val base_ctrs :
  RocqExpr.ty_ctr ->
  ('a * RocqExpr.rocq_type) list -> ('a * RocqExpr.rocq_type) list
val sized_decl :
  (RocqExpr.ty_ctr * RocqExpr.ty_param list * RocqExpr.ctr_rep list) list ->
  (RocqExpr.ty_ctr -> RocqExpr.var list -> RocqExpr.rocq_expr) * ((RocqExpr.var * RocqExpr.arg list * RocqExpr.var * RocqExpr.rocq_expr * RocqExpr.rocq_expr) list)
val gen_args :
  RocqExpr.rocq_type ->
  RocqExpr.ty_ctr -> int -> string list * string list
val dropIH :
  RocqExpr.rocq_type -> RocqExpr.ty_ctr -> 'a list -> 'a list * 'a list
val zeroEqProof :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.rocq_type) list ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.var list -> RocqExpr.rocq_expr
val succEqProof :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.rocq_type) list ->
  RocqExpr.rocq_expr ->
  (RocqExpr.var -> RocqExpr.rocq_expr) ->
  RocqExpr.rocq_expr -> RocqExpr.var list -> RocqExpr.rocq_expr
val sizeEqType :
  RocqExpr.ty_ctr ->
  (RocqExpr.constructor * RocqExpr.rocq_type) list ->
  RocqExpr.rocq_expr -> RocqExpr.var list -> RocqExpr.rocq_expr
