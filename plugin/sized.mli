val sizeM : CoqExpr.coq_expr
val succ_zero : CoqExpr.coq_expr -> CoqExpr.coq_expr
val base_ctrs :
  CoqExpr.ty_ctr ->
  ('a * CoqExpr.coq_type) list -> ('a * CoqExpr.coq_type) list
val sized_decl :
  (CoqExpr.ty_ctr * CoqExpr.ty_param list * CoqExpr.ctr_rep list) list ->
  (CoqExpr.ty_ctr -> CoqExpr.var list -> CoqExpr.coq_expr) * ((CoqExpr.var * CoqExpr.arg list * CoqExpr.var * CoqExpr.coq_expr * CoqExpr.coq_expr) list)
val gen_args :
  CoqExpr.coq_type ->
  CoqExpr.ty_ctr -> int -> string list * string list
val dropIH :
  CoqExpr.coq_type -> CoqExpr.ty_ctr -> 'a list -> 'a list * 'a list
val zeroEqProof :
  CoqExpr.ty_ctr ->
  (CoqExpr.constructor * CoqExpr.coq_type) list ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.var list -> CoqExpr.coq_expr
val succEqProof :
  CoqExpr.ty_ctr ->
  (CoqExpr.constructor * CoqExpr.coq_type) list ->
  CoqExpr.coq_expr ->
  (CoqExpr.var -> CoqExpr.coq_expr) ->
  CoqExpr.coq_expr -> CoqExpr.var list -> CoqExpr.coq_expr
val sizeEqType :
  CoqExpr.ty_ctr ->
  (CoqExpr.constructor * CoqExpr.coq_type) list ->
  CoqExpr.coq_expr -> CoqExpr.var list -> CoqExpr.coq_expr
