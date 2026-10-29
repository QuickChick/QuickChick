val shrink_decl :
  (CoqExpr.ty_ctr * CoqExpr.ty_param list * CoqExpr.ctr_rep list) list ->
  (CoqExpr.ty_ctr -> CoqExpr.var list -> CoqExpr.coq_expr) * ((CoqExpr.var * CoqExpr.arg list * CoqExpr.var * CoqExpr.coq_expr * CoqExpr.coq_expr) list)
val show_decl :
  (CoqExpr.ty_ctr * CoqExpr.ty_param list * CoqExpr.ctr_rep list) list ->
  (CoqExpr.ty_ctr -> CoqExpr.var list -> CoqExpr.coq_expr) * ((CoqExpr.var * CoqExpr.arg list * CoqExpr.var * CoqExpr.coq_expr * CoqExpr.coq_expr) list)

val fuzzy_decl : CoqExpr.ty_ctr -> CoqExpr.ctr_rep list -> CoqExpr.var list -> CoqExpr.coq_expr
val mutate_decl : CoqExpr.ty_ctr -> CoqExpr.ctr_rep list -> CoqExpr.var list -> CoqExpr.coq_expr
