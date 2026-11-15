val shrink_decl :
  (RocqExpr.ty_ctr * RocqExpr.ty_param list * RocqExpr.ctr_rep list) list ->
  (RocqExpr.ty_ctr -> RocqExpr.var list -> RocqExpr.rocq_expr) * ((RocqExpr.var * RocqExpr.arg list * RocqExpr.var * RocqExpr.rocq_expr * RocqExpr.rocq_expr) list)
val show_decl :
  (RocqExpr.ty_ctr * RocqExpr.ty_param list * RocqExpr.ctr_rep list) list ->
  (RocqExpr.ty_ctr -> RocqExpr.var list -> RocqExpr.rocq_expr) * ((RocqExpr.var * RocqExpr.arg list * RocqExpr.var * RocqExpr.rocq_expr * RocqExpr.rocq_expr) list)

val fuzzy_decl : RocqExpr.ty_ctr -> RocqExpr.ctr_rep list -> RocqExpr.var list -> RocqExpr.rocq_expr
val mutate_decl : RocqExpr.ty_ctr -> RocqExpr.ctr_rep list -> RocqExpr.var list -> RocqExpr.rocq_expr
