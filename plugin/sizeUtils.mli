type size_inputs = {
  _ty_ctr : RocqExpr.ty_ctr;
  _ctrs : RocqExpr.ctr_rep list;
  _coqTyCtr : RocqExpr.coq_expr;
  _coqTyParams : RocqExpr.coq_expr list;
  _full_dt : RocqExpr.coq_expr;
  _isCurrentTyCtr : RocqExpr.coq_type -> bool;
}
val gen_list :
  size_inputs ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.constructor * RocqExpr.coq_type -> RocqExpr.coq_expr
val fst_leq_proof : 'a list -> RocqExpr.coq_expr
