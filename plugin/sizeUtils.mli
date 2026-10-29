type size_inputs = {
  _ty_ctr : CoqExpr.ty_ctr;
  _ctrs : CoqExpr.ctr_rep list;
  _coqTyCtr : CoqExpr.coq_expr;
  _coqTyParams : CoqExpr.coq_expr list;
  _full_dt : CoqExpr.coq_expr;
  _isCurrentTyCtr : CoqExpr.coq_type -> bool;
}
val gen_list :
  size_inputs ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.constructor * CoqExpr.coq_type -> CoqExpr.coq_expr
val fst_leq_proof : 'a list -> CoqExpr.coq_expr
