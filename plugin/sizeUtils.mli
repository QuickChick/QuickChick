type size_inputs = {
  _ty_ctr : RocqExpr.ty_ctr;
  _ctrs : RocqExpr.ctr_rep list;
  _rocqTyCtr : RocqExpr.rocq_expr;
  _rocqTyParams : RocqExpr.rocq_expr list;
  _full_dt : RocqExpr.rocq_expr;
  _isCurrentTyCtr : RocqExpr.rocq_type -> bool;
}
val gen_list :
  size_inputs ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.constructor * RocqExpr.rocq_type -> RocqExpr.rocq_expr
val fst_leq_proof : 'a list -> RocqExpr.rocq_expr
