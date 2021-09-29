type size_inputs = {
  _ty_ctr : GenericLib.ty_ctr;
  _ctrs : GenericLib.ctr_rep list;
  _coqTyCtr : GenericLib.coq_expr;
  _coqTyParams : GenericLib.coq_expr list;
  _full_dt : GenericLib.coq_expr;
  _isCurrentTyCtr : GenericLib.coq_type -> bool;
}
val gen_list :
  size_inputs ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.constructor * GenericLib.coq_type -> GenericLib.coq_expr
val fst_leq_proof : 'a list -> GenericLib.coq_expr
