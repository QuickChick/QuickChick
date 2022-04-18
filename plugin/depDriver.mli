type derivable =
  DecOpt
| DecOptMon
| ArbitrarySizedSuchThat
| EnumSizedSuchThat
| GenSizedSuchThatMonotonicOpt
| GenSizedSuchThatSizeMonotonicOpt
| GenSizedSuchThatCorrect
val derivable_to_string : derivable -> string
val mk_instance_name : derivable -> string -> string
val derive_dependent :
  derivable ->
  Constrexpr.constr_expr ->
  UnifyQC.range UnifyQC.UM.t ->
  GenericLib.dep_type UnifyQC.UM.t ->
  GenericLib.var list ->
  UnifyQC.range list ->
  GenericLib.ty_ctr * GenericLib.ty_param list * GenericLib.dep_ctr list *
  GenericLib.dep_type ->
  GenericLib.var list option -> UnifyQC.unknown -> unit
val create_t_and_u_maps :
  GenericLib.dep_type option UnifyQC.UM.t ->
  GenericLib.dep_type ->
  (Constrexpr.constr_expr_r CAst.t * 'a) list ->
  UnifyQC.range UnifyQC.UM.t * GenericLib.dep_type UnifyQC.UM.t
val dep_dispatch : Constrexpr.constr_expr_r CAst.t -> derivable -> unit
