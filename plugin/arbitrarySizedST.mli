val fail_exp : GenericLib.coq_expr -> GenericLib.coq_expr
val not_enough_fuel_exp : GenericLib.coq_expr -> GenericLib.coq_expr
val ret_exp :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val ret_type : GenericLib.var -> 'a -> GenericLib.coq_expr
val instantiate_existential_method : GenericLib.coq_expr
val instantiate_existential_methodST :
  int -> GenericLib.coq_expr -> GenericLib.coq_expr
val rec_method :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  int ->
  UnifyQC.unknown list option ->
  GenericLib.coq_expr list -> GenericLib.coq_expr
val bind :
  bool ->
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val stMaybe :
  bool ->
  GenericLib.coq_expr ->
  string ->
  ((GenericLib.coq_expr -> GenericLib.coq_expr) * int) list ->
  GenericLib.coq_expr
val ret_type_dec :
  GenericLib.var ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val check_expr :
  int ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val match_inp :
  GenericLib.var ->
  GenericLib.matcher_pat ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
type generator_kind = Base_gen | Ind_gen
val construct_generators :
  generator_kind ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.ty_ctr ->
  GenericLib.dep_type ->
  GenericLib.dep_ctr list ->
  GenericLib.coq_expr ->
  UnifyQC.range list ->
  UnifyQC.range UnifyQC.UM.t ->
  GenericLib.dep_type UnifyQC.UM.t ->
  UnifyQC.Unknown.t -> GenericLib.coq_expr list                               
val base_gens :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.ty_ctr ->
  GenericLib.dep_type ->
  GenericLib.dep_ctr list ->
  GenericLib.coq_expr ->
  UnifyQC.range list ->
  UnifyQC.range UnifyQC.UM.t ->
  GenericLib.dep_type UnifyQC.UM.t ->
  UnifyQC.Unknown.t -> GenericLib.coq_expr list
val ind_gens :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.ty_ctr ->
  GenericLib.dep_type ->
  GenericLib.dep_ctr list ->
  GenericLib.coq_expr ->
  UnifyQC.range list ->
  UnifyQC.range UnifyQC.UM.t ->
  GenericLib.dep_type UnifyQC.UM.t ->
  UnifyQC.Unknown.t -> GenericLib.coq_expr list  
val arbitrarySizedST :
  GenericLib.ty_ctr ->
  GenericLib.ty_param list ->
  GenericLib.dep_ctr list ->
  GenericLib.dep_type ->
  GenericLib.var list ->
  UnifyQC.range list ->
  UnifyQC.range UnifyQC.UM.t ->
  GenericLib.dep_type UnifyQC.UM.t ->
  GenericLib.arg list ->
  UnifyQC.Unknown.t -> GenericLib.coq_expr -> GenericLib.coq_expr
