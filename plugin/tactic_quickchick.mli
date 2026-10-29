(** Compile scheduled instances without retaining temporary declarations. *)
val compile_public : mode:string -> outputs:int list -> constrained:bool ->
  all_mutual:bool -> Constrexpr.constr_expr ->
  Evd.evar_map * (Names.Id.t * EConstr.t) list
