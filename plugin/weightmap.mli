module CtrMap : Map.S with type key = GenericLib.Ord_ctr.t
type weight_ast = WNum of int | WSize
val weight_ast_to_string : weight_ast -> string
val weight_env : weight_ast CtrMap.t ref
val weight_env_to_string : unit -> string
val register_weights : (GenericLib.constructor * weight_ast) list -> unit
val convert_constr_to_weight : Constrexpr.constr_expr_r CAst.t -> weight_ast
val convert_constr_to_cw_pair :
  Constrexpr.constr_expr_r CAst.t -> GenericLib.constructor * weight_ast
val register_weights_object :
  (GenericLib.constructor * weight_ast) list -> Libobject.obj
val lookup_weight : CtrMap.key -> GenericLib.var -> GenericLib.coq_expr
