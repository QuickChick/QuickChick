module CtrMap : Map.S with type key = RocqExpr.Ord_ctr.t
type weight_ast = WNum of int | WSize
val weight_ast_to_string : weight_ast -> string
val weight_env_to_string : unit -> string
val register_weights : (RocqExpr.constructor * weight_ast) list -> unit
val convert_constr_to_weight : Constrexpr.constr_expr_r CAst.t -> weight_ast
val convert_constr_to_cw_pair :
  Constrexpr.constr_expr_r CAst.t -> RocqExpr.constructor * weight_ast
val register_weights_object :
  (RocqExpr.constructor * weight_ast) list -> Libobject.obj
val lookup_weight : bool -> CtrMap.key -> RocqExpr.var -> RocqExpr.coq_expr

(* The weight registered for the constructor of this name, if any. *)
val find_weight : string -> weight_ast option
