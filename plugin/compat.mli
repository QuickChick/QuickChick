open Constrexpr
val unCNotation11 : constr_expr_r CAst.t -> (unit -> constr_expr) -> (constr_expr * constr_expr list) option

module MonoConstr : sig
  val mkConst : Names.Constant.t -> Constr.t
  val mkInd : Names.inductive -> Constr.t
  val mkConstruct : Names.constructor -> Constr.t
end
