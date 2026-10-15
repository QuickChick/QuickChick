(** Shared dispatcher for QCDerive and the opt-in legacy spelling. *)
val dispatch : Constrexpr.constr_expr -> Constrexpr.constr_expr -> string -> string -> unit
