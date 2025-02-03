val arbitrarySized_decl :
  (GenericLib.ty_ctr * GenericLib.ty_param list * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * GenericLib.arg list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
val shrink_decl :
  (GenericLib.ty_ctr * GenericLib.ty_param list * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * GenericLib.arg list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
val show_decl :
  (GenericLib.ty_ctr * GenericLib.ty_param list * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * GenericLib.arg list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
