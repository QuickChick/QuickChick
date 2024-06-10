val arbitrarySized_decl :
  (GenericLib.ty_ctr * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * (GenericLib.var * GenericLib.coq_expr) list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
val shrink_decl :
  (GenericLib.ty_ctr * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * (GenericLib.var * GenericLib.coq_expr) list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
val show_decl :
  (GenericLib.ty_ctr * GenericLib.ctr_rep list) list ->
  (GenericLib.ty_ctr -> GenericLib.var list -> GenericLib.coq_expr) * ((GenericLib.var * (GenericLib.var * GenericLib.coq_expr) list * GenericLib.var * GenericLib.coq_expr * GenericLib.coq_expr) list)
