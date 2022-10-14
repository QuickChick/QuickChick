val gGen : GenericLib.coq_expr -> GenericLib.coq_expr
val returnGen : GenericLib.coq_expr -> GenericLib.coq_expr
val bindGen :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val bindGenOpt :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr

val gEnum : GenericLib.coq_expr -> GenericLib.coq_expr
val returnEnum : GenericLib.coq_expr -> GenericLib.coq_expr  
val bindEnum : 
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val bindEnumOpt :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val failEnum : GenericLib.coq_expr -> GenericLib.coq_expr

val enumChecker :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) ->
  GenericLib.coq_expr -> GenericLib.coq_expr
val enumCheckerOpt :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) ->
  GenericLib.coq_expr -> GenericLib.coq_expr
  
val oneof : GenericLib.coq_expr list -> GenericLib.coq_expr
val oneofT : GenericLib.coq_expr list -> GenericLib.coq_expr  
val frequency :
  (GenericLib.coq_expr * GenericLib.coq_expr) list -> GenericLib.coq_expr
val frequencyT :
  (GenericLib.coq_expr * GenericLib.coq_expr) list -> GenericLib.coq_expr
val backtracking :
  (GenericLib.coq_expr * GenericLib.coq_expr) list -> GenericLib.coq_expr
val enumerating :
  (GenericLib.coq_expr) list -> GenericLib.coq_expr
val uniform_backtracking : GenericLib.coq_expr list -> GenericLib.coq_expr
val checker_backtracking : GenericLib.coq_expr list -> GenericLib.coq_expr
module TyCtrMap : CMap.ExtS with type key = GenericLib.Ord_ty_ctr.t and module Set := Set.Make(GenericLib.Ord_ty_ctr)
module CtrMap : CMap.ExtS with type key = GenericLib.Ord_ctr.t and module Set := Set.Make(GenericLib.Ord_ctr)
