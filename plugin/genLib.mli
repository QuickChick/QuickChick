val gGen : CoqExpr.coq_expr -> CoqExpr.coq_expr
val returnGen : CoqExpr.coq_expr -> CoqExpr.coq_expr
val bindGen :
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val bindGenOpt :
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr

val gEnum : CoqExpr.coq_expr -> CoqExpr.coq_expr
val returnEnum : CoqExpr.coq_expr -> CoqExpr.coq_expr  
val bindEnum : 
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val bindEnumOpt :
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val failEnum : CoqExpr.coq_expr -> CoqExpr.coq_expr

val enumChecker :
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr
val enumCheckerOpt :
  CoqExpr.coq_expr ->
  string -> (CoqExpr.var -> CoqExpr.coq_expr) ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr

val thunkify : CoqExpr.coq_expr -> CoqExpr.coq_expr
val oneof : CoqExpr.coq_expr list -> CoqExpr.coq_expr
val oneofThunked : CoqExpr.coq_expr list -> CoqExpr.coq_expr
val frequency :
  (CoqExpr.coq_expr * CoqExpr.coq_expr) list -> CoqExpr.coq_expr
val frequencyThunked :
  (CoqExpr.coq_expr * CoqExpr.coq_expr) list -> CoqExpr.coq_expr
val backtracking :
  (CoqExpr.coq_expr * CoqExpr.coq_expr) list -> CoqExpr.coq_expr
val enumerating :
  (CoqExpr.coq_expr) list -> CoqExpr.coq_expr
val uniform_backtracking : CoqExpr.coq_expr list -> CoqExpr.coq_expr
val checker_backtracking : CoqExpr.coq_expr list -> CoqExpr.coq_expr
module TyCtrMap : CMap.ExtS with type key = CoqExpr.Ord_ty_ctr.t and module Set := Set.Make(CoqExpr.Ord_ty_ctr)
module CtrMap : CMap.ExtS with type key = CoqExpr.Ord_ctr.t and module Set := Set.Make(CoqExpr.Ord_ctr)
