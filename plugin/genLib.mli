val gGen : RocqExpr.coq_expr -> RocqExpr.coq_expr
val returnGen : RocqExpr.coq_expr -> RocqExpr.coq_expr
val bindGen :
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val bindGenOpt :
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr

val gEnum : RocqExpr.coq_expr -> RocqExpr.coq_expr
val returnEnum : RocqExpr.coq_expr -> RocqExpr.coq_expr
val bindEnum : 
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val bindEnumOpt :
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val failEnum : RocqExpr.coq_expr -> RocqExpr.coq_expr

val enumChecker :
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr
val enumCheckerOpt :
  RocqExpr.coq_expr ->
  string -> (RocqExpr.var -> RocqExpr.coq_expr) ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr

val thunkify : RocqExpr.coq_expr -> RocqExpr.coq_expr
val oneof : RocqExpr.coq_expr list -> RocqExpr.coq_expr
val oneofThunked : RocqExpr.coq_expr list -> RocqExpr.coq_expr
val frequency :
  (RocqExpr.coq_expr * RocqExpr.coq_expr) list -> RocqExpr.coq_expr
val frequencyThunked :
  (RocqExpr.coq_expr * RocqExpr.coq_expr) list -> RocqExpr.coq_expr
val backtracking :
  (RocqExpr.coq_expr * RocqExpr.coq_expr) list -> RocqExpr.coq_expr
val enumerating :
  (RocqExpr.coq_expr) list -> RocqExpr.coq_expr
val uniform_backtracking : RocqExpr.coq_expr list -> RocqExpr.coq_expr
val checker_backtracking : RocqExpr.coq_expr list -> RocqExpr.coq_expr
module TyCtrMap : CMap.ExtS with type key = RocqExpr.Ord_ty_ctr.t and module Set := Set.Make(RocqExpr.Ord_ty_ctr)
module CtrMap : CMap.ExtS with type key = RocqExpr.Ord_ctr.t and module Set := Set.Make(RocqExpr.Ord_ctr)
