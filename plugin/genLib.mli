val gGen : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val returnGen : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bindGen :
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val bindGenOpt :
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr

val gEnum : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val returnEnum : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bindEnum : 
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val bindEnumOpt :
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val failEnum : RocqExpr.rocq_expr -> RocqExpr.rocq_expr

val enumChecker :
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val enumCheckerOpt :
  RocqExpr.rocq_expr ->
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr

val thunkify : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val oneof : RocqExpr.rocq_expr list -> RocqExpr.rocq_expr
val oneofThunked : RocqExpr.rocq_expr list -> RocqExpr.rocq_expr
val frequency :
  (RocqExpr.rocq_expr * RocqExpr.rocq_expr) list -> RocqExpr.rocq_expr
val frequencyThunked :
  (RocqExpr.rocq_expr * RocqExpr.rocq_expr) list -> RocqExpr.rocq_expr
val backtracking :
  (RocqExpr.rocq_expr * RocqExpr.rocq_expr) list -> RocqExpr.rocq_expr
val enumerating :
  (RocqExpr.rocq_expr) list -> RocqExpr.rocq_expr
val uniform_backtracking : RocqExpr.rocq_expr list -> RocqExpr.rocq_expr
val checker_backtracking : RocqExpr.rocq_expr list -> RocqExpr.rocq_expr
module TyCtrMap : CMap.ExtS with type key = RocqExpr.Ord_ty_ctr.t and module Set := Set.Make(RocqExpr.Ord_ty_ctr)
module CtrMap : CMap.ExtS with type key = RocqExpr.Ord_ctr.t and module Set := Set.Make(RocqExpr.Ord_ctr)
