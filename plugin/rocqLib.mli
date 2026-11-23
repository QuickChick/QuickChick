val gExIntro_impl :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gExIntro :
  string ->
  (RocqExpr.var -> RocqExpr.rocq_expr) ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gEx :
  string -> (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val gConjIntro :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gEqType :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gConj : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gProjL : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gProjR : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gImpl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gForall :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gProd : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gLe  : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gLeq : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gIsTrueLeq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gOrIntroL : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gOrIntroR : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gEqRefl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gTt : RocqExpr.rocq_expr
val gI : RocqExpr.rocq_expr
val gT : RocqExpr.rocq_expr
val gTrueb : RocqExpr.rocq_expr
val gFalseb : RocqExpr.rocq_expr
val gTrue : RocqExpr.rocq_expr
val gFalse : RocqExpr.rocq_expr
val gIff : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gIsTrue : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gIsTrueTrue : RocqExpr.rocq_expr
val false_ind :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val discriminate : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val rewrite :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val rewrite_sym :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val lt0_False : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val nat_ind :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val appn :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val matchDec :
  RocqExpr.rocq_expr ->
  (RocqExpr.var list -> RocqExpr.rocq_expr) ->
  (RocqExpr.var list -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val matchDecOpt :
  RocqExpr.rocq_expr ->
  (RocqExpr.var list -> RocqExpr.rocq_expr) ->
  (RocqExpr.var list -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val plus : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val plus_leq_compat_l : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val leq_addl :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gProp : RocqExpr.rocq_expr
val succ_neq_zero : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val succ_neq_zero_app :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val isSome : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val isSomeSome : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val diff_false_true : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gSnd : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val gFst : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val is_true : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val forall_nil : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val forall_cons :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val ltnOSn : RocqExpr.rocq_expr
val ltnOSn_pair : RocqExpr.rocq_expr
