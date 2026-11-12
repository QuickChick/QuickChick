val gExIntro_impl :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gExIntro :
  string ->
  (RocqExpr.var -> RocqExpr.coq_expr) ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gEx :
  string -> (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val gConjIntro :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gEqType :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gConj : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gProjL : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gProjR : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gImpl : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gForall :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gProd : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gLe  : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gLeq : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gIsTrueLeq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gOrIntroL : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gOrIntroR : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gEqRefl : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gTt : RocqExpr.coq_expr
val gI : RocqExpr.coq_expr
val gT : RocqExpr.coq_expr
val gTrueb : RocqExpr.coq_expr
val gFalseb : RocqExpr.coq_expr
val gTrue : RocqExpr.coq_expr
val gFalse : RocqExpr.coq_expr
val gIff : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gIsTrue : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gIsTrueTrue : RocqExpr.coq_expr
val false_ind :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val discriminate : RocqExpr.coq_expr -> RocqExpr.coq_expr
val rewrite :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val rewrite_sym :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val lt0_False : RocqExpr.coq_expr -> RocqExpr.coq_expr
val nat_ind :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val appn :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val matchDec :
  RocqExpr.coq_expr ->
  (RocqExpr.var list -> RocqExpr.coq_expr) ->
  (RocqExpr.var list -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val matchDecOpt :
  RocqExpr.coq_expr ->
  (RocqExpr.var list -> RocqExpr.coq_expr) ->
  (RocqExpr.var list -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val plus : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val plus_leq_compat_l : RocqExpr.coq_expr -> RocqExpr.coq_expr
val leq_addl :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val gProp : RocqExpr.coq_expr
val succ_neq_zero : RocqExpr.coq_expr -> RocqExpr.coq_expr
val succ_neq_zero_app :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val isSome : RocqExpr.coq_expr -> RocqExpr.coq_expr
val isSomeSome : RocqExpr.coq_expr -> RocqExpr.coq_expr
val diff_false_true : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gSnd : RocqExpr.coq_expr -> RocqExpr.coq_expr
val gFst : RocqExpr.coq_expr -> RocqExpr.coq_expr
val is_true : RocqExpr.coq_expr -> RocqExpr.coq_expr
val forall_nil : RocqExpr.coq_expr -> RocqExpr.coq_expr
val forall_cons :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val ltnOSn : RocqExpr.coq_expr
val ltnOSn_pair : RocqExpr.coq_expr
