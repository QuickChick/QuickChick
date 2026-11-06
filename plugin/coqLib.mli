val gExIntro_impl :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gExIntro :
  string ->
  (CoqExpr.var -> CoqExpr.coq_expr) ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gEx :
  string -> (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val gConjIntro :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gEqType :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gConj : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gProjL : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gProjR : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gImpl : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gForall :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gProd : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gLe  : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr  
val gLeq : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gIsTrueLeq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gOrIntroL : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gOrIntroR : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gEqRefl : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gTt : CoqExpr.coq_expr
val gI : CoqExpr.coq_expr
val gT : CoqExpr.coq_expr
val gTrueb : CoqExpr.coq_expr
val gFalseb : CoqExpr.coq_expr
val gTrue : CoqExpr.coq_expr
val gFalse : CoqExpr.coq_expr
val gIff : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gIsTrue : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gIsTrueTrue : CoqExpr.coq_expr
val false_ind :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val discriminate : CoqExpr.coq_expr -> CoqExpr.coq_expr
val rewrite :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val rewrite_sym :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val lt0_False : CoqExpr.coq_expr -> CoqExpr.coq_expr
val nat_ind :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val appn :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val matchDec :
  CoqExpr.coq_expr ->
  (CoqExpr.var list -> CoqExpr.coq_expr) ->
  (CoqExpr.var list -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val matchDecOpt :
  CoqExpr.coq_expr ->
  (CoqExpr.var list -> CoqExpr.coq_expr) ->
  (CoqExpr.var list -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val plus : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val plus_leq_compat_l : CoqExpr.coq_expr -> CoqExpr.coq_expr
val leq_addl :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val gProp : CoqExpr.coq_expr
val succ_neq_zero : CoqExpr.coq_expr -> CoqExpr.coq_expr
val succ_neq_zero_app :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val isSome : CoqExpr.coq_expr -> CoqExpr.coq_expr
val isSomeSome : CoqExpr.coq_expr -> CoqExpr.coq_expr
val diff_false_true : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gSnd : CoqExpr.coq_expr -> CoqExpr.coq_expr
val gFst : CoqExpr.coq_expr -> CoqExpr.coq_expr
val is_true : CoqExpr.coq_expr -> CoqExpr.coq_expr
val forall_nil : CoqExpr.coq_expr -> CoqExpr.coq_expr
val forall_cons :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val ltnOSn : CoqExpr.coq_expr
val ltnOSn_pair : CoqExpr.coq_expr
