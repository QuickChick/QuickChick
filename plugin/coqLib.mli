val gExIntro_impl :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gExIntro :
  string ->
  (GenericLib.var -> GenericLib.coq_expr) ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gEx :
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val gConjIntro :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gEqType :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gConj : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gProjL : GenericLib.coq_expr -> GenericLib.coq_expr
val gProjR : GenericLib.coq_expr -> GenericLib.coq_expr
val gImpl : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gForall :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gProd : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gLe  : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr  
val gLeq : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gIsTrueLeq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gOrIntroL : GenericLib.coq_expr -> GenericLib.coq_expr
val gOrIntroR : GenericLib.coq_expr -> GenericLib.coq_expr
val gEqRefl : GenericLib.coq_expr -> GenericLib.coq_expr
val gTt : GenericLib.coq_expr
val gI : GenericLib.coq_expr
val gT : GenericLib.coq_expr
val gTrueb : GenericLib.coq_expr
val gFalseb : GenericLib.coq_expr
val gTrue : GenericLib.coq_expr
val gFalse : GenericLib.coq_expr
val gIff : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gIsTrue : GenericLib.coq_expr -> GenericLib.coq_expr
val gIsTrueTrue : GenericLib.coq_expr
val false_ind :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gfalse : GenericLib.coq_expr
val discriminate : GenericLib.coq_expr -> GenericLib.coq_expr
val rewrite :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val rewrite_sym :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val eq_symm : GenericLib.coq_expr -> GenericLib.coq_expr
val rewrite_symm :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val lt0_False : GenericLib.coq_expr -> GenericLib.coq_expr
val nat_ind :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val appn :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val matchDec :
  GenericLib.coq_expr ->
  (GenericLib.var list -> GenericLib.coq_expr) ->
  (GenericLib.var list -> GenericLib.coq_expr) -> GenericLib.coq_expr
val matchDecOpt :
  GenericLib.coq_expr ->
  (GenericLib.var list -> GenericLib.coq_expr) ->
  (GenericLib.var list -> GenericLib.coq_expr) -> GenericLib.coq_expr
val plus : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val plus_leq_compat_l : GenericLib.coq_expr -> GenericLib.coq_expr
val leq_addl :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val gProp : GenericLib.coq_expr
val succ_neq_zero : GenericLib.coq_expr -> GenericLib.coq_expr
val succ_neq_zero_app :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val isSome : GenericLib.coq_expr -> GenericLib.coq_expr
val isSomeSome : GenericLib.coq_expr -> GenericLib.coq_expr
val diff_false_true : GenericLib.coq_expr -> GenericLib.coq_expr
val gSnd : GenericLib.coq_expr -> GenericLib.coq_expr
val gFst : GenericLib.coq_expr -> GenericLib.coq_expr
val is_true : GenericLib.coq_expr -> GenericLib.coq_expr
val forall_nil : GenericLib.coq_expr -> GenericLib.coq_expr
val forall_cons :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val ltnOSn : GenericLib.coq_expr
val ltnOSn_pair : GenericLib.coq_expr
