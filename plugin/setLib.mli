val set_singleton : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_empty : CoqExpr.coq_expr
val set_full : CoqExpr.coq_expr
val set_bigcup :
  string ->
  CoqExpr.coq_expr ->
  (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val set_suchThat :
  string ->
  CoqExpr.coq_expr ->
  (CoqExpr.var -> CoqExpr.coq_expr) -> CoqExpr.coq_expr
val set_eq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_union :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_int :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset : CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val sub0set : CoqExpr.coq_expr
val imset_set0_subset : CoqExpr.coq_expr
val set_unions : CoqExpr.coq_expr list -> CoqExpr.coq_expr
val set_eq_refl : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl_refl : CoqExpr.coq_expr
val _incl_subset :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val incl_refl : CoqExpr.coq_expr
val incl_hd_same : CoqExpr.coq_expr -> CoqExpr.coq_expr
val incl_tl : CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_set_eq_compat :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_set0_r :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_eq_trans :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl_trans :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_set0_l :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_set0_neut_eq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val eq_bigcupl :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val cons_set_eq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val singl_set_eq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_setU_l :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_set1 :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val subset_respects_set_eq_l :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val subset_respects_set_eq_r :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val subset_respects_set_eq :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val subset_set_eq_compat :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val incl_bigcupl : CoqExpr.coq_expr -> CoqExpr.coq_expr
val incl_bigcup_compat :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_isSome : CoqExpr.coq_expr -> CoqExpr.coq_expr
val isSomeSet : CoqExpr.coq_expr -> CoqExpr.coq_expr
val incl_subset :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_set_subset_compat :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setI_subset_compat :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val nil_subset : CoqExpr.coq_expr -> CoqExpr.coq_expr
val cons_subset :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setI_set_incl :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setI_set_eq_r : CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_subset_r :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val setU_subset_l :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_set0_incl :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_singl_incl :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_union_incl :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_incl : CoqExpr.coq_expr -> CoqExpr.coq_expr
val rewrite_set_r :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val rewrite_set_l :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_bigcup_incl_l :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_eq_set_incl_r : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_eq_set_incl_l : CoqExpr.coq_expr -> CoqExpr.coq_expr
val in_imset :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val lift_union_compat :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val lift_subset_pres_r : CoqExpr.coq_expr -> CoqExpr.coq_expr
val lift_subset_pres_l : CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_set0_subset :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_set_U :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_set_I_l : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl_setI_l : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl_setI_r : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_incl_setU_l :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_subset :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_subset_r :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_setI_cons_subset_r :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val imset_bigcup_setI_cons_subset_r :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_nil_subset : CoqExpr.coq_expr
val isSome_subset : CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_setI_subset_pres :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_setI_subset_compat_backtrack :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_setI_subset_compat_backtrack_weak :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_setI_subset_pres_backtrack :
  CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_cons_setI_subset_pres_backtrack_weak :
  CoqExpr.coq_expr -> CoqExpr.coq_expr
val bigcup_nil_setI :
  CoqExpr.coq_expr ->
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val isSome_set_eq :
  CoqExpr.coq_expr -> CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_eq_isSome_sound : CoqExpr.coq_expr -> CoqExpr.coq_expr
val set_eq_isSome_complete : CoqExpr.coq_expr -> CoqExpr.coq_expr
