val set_singleton : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_empty : RocqExpr.coq_expr
val set_full : RocqExpr.coq_expr
val set_bigcup :
  string ->
  RocqExpr.coq_expr ->
  (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val set_suchThat :
  string ->
  RocqExpr.coq_expr ->
  (RocqExpr.var -> RocqExpr.coq_expr) -> RocqExpr.coq_expr
val set_eq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_union :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_int :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset : RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val sub0set : RocqExpr.coq_expr
val imset_set0_subset : RocqExpr.coq_expr
val set_unions : RocqExpr.coq_expr list -> RocqExpr.coq_expr
val set_eq_refl : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl_refl : RocqExpr.coq_expr
val _incl_subset :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val incl_refl : RocqExpr.coq_expr
val incl_hd_same : RocqExpr.coq_expr -> RocqExpr.coq_expr
val incl_tl : RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_set_eq_compat :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_set0_r :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_eq_trans :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl_trans :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_set0_l :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_set0_neut_eq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val eq_bigcupl :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val cons_set_eq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val singl_set_eq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_setU_l :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_set1 :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val subset_respects_set_eq_l :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val subset_respects_set_eq_r :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val subset_respects_set_eq :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val subset_set_eq_compat :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val incl_bigcupl : RocqExpr.coq_expr -> RocqExpr.coq_expr
val incl_bigcup_compat :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_isSome : RocqExpr.coq_expr -> RocqExpr.coq_expr
val isSomeSet : RocqExpr.coq_expr -> RocqExpr.coq_expr
val incl_subset :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_set_subset_compat :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setI_subset_compat :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val nil_subset : RocqExpr.coq_expr -> RocqExpr.coq_expr
val cons_subset :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setI_set_incl :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setI_set_eq_r : RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_subset_r :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val setU_subset_l :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_set0_incl :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_singl_incl :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_union_incl :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_incl : RocqExpr.coq_expr -> RocqExpr.coq_expr
val rewrite_set_r :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val rewrite_set_l :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_bigcup_incl_l :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_eq_set_incl_r : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_eq_set_incl_l : RocqExpr.coq_expr -> RocqExpr.coq_expr
val in_imset :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val lift_union_compat :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val lift_subset_pres_r : RocqExpr.coq_expr -> RocqExpr.coq_expr
val lift_subset_pres_l : RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_set0_subset :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_set_U :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_set_I_l : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl_setI_l : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl_setI_r : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_incl_setU_l :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_subset :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_subset_r :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_setI_cons_subset_r :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val imset_bigcup_setI_cons_subset_r :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_nil_subset : RocqExpr.coq_expr
val isSome_subset : RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_setI_subset_pres :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_setI_subset_compat_backtrack :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_setI_subset_compat_backtrack_weak :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_setI_subset_pres_backtrack :
  RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_cons_setI_subset_pres_backtrack_weak :
  RocqExpr.coq_expr -> RocqExpr.coq_expr
val bigcup_nil_setI :
  RocqExpr.coq_expr ->
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val isSome_set_eq :
  RocqExpr.coq_expr -> RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_eq_isSome_sound : RocqExpr.coq_expr -> RocqExpr.coq_expr
val set_eq_isSome_complete : RocqExpr.coq_expr -> RocqExpr.coq_expr
