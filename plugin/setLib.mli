val set_singleton : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_empty : RocqExpr.rocq_expr
val set_full : RocqExpr.rocq_expr
val set_bigcup :
  string ->
  RocqExpr.rocq_expr ->
  (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val set_suchThat :
  string ->
  RocqExpr.rocq_expr ->
  (RocqExpr.var -> RocqExpr.rocq_expr) -> RocqExpr.rocq_expr
val set_eq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_union :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_int :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset : RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val sub0set : RocqExpr.rocq_expr
val imset_set0_subset : RocqExpr.rocq_expr
val set_unions : RocqExpr.rocq_expr list -> RocqExpr.rocq_expr
val set_eq_refl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl_refl : RocqExpr.rocq_expr
val _incl_subset :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val incl_refl : RocqExpr.rocq_expr
val incl_hd_same : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val incl_tl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_set_eq_compat :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_set0_r :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_eq_trans :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl_trans :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_set0_l :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_set0_neut_eq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val eq_bigcupl :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val cons_set_eq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val singl_set_eq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_setU_l :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_set1 :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val subset_respects_set_eq_l :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val subset_respects_set_eq_r :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val subset_respects_set_eq :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val subset_set_eq_compat :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val incl_bigcupl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val incl_bigcup_compat :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_isSome : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val isSomeSet : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val incl_subset :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_set_subset_compat :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setI_subset_compat :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val nil_subset : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val cons_subset :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setI_set_incl :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setI_set_eq_r : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_subset_r :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val setU_subset_l :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_set0_incl :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_singl_incl :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_union_incl :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_incl : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val rewrite_set_r :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val rewrite_set_l :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_bigcup_incl_l :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_eq_set_incl_r : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_eq_set_incl_l : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val in_imset :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val lift_union_compat :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val lift_subset_pres_r : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val lift_subset_pres_l : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_set0_subset :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_set_U :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_set_I_l : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl_setI_l : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl_setI_r : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_incl_setU_l :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_subset :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_subset_r :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_setI_cons_subset_r :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val imset_bigcup_setI_cons_subset_r :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_nil_subset : RocqExpr.rocq_expr
val isSome_subset : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_setI_subset_pres :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_setI_subset_compat_backtrack :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_setI_subset_compat_backtrack_weak :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_setI_subset_pres_backtrack :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_cons_setI_subset_pres_backtrack_weak :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val bigcup_nil_setI :
  RocqExpr.rocq_expr ->
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val isSome_set_eq :
  RocqExpr.rocq_expr -> RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_eq_isSome_sound : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
val set_eq_isSome_complete : RocqExpr.rocq_expr -> RocqExpr.rocq_expr
