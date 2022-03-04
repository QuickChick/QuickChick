val set_singleton : GenericLib.coq_expr -> GenericLib.coq_expr
val set_empty : GenericLib.coq_expr
val set_full : GenericLib.coq_expr
val set_bigcup :
  string ->
  GenericLib.coq_expr ->
  (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val set_suchThat :
  string ->
  GenericLib.coq_expr ->
  (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val set_eq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_union :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_int :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset : GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val sub0set : GenericLib.coq_expr
val imset_set0_subset : GenericLib.coq_expr
val set_unions : GenericLib.coq_expr list -> GenericLib.coq_expr
val set_eq_refl : GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl_refl : GenericLib.coq_expr
val _incl_subset :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val incl_refl : GenericLib.coq_expr
val incl_hd_same : GenericLib.coq_expr -> GenericLib.coq_expr
val incl_tl : GenericLib.coq_expr -> GenericLib.coq_expr
val setU_set_eq_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setU_set0_r :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_eq_trans :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl_trans :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setU_set0_l :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setU_set0_neut_eq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val eq_bigcupl :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val cons_set_eq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val singl_set_eq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_setU_l :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_set1 :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val subset_respects_set_eq_l :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val subset_respects_set_eq_r :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val subset_respects_set_eq :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val subset_set_eq_compat :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val incl_bigcupl : GenericLib.coq_expr -> GenericLib.coq_expr
val incl_bigcup_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_isSome : GenericLib.coq_expr -> GenericLib.coq_expr
val isSomeSet : GenericLib.coq_expr -> GenericLib.coq_expr
val incl_subset :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setU_set_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setI_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val nil_subset : GenericLib.coq_expr -> GenericLib.coq_expr
val cons_subset :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setI_set_incl :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setI_set_eq_r : GenericLib.coq_expr -> GenericLib.coq_expr
val setU_subset_r :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val setU_subset_l :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_set0_incl :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_singl_incl :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_union_incl :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_incl : GenericLib.coq_expr -> GenericLib.coq_expr
val rewrite_set_r :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val rewrite_set_l :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_bigcup_incl_l :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_eq_set_incl_r : GenericLib.coq_expr -> GenericLib.coq_expr
val set_eq_set_incl_l : GenericLib.coq_expr -> GenericLib.coq_expr
val in_imset :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val lift_union_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val lift_subset_pres_r : GenericLib.coq_expr -> GenericLib.coq_expr
val lift_subset_pres_l : GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_set0_subset :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_set_U :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_set_I_l : GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl_setI_l : GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl_setI_r : GenericLib.coq_expr -> GenericLib.coq_expr
val set_incl_setU_l :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_subset :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_subset_r :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_setI_cons_subset_r :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val imset_bigcup_setI_cons_subset_r :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_nil_subset : GenericLib.coq_expr
val isSome_subset : GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_setI_subset_pres :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_setI_subset_compat_backtrack :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_setI_subset_compat_backtrack_weak :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_setI_subset_pres_backtrack :
  GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_cons_setI_subset_pres_backtrack_weak :
  GenericLib.coq_expr -> GenericLib.coq_expr
val bigcup_nil_setI :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val isSome_set_eq :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val set_eq_isSome_sound : GenericLib.coq_expr -> GenericLib.coq_expr
val set_eq_isSome_complete : GenericLib.coq_expr -> GenericLib.coq_expr
