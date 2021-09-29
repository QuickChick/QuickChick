val semGenSize :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semGen : GenericLib.coq_expr -> GenericLib.coq_expr
val semReturn : GenericLib.coq_expr -> GenericLib.coq_expr
val arbitrarySize : GenericLib.coq_expr -> GenericLib.coq_expr
val oneOf_freq :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semFreqSize :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semFreq :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindSize :
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindSizeMon :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val backtrackSizeMonotonic :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val backtrackSizeMonotonicOpt :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBacktrack_sound : GenericLib.coq_expr -> GenericLib.coq_expr
val semBacktrack_complete : GenericLib.coq_expr -> GenericLib.coq_expr
val semBacktrackSize :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val returnGenSizeMonotonic : GenericLib.coq_expr -> GenericLib.coq_expr
val returnGenSizeMonotonicOpt : GenericLib.coq_expr -> GenericLib.coq_expr
val bindMonotonic :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val bindMonotonicOpt :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val bindOptMonotonic :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val bindOptMonotonicOpt :
  GenericLib.coq_expr ->
  string -> (GenericLib.var -> GenericLib.coq_expr) -> GenericLib.coq_expr
val suchThatMaybeMonotonicOpt :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val suchThatMaybeOptMonotonicOpt :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindOptSizeMonotonicIncl_r :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindSizeMonotonicIncl_r :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindOptSizeMonotonicIncl_l :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindSizeMonotonicIncl_l :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semSuchThatMaybe_complete :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semSuchThatMaybeOpt_complete :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semSuchThatMaybe_sound :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semSuchThatMaybeOpt_sound :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindSizeOpt_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val semBindOptSizeOpt_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val suchThatMaybe_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val suchThatMaybeOpt_subset_compat :
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
val nat_set_ind :
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr ->
  GenericLib.coq_expr -> GenericLib.coq_expr -> GenericLib.coq_expr
