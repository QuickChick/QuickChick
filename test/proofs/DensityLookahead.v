(** The variable-use look-ahead of the density prefix bound.

    The density bound (DensityPrefixBound.v) takes its variable-use
    look-ahead [la] as a premise: [la] is at most the uses the remaining steps
    incur. That bound's look-ahead is the floor's count of bound non-input
    variables of the remaining hypotheses plus, for each unbound variable in
    k of them, k - 1: the [lookahead] of BudgetAwarePrefixBound.v.

    get_num_var_uses counts, in each step, the occurrences of variables bound
    by earlier steps. When a hypothesis is scheduled, each of its variables
    that is neither an input nor one of its outputs has been bound by an
    earlier step, so its steps count at least [counted_deps]. That is the
    premise [uses_cover] below; the counting theorem then discharges the
    density bound's premise. *)

From Coq Require Import List Arith Lia.
Require Import BudgetAwarePrefixBound DensityPrefixBound.

Section DensityLookahead.
  Variable universe : list nat.
  Variable input bound : nat -> bool.
  Variable hs : list BudgetAwarePrefixBound.hyp.

  Hypothesis outputs_unbound : forall h v,
    List.In h hs -> BudgetAwarePrefixBound.outs h v = true -> bound v = false.
  Hypothesis inputs_bound : forall v, input v = true -> bound v = true.
  Hypothesis produced_once : forall v,
    BudgetAwarePrefixBound.count (fun h => BudgetAwarePrefixBound.outs h v) hs <= 1.

  (** [rest_uses] is what get_num_var_uses counts over the remaining steps. *)
  Variable rest_uses : nat.
  Hypothesis uses_cover :
    BudgetAwarePrefixBound.hsum hs (BudgetAwarePrefixBound.counted_deps universe input)
    <= rest_uses.

  Theorem density_lookahead_le :
    BudgetAwarePrefixBound.lookahead universe input bound hs <= rest_uses.
  Proof.
    pose proof (BudgetAwarePrefixBound.lookahead_admissible universe input bound hs
      outputs_unbound inputs_bound produced_once). lia.
  Qed.

  (** The density bound with this look-ahead is admissible for every
      completion of the committed prefix, for every built-in policy. *)
  Corollary density_bound_with_lookahead : forall dense p prefix forced others up,
    DensityPrefixBound.at_least_as_good dense p
      {| DensityPrefixBound.grades := prefix ++ forced;
         DensityPrefixBound.uses :=
           up + BudgetAwarePrefixBound.lookahead universe input bound hs |}
      {| DensityPrefixBound.grades := prefix ++ forced ++ others;
         DensityPrefixBound.uses := up + rest_uses |}.
  Proof.
    intros. apply DensityPrefixBound.bound_admissible.
    apply DensityPrefixBound.lookahead_admissible. apply density_lookahead_le.
  Qed.
End DensityLookahead.
