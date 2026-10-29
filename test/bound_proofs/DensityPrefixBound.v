(** Admissibility of QuickChick's density prefix bound, and exactness of
    pruning with it, for every built-in ranking policy.

    This models ScheduleRanking.prefix_bound, compare_without_id and
    can_prune_after (plugin/scheduleRanking.ml). The OCaml search supplies
    the premises of [bound_admissible]: every committed step, and every
    forced check, occurs in each completion with the grade the bound uses,
    and the variable-use look-ahead never exceeds the uses the remaining steps
    incur. QC_SCHEDULE_SCORE_PRUNING=verify checks those premises at run
    time against every completed descendant. *)

From Coq Require Import List Arith Lia Permutation.
Import ListNotations.

(** * Grades and features *)

(** Grades are density ranks: 0 Checking, 1 Backtracking, 2 Neutral,
    3 Partial, 4 Total. [dense] holds for generators and theorems, where a
    denser schedule is better and density is the minimum grade; otherwise
    density is the maximum and a lower one is better. *)

Definition density (dense : bool) (gs : list nat) : nat :=
  fold_left (if dense then Nat.min else Nat.max) gs (if dense then 4 else 0).

Definition count (g : nat) (gs : list nat) : nat :=
  length (filter (Nat.eqb g) gs).

Record features := { grades : list nat; uses : nat }.

Inductive policy :=
| DensityThenVars | DensityCountsThenVars | DensityOnly
| VarsThenDensity | VarsOnly.

(** The comparison as a lexicographic key, smaller is better. The histogram
    is compared by counts of Checking first for generators and of Total
    first otherwise, as compare_histogram does. *)

Definition density_key (dense : bool) (gs : list nat) : nat :=
  if dense then 4 - density true gs else density false gs.

Definition histogram_key (dense : bool) (gs : list nat) : list nat :=
  map (fun g => count g gs) (if dense then [0;1;2;3;4] else [4;3;2;1;0]).

Definition key (dense : bool) (p : policy) (f : features) : list nat :=
  match p with
  | DensityThenVars => [density_key dense (grades f); uses f]
  | DensityCountsThenVars =>
      density_key dense (grades f) :: histogram_key dense (grades f) ++ [uses f]
  | DensityOnly => [density_key dense (grades f)]
  | VarsThenDensity => [uses f; density_key dense (grades f)]
  | VarsOnly => [uses f]
  end.

Fixpoint lex_le (a b : list nat) : Prop :=
  match a, b with
  | [], _ => True
  | _ :: _, [] => False
  | x :: a', y :: b' => x < y \/ (x = y /\ lex_le a' b')
  end.

(** [at_least_as_good] is compare_without_id <= 0. *)
Definition at_least_as_good (dense : bool) (p : policy) (f g : features) : Prop := lex_le (key dense p f) (key dense p g).

(** * Lexicographic order *)

Lemma lex_le_trans : forall a b c, lex_le a b -> lex_le b c -> lex_le a c.
Proof.
  induction a as [|x a IH]; intros b c Hab Hbc; [exact I|].
  destruct b as [|y b]; [contradiction|].
  destruct c as [|z c]; [contradiction|].
  simpl in *.
  destruct Hab as [Hxy|[Exy Hab]]; destruct Hbc as [Hyz|[Eyz Hbc]].
  - left; lia.
  - left; lia.
  - left; lia.
  - right; split; [lia|eapply IH; eauto].
Qed.

Fixpoint pointwise_le (a b : list nat) : Prop :=
  match a, b with
  | [], [] => True
  | x :: a', y :: b' => x <= y /\ pointwise_le a' b'
  | _, _ => False
  end.

Lemma pointwise_lex : forall a b, pointwise_le a b -> lex_le a b.
Proof.
  induction a as [|x a IH]; intros b H; [exact I|].
  destruct b as [|y b]; [contradiction|].
  simpl in *; destruct H as [Hxy Hab].
  destruct (Nat.eq_dec x y) as [Exy|Nxy]; [right; split; auto|left; lia].
Qed.

(** * Grade folds over a sub-multiset *)

Lemma fold_min_le : forall gs a, fold_left Nat.min gs a <= a.
Proof. induction gs; simpl; intros; [lia|]. specialize (IHgs (Nat.min a0 a)). lia. Qed.

Lemma fold_min_app : forall xs ys a,
  fold_left Nat.min (xs ++ ys) a = fold_left Nat.min ys (fold_left Nat.min xs a).
Proof. intros; apply fold_left_app. Qed.

Lemma fold_min_mono : forall gs a b, a <= b -> fold_left Nat.min gs a <= fold_left Nat.min gs b.
Proof. induction gs; simpl; intros; auto. apply IHgs. lia. Qed.

Lemma fold_max_ge : forall gs a, a <= fold_left Nat.max gs a.
Proof. induction gs; simpl; intros; [lia|]. specialize (IHgs (Nat.max a0 a)). lia. Qed.

Lemma fold_max_mono : forall gs a b, a <= b -> fold_left Nat.max gs a <= fold_left Nat.max gs b.
Proof. induction gs; simpl; intros; auto. apply IHgs. lia. Qed.

Lemma fold_min_perm : forall xs ys a, Permutation xs ys ->
  fold_left Nat.min xs a = fold_left Nat.min ys a.
Proof.
  intros xs ys a H; revert a; induction H; simpl; intros; auto.
  - f_equal; lia.
  - rewrite IHPermutation1; auto.
Qed.

Lemma fold_max_perm : forall xs ys a, Permutation xs ys ->
  fold_left Nat.max xs a = fold_left Nat.max ys a.
Proof.
  intros xs ys a H; revert a; induction H; simpl; intros; auto.
  - f_equal; lia.
  - rewrite IHPermutation1; auto.
Qed.

Lemma count_perm : forall g xs ys, Permutation xs ys -> count g xs = count g ys.
Proof.
  intros g xs ys H; unfold count; induction H; simpl; auto.
  - destruct (Nat.eqb g x); simpl; auto.
  - destruct (Nat.eqb g x), (Nat.eqb g y); simpl; auto.
  - lia.
Qed.

Lemma count_app : forall g xs ys, count g (xs ++ ys) = count g xs + count g ys.
Proof. intros; unfold count; rewrite filter_app, length_app; auto. Qed.

(** The bound's grades [b] are a sub-multiset of the completion's grades
    [b ++ r], up to order. *)

Lemma density_key_sub : forall dense b r s, Permutation s (b ++ r) ->
  density_key dense b <= density_key dense s.
Proof.
  intros dense b r s Hs; unfold density_key, density; destruct dense.
  - rewrite (fold_min_perm _ _ _ Hs), fold_min_app.
    pose proof (fold_min_le r (fold_left Nat.min b 4)). lia.
  - rewrite (fold_max_perm _ _ _ Hs), fold_left_app. apply fold_max_ge.
Qed.

Lemma histogram_key_sub : forall dense b r s, Permutation s (b ++ r) ->
  pointwise_le (histogram_key dense b) (histogram_key dense s).
Proof.
  intros dense b r s Hs; unfold histogram_key.
  assert (H : forall g, count g b <= count g s).
  { intro g; rewrite (count_perm g _ _ Hs), count_app; lia. }
  destruct dense; simpl; repeat split; auto.
Qed.

Lemma pointwise_app : forall a b c d,
  pointwise_le a b -> pointwise_le c d -> pointwise_le (a ++ c) (b ++ d).
Proof.
  induction a as [|x a IH]; intros [|y b] c d Hab Hcd; simpl in *; auto; try tauto.
  destruct Hab; split; auto.
Qed.

(** * Admissibility and exact pruning *)

(** A bound is admissible for a completion when its grades are a
    sub-multiset of the completion's and its uses do not exceed the
    completion's. Committed steps and forced checks contribute their grades;
    an uncertified grade is omitted, which is the best case in every policy. *)

Definition admissible (bound completion : features) :=
  exists rest, Permutation (grades completion) (grades bound ++ rest)
               /\ uses bound <= uses completion.

Theorem bound_admissible : forall dense p bound completion,
  admissible bound completion -> at_least_as_good dense p bound completion.
Proof.
  intros dense p bound completion [r [Hperm Huses]].
  unfold at_least_as_good; apply pointwise_lex.
  pose proof (density_key_sub dense _ _ _ Hperm) as Hd.
  pose proof (histogram_key_sub dense _ _ _ Hperm) as Hh.
  destruct p; simpl; repeat split; auto.
  apply pointwise_app; auto. simpl; auto.
Qed.

(** can_prune_after: an incumbent at least as good as the bound of a prefix
    is at least as good as every completion of that prefix. The incumbent was
    found first, so it also wins ties; no completion can be selected over it. *)

Theorem prune_exact : forall dense p incumbent bound completion,
  at_least_as_good dense p incumbent bound ->
  admissible bound completion ->
  at_least_as_good dense p incumbent completion.
Proof.
  intros dense p incumbent bound completion Hinc Hadm.
  unfold at_least_as_good in *.
  eapply lex_le_trans; [exact Hinc|].
  apply (bound_admissible dense p bound completion Hadm).
Qed.

(** The committed prefix of a completion is admissible for it when variable
    uses add up over steps, which get_num_var_uses does. *)

Corollary committed_prefix_admissible : forall prefix rest up ur,
  admissible {| grades := prefix; uses := up |}
             {| grades := prefix ++ rest; uses := up + ur |}.
Proof. intros; exists rest; simpl; split; [apply Permutation_refl|lia]. Qed.

(** Forced checks and the variable-use look-ahead strengthen the bound as
    long as they occur in every completion: here [forced] grades and [la]
    uses are part of the remaining steps' [rest] grades and [ur] uses. *)

Corollary lookahead_admissible : forall prefix forced others up la ur,
  la <= ur ->
  admissible {| grades := prefix ++ forced; uses := up + la |}
             {| grades := prefix ++ forced ++ others; uses := up + ur |}.
Proof.
  intros; exists others; simpl; split; [rewrite app_assoc; apply Permutation_refl|lia].
Qed.
