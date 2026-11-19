(** Admissibility of the BudgetAware prefix bound with its look-aheads, and
    exactness of pruning with it.

    This models BudgetAwareScore.score_schedule and compare
    (plugin/budgetAwareScore.ml) and the prefix bound of BudgetAware score
    pruning (plugin/tactic_quickchick.mlg.cppo): the committed prefix's score,
    with unstable dependencies at their best, forced checks at Checking, and
    variable dependencies raised by the floor's look-ahead.

    The search supplies these premises, which QC_SCHEDULE_SCORE_PRUNING=verify
    checks at run time: a step's score does not depend on its position; each
    variable is produced at most once; a hypothesis's steps count each of its
    variables that is neither an input nor one of its outputs at least once
    (in its own source, or in the equality check a constrained output
    becomes); and its outputs are unbound when it is scheduled. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(** * Lexicographic keys *)

Fixpoint lex_le (a b : list nat) : Prop :=
  match a, b with
  | [], _ => True
  | _ :: _, [] => False
  | x :: a', y :: b' => x < y \/ (x = y /\ lex_le a' b')
  end.

Lemma lex_le_trans : forall a b c, lex_le a b -> lex_le b c -> lex_le a c.
Proof.
  induction a as [|x a IH]; intros b c Hab Hbc; [exact I|].
  destruct b as [|y b]; [contradiction|]. destruct c as [|z c]; [contradiction|].
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

(** * Scores *)

(** BudgetAware compares (selectivity, density, fabrication, locality,
    input-check dependencies, variable dependencies) lexicographically,
    smaller is better; density and locality are ranks combined by max. *)

Record score := {
  selectivity : nat; density : nat; fabrication : nat;
  locality : nat; input_deps : nat; var_deps : nat }.

Definition key (s : score) :=
  [selectivity s; density s; fabrication s; locality s; input_deps s; var_deps s].

Definition at_least_as_good (a b : score) := lex_le (key a) (key b).

Definition fields_le (a b : score) :=
  selectivity a <= selectivity b /\ density a <= density b /\
  fabrication a <= fabrication b /\ locality a <= locality b /\
  input_deps a <= input_deps b /\ var_deps a <= var_deps b.

Lemma fields_le_good : forall a b, fields_le a b -> at_least_as_good a b.
Proof.
  intros a b (H1 & H2 & H3 & H4 & H5 & H6).
  apply pointwise_lex; unfold key; simpl; repeat split; auto.
Qed.

(** Pruning with an incumbent at least as good as an admissible bound loses
    no completion; the incumbent was found first and wins ties. *)
Theorem prune_exact : forall incumbent bound completion,
  at_least_as_good incumbent bound -> fields_le bound completion ->
  at_least_as_good incumbent completion.
Proof.
  intros incumbent bound completion Hinc Hle. unfold at_least_as_good in *.
  eapply lex_le_trans; [exact Hinc|]. apply (fields_le_good _ _ Hle).
Qed.

(** * Per-step fields *)

(** A step's own contribution to the five per-step fields. *)
Record step_score := { s_density : nat; s_fabrication : nat; s_locality : nat;
                       s_input_deps : nat; s_var_deps : nat }.

Definition sum f (xs : list step_score) := fold_right (fun x n => f x + n) 0 xs.
Definition maxf f (xs : list step_score) := fold_right (fun x n => Nat.max (f x) n) 0 xs.

Lemma sum_app : forall f xs ys, sum f (xs ++ ys) = sum f xs + sum f ys.
Proof. induction xs; simpl; intros; [auto|rewrite IHxs; lia]. Qed.

Lemma maxf_app : forall f xs ys, maxf f (xs ++ ys) = Nat.max (maxf f xs) (maxf f ys).
Proof. induction xs; simpl; intros; [lia|rewrite IHxs; lia]. Qed.

Lemma maxf_in : forall f x xs, In x xs -> f x <= maxf f xs.
Proof. induction xs; simpl; intros H; [contradiction|destruct H as [->|H]; [lia|]].
  specialize (IHxs H); lia. Qed.

(** * Selectivity *)

(** Over a finite universe of variables, a schedule counts each variable that
    is finitely pinnable, produced, and not produced at a finitely pinned
    position. Each of the three properties of the completion is the union of
    the property over prefix and rest. *)

Section Selectivity.
  Variable universe : list nat.
  Variables (pin_p prod_p fin_p pin_r prod_r fin_r : nat -> bool).

  Definition counted (pin prod fin : nat -> bool) (v : nat) := pin v && prod v && negb (fin v).
  Definition sel (pin prod fin : nat -> bool) := length (filter (counted pin prod fin) universe).

  (** Each variable is produced at most once: one produced in the prefix is
      not produced again, so it is not produced finitely by the rest. *)
  Hypothesis produced_once : forall v, prod_p v = true -> prod_r v = false.
  Hypothesis finite_is_produced : forall v, fin_r v = true -> prod_r v = true.

  Lemma filter_length_mono : forall (p q : nat -> bool) xs,
    (forall x, p x = true -> q x = true) ->
    length (filter p xs) <= length (filter q xs).
  Proof.
    intros p q xs H; induction xs as [|x xs IH]; simpl; [lia|].
    destruct (p x) eqn:Px; [rewrite (H x Px); simpl; lia|destruct (q x); simpl; lia].
  Qed.

  Theorem selectivity_admissible :
    sel pin_p prod_p fin_p <=
    sel (fun v => pin_p v || pin_r v) (fun v => prod_p v || prod_r v)
        (fun v => fin_p v || fin_r v).
  Proof.
    unfold sel; apply filter_length_mono; intros v; unfold counted.
    destruct (pin_p v), (prod_p v) eqn:Pp, (fin_p v); simpl; intro H; try discriminate H.
    destruct (fin_r v) eqn:Fr; [|reflexivity].
    pose proof (produced_once v Pp). pose proof (finite_is_produced v Fr). congruence.
  Qed.
End Selectivity.

(** * The variable-dependency look-ahead *)

(** Remaining hypotheses over a finite universe of variables: each has its
    variables and its outputs (the variables its step binds), as predicates.
    [counted_deps h] is what the premise says the hypothesis's steps contribute at
    least to variable dependencies: its variables that are neither inputs nor
    its outputs. *)

Record hyp := { vars : nat -> bool; outs : nat -> bool }.

Section Lookahead.
  Variable universe : list nat.
  Variable input bound : nat -> bool.
  Variable hs : list hyp.

  Definition count {A} (p : A -> bool) (xs : list A) := length (filter p xs).

  Definition counted_deps (h : hyp) :=
    count (fun v => vars h v && negb (input v) && negb (outs h v)) universe.

  (** Outputs are unbound when a hypothesis is scheduled, inputs are bound
      from the start, and a variable is the output of at most one remaining
      hypothesis. *)
  Hypothesis outputs_unbound : forall h v, In h hs -> outs h v = true -> bound v = false.
  Hypothesis inputs_bound : forall v, input v = true -> bound v = true.
  Hypothesis produced_once : forall v, count (fun h => outs h v) hs <= 1.
  Hypothesis outputs_are_vars : forall h v, In h hs -> outs h v = true -> vars h v = true.

  (** The floor's two counts: each hypothesis's bound non-input variables,
      and, for each unbound variable in k hypotheses, k - 1. *)
  Definition bound_part (h : hyp) :=
    count (fun v => vars h v && bound v && negb (input v)) universe.
  Definition occurrences v := count (fun h => vars h v) hs.

  Definition hsum (f : hyp -> nat) := fold_right (fun h n => f h + n) 0 hs.
  Definition vsum (f : nat -> nat) := fold_right (fun v n => f v + n) 0 universe.

  Definition lookahead :=
    hsum bound_part + vsum (fun v => if bound v then 0 else occurrences v - 1).

  (** Double counting over hypotheses and variables. *)
  Definition column (Q : hyp -> nat -> bool) (H : list hyp) v := count (fun h => Q h v) H.
  Arguments column : simpl never.

  Lemma column_cons : forall Q h H v,
    column Q (h :: H) v = (if Q h v then 1 else 0) + column Q H v.
  Proof. intros; unfold column, count; simpl; destruct (Q h v); reflexivity. Qed.

  Lemma sum_column_cons : forall Q h H (U : list nat),
    fold_right (fun v n => column Q (h :: H) v + n) 0 U =
    count (Q h) U + fold_right (fun v n => column Q H v + n) 0 U.
  Proof.
    intros Q h H U; induction U as [|u U IHU]; [reflexivity|].
    cbn [fold_right]. rewrite column_cons, IHU. unfold count; simpl.
    destruct (Q h u); simpl; lia.
  Qed.

  Lemma swap : forall (Q : hyp -> nat -> bool) (H : list hyp) (U : list nat),
    fold_right (fun h n => count (Q h) U + n) 0 H =
    fold_right (fun v n => column Q H v + n) 0 U.
  Proof.
    intros Q H U; induction H as [|h H IH].
    - simpl. induction U as [|u U IHU]; [reflexivity|]. cbn [fold_right].
      rewrite <- IHU. unfold column, count. reflexivity.
    - cbn [fold_right]. rewrite IH, sum_column_cons. reflexivity.
  Qed.

  Lemma count_le_ext : forall {A} (p q : A -> bool) xs,
    (forall x, In x xs -> p x = true -> q x = true) -> count p xs <= count q xs.
  Proof.
    intros A p q xs H; unfold count; induction xs as [|x xs IH]; simpl; [lia|].
    assert (IH' : length (filter p xs) <= length (filter q xs))
      by (apply IH; intros y Hy; apply H; right; exact Hy).
    destruct (p x) eqn:Px.
    - rewrite (H x (or_introl eq_refl) Px); simpl; lia.
    - destruct (q x); simpl; lia.
  Qed.

  Lemma count_split : forall {A} (p q : A -> bool) xs,
    count p xs <= count (fun x => p x && negb (q x)) xs + count q xs.
  Proof.
    intros A p q xs; unfold count; induction xs as [|x xs IH]; simpl; [lia|].
    destruct (p x), (q x); simpl; lia.
  Qed.

  Theorem lookahead_admissible : lookahead <= hsum counted_deps.
  Proof.
    unfold lookahead, hsum, bound_part, counted_deps, vsum.
    rewrite (swap (fun h v => vars h v && bound v && negb (input v))).
    rewrite (swap (fun h v => vars h v && negb (input v) && negb (outs h v))).
    unfold column.
    assert (Hv : forall v,
      count (fun h => vars h v && bound v && negb (input v)) hs +
      (if bound v then 0 else occurrences v - 1) <=
      count (fun h => vars h v && negb (input v) && negb (outs h v)) hs).
    { intro v. destruct (bound v) eqn:Bv; simpl.
      - rewrite Nat.add_0_r. apply count_le_ext. intros h Hh Hp.
        apply andb_true_iff in Hp as [Hp Hi]. rewrite andb_true_r in Hp. rewrite Hp, Hi; simpl.
        destruct (outs h v) eqn:Ov; [|reflexivity].
        rewrite (outputs_unbound h v Hh Ov) in Bv; discriminate.
      - assert (Iv : input v = false).
        { destruct (input v) eqn:Iv; [rewrite (inputs_bound v Iv) in Bv; discriminate|reflexivity]. }
        assert (Hz : count (fun h => vars h v && false && negb (input v)) hs = 0).
        { unfold count; clear; induction hs as [|h l IH]; simpl; [auto|].
          rewrite andb_false_r; simpl; auto. }
        rewrite Hz, Iv. simpl. unfold occurrences.
        pose proof (count_split (fun h => vars h v) (fun h => outs h v) hs) as Hs.
        pose proof (produced_once v) as Hp.
        assert (Heq : count (fun h => vars h v && negb (outs h v)) hs =
                      count (fun h => vars h v && true && negb (outs h v)) hs).
        { unfold count; f_equal; apply filter_ext; intro h; rewrite andb_true_r; auto. }
        lia. }
    clear -Hv. induction universe as [|v U IH]; simpl; [lia|].
    specialize (Hv v). lia.
  Qed.
End Lookahead.

(** * The bound

    With step scores independent of position, the committed prefix's per-step
    fields are at most the completion's (sums grow and maxima do not fall over
    [prefix ++ rest]); selectivity is at most the completion's by
    [selectivity_admissible]; a forced check in the rest has density Checking,
    the greatest rank; and the variable-dependency look-ahead is at most the
    rest's variable dependencies by [lookahead_admissible]. Each field of the
    bound is then at most the completion's, so [prune_exact] applies. *)

Theorem prefix_fields_le : forall (p r : list step_score) forced la,
  (forced = true -> exists c, In c r /\ 3 <= s_density c) ->
  la <= sum s_var_deps r ->
  forall sel_p sel_c, sel_p <= sel_c ->
  fields_le
    {| selectivity := sel_p;
       density := Nat.max (maxf s_density p) (if forced then 3 else 0);
       fabrication := sum s_fabrication p; locality := maxf s_locality p;
       input_deps := sum s_input_deps p; var_deps := sum s_var_deps p + la |}
    {| selectivity := sel_c;
       density := maxf s_density (p ++ r);
       fabrication := sum s_fabrication (p ++ r); locality := maxf s_locality (p ++ r);
       input_deps := sum s_input_deps (p ++ r); var_deps := sum s_var_deps (p ++ r) |}.
Proof.
  intros p r forced la Hforced Hla sel_p sel_c Hsel.
  unfold fields_le; simpl. rewrite !maxf_app, !sum_app.
  repeat split; try lia.
  destruct forced; [|lia].
  destruct (Hforced eq_refl) as [c [Hc Hd]].
  pose proof (maxf_in s_density c r Hc). lia.
Qed.
