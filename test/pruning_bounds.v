(* Algebraic bounds for committed schedule prefixes. Applying these lemmas to
   the typed scheduler requires proof that conversion preserves earlier steps
   and their finalized dependency grades. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Definition generator_worst (grades : list nat) := fold_left Nat.min grades 4.
Definition checker_worst (grades : list nat) := fold_left Nat.max grades 0.

Lemma fold_min_le_start : forall grades start,
  fold_left Nat.min grades start <= start.
Proof.
  induction grades as [|grade rest IH]; intros start; simpl; auto.
  specialize (IH (Nat.min start grade)).
  lia.
Qed.

Lemma fold_max_ge_start : forall grades start,
  start <= fold_left Nat.max grades start.
Proof.
  induction grades as [|grade rest IH]; intros start; simpl; auto.
  specialize (IH (Nat.max start grade)).
  lia.
Qed.

Lemma generator_prefix_bound : forall prefix suffix,
  4 - generator_worst prefix <=
  4 - generator_worst (prefix ++ suffix).
Proof.
  intros prefix suffix.
  unfold generator_worst.
  rewrite fold_left_app.
  pose proof (fold_min_le_start suffix (fold_left Nat.min prefix 4)) as H.
  pose proof (fold_min_le_start prefix 4) as Hrange.
  lia.
Qed.

Lemma checker_prefix_bound : forall prefix suffix,
  checker_worst prefix <= checker_worst (prefix ++ suffix).
Proof.
  intros prefix suffix.
  unfold checker_worst.
  rewrite fold_left_app.
  apply fold_max_ge_start.
Qed.

Lemma variable_use_prefix_bound : forall prefix suffix,
  fold_left Nat.add prefix 0 <= fold_left Nat.add (prefix ++ suffix) 0.
Proof.
  intros prefix suffix.
  rewrite fold_left_app.
  assert (H : forall xs start, start <= fold_left Nat.add xs start).
  { induction xs as [|x rest IH]; intros start; simpl; auto.
    specialize (IH (start + x)). lia. }
  apply H.
Qed.

Section StatefulVariableUses.
  Context {Environment Step : Type}.
  Variable update : Environment -> Step -> Environment.
  Variable use_count : Environment -> Step -> nat.

  Fixpoint scan_uses (env : Environment) (steps : list Step) : nat :=
    match steps with
    | [] => 0
    | step :: rest =>
        use_count env step + scan_uses (update env step) rest
    end.

  Fixpoint final_env (env : Environment) (steps : list Step) : Environment :=
    match steps with
    | [] => env
    | step :: rest => final_env (update env step) rest
    end.

  Lemma scan_uses_app : forall env prefix suffix,
    scan_uses env (prefix ++ suffix) =
    scan_uses env prefix + scan_uses (final_env env prefix) suffix.
  Proof.
    intros env prefix; revert env.
    induction prefix as [|step rest IH]; intros env suffix; simpl.
    - lia.
    - rewrite IH. lia.
  Qed.

  Theorem stateful_variable_use_prefix_bound : forall env prefix suffix,
    scan_uses env prefix <= scan_uses env (prefix ++ suffix).
  Proof.
    intros. rewrite scan_uses_app. lia.
  Qed.
End StatefulVariableUses.

Fixpoint grade_count (grade : nat) (grades : list nat) : nat :=
  match grades with
  | [] => 0
  | x :: rest => (if Nat.eqb grade x then 1 else 0) + grade_count grade rest
  end.

Lemma grade_count_app : forall grade prefix suffix,
  grade_count grade (prefix ++ suffix) =
  grade_count grade prefix + grade_count grade suffix.
Proof.
  intros grade prefix; induction prefix as [|x rest IH]; intros suffix;
    simpl; try rewrite IH; lia.
Qed.

Definition generator_counted_key grades uses :=
  [4 - generator_worst grades;
   grade_count 0 grades; grade_count 1 grades; grade_count 2 grades;
   grade_count 3 grades; grade_count 4 grades;
   fold_left Nat.add uses 0].

Definition checker_counted_key grades uses :=
  [checker_worst grades;
   grade_count 4 grades; grade_count 3 grades; grade_count 2 grades;
   grade_count 1 grades; grade_count 0 grades;
   fold_left Nat.add uses 0].

Lemma generator_counted_prefix_components : forall grades more uses more_uses,
  Forall2 le (generator_counted_key grades uses)
    (generator_counted_key (grades ++ more) (uses ++ more_uses)).
Proof.
  intros grades more uses more_uses.
  unfold generator_counted_key.
  repeat constructor;
    try apply generator_prefix_bound;
    try apply variable_use_prefix_bound;
    try (rewrite grade_count_app; lia).
Qed.

Lemma checker_counted_prefix_components : forall grades more uses more_uses,
  Forall2 le (checker_counted_key grades uses)
    (checker_counted_key (grades ++ more) (uses ++ more_uses)).
Proof.
  intros grades more uses more_uses.
  unfold checker_counted_key.
  repeat constructor;
    try apply checker_prefix_bound;
    try apply variable_use_prefix_bound;
    try (rewrite grade_count_app; lia).
Qed.

Fixpoint lex_compare (left right : list nat) : comparison :=
  match left, right with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x :: xs, y :: ys =>
      match Nat.compare x y with
      | Eq => lex_compare xs ys
      | result => result
      end
  end.

Lemma component_bounds_are_lex_bounds : forall left right,
  Forall2 le left right -> lex_compare left right <> Gt.
Proof.
  intros left right H; induction H as [|x y xs ys Hle Htail IH]; simpl.
  - discriminate.
  - destruct (Nat.compare x y) eqn:Hcmp; try discriminate; auto.
    apply Nat.compare_gt_iff in Hcmp; lia.
Qed.

Inductive lex_better : list nat -> list nat -> Prop :=
| lex_head : forall x y xs ys,
    x < y -> lex_better (x :: xs) (y :: ys)
| lex_tail : forall x xs ys,
    lex_better xs ys -> lex_better (x :: xs) (x :: ys).

Theorem strict_component_pruning_safe : forall incumbent bound completed,
  lex_better incumbent bound ->
  Forall2 le bound completed ->
  lex_better incumbent completed.
Proof.
  intros incumbent bound completed Hbetter Hbound.
  revert incumbent Hbetter.
  induction Hbound as [|b c bs cs Hbc Htail IH];
    intros incumbent Hbetter; inversion Hbetter; subst.
  - apply lex_head. lia.
  - destruct (Nat.eq_dec b c) as [Heq | Hneq].
    + subst. apply lex_tail. eapply IH; eauto.
    + apply lex_head. lia.
Qed.

Theorem generator_counted_prefix_bound : forall grades more uses more_uses,
  lex_compare (generator_counted_key grades uses)
    (generator_counted_key (grades ++ more) (uses ++ more_uses)) <> Gt.
Proof.
  intros. apply component_bounds_are_lex_bounds.
  apply generator_counted_prefix_components.
Qed.

Theorem checker_counted_prefix_bound : forall grades more uses more_uses,
  lex_compare (checker_counted_key grades uses)
    (checker_counted_key (grades ++ more) (uses ++ more_uses)) <> Gt.
Proof.
  intros. apply component_bounds_are_lex_bounds.
  apply checker_counted_prefix_components.
Qed.

(* An unresolved dependency has no certified grade. Give it the best possible
   density grade for the direction, and count it in no histogram bucket. This
   is deliberately weak but remains safe while recursive scoring is pending. *)
Definition certified_grade (candidate : option nat) (actual : nat) : Prop :=
  match candidate with
  | Some grade => grade = actual
  | None => True
  end.

Definition optimistic_generator_grade (candidate : option nat) : nat :=
  match candidate with Some grade => grade | None => 4 end.

Definition optimistic_checker_grade (candidate : option nat) : nat :=
  match candidate with Some grade => grade | None => 0 end.

Fixpoint known_grade_count (grade : nat) (candidates : list (option nat)) : nat :=
  match candidates with
  | [] => 0
  | Some actual :: rest =>
      (if Nat.eqb grade actual then 1 else 0) + known_grade_count grade rest
  | None :: rest => known_grade_count grade rest
  end.

Lemma fold_min_monotone : forall lower upper,
  Forall2 le lower upper -> forall low high,
  low <= high ->
  fold_left Nat.min lower low <= fold_left Nat.min upper high.
Proof.
  intros lower upper H; induction H as [|x y xs ys Hxy Htail IH];
    intros low high Hle; simpl; auto.
  apply IH. lia.
Qed.

Lemma fold_max_monotone : forall lower upper,
  Forall2 le lower upper -> forall low high,
  low <= high ->
  fold_left Nat.max lower low <= fold_left Nat.max upper high.
Proof.
  intros lower upper H; induction H as [|x y xs ys Hxy Htail IH];
    intros low high Hle; simpl; auto.
  apply IH. lia.
Qed.

Lemma optimistic_generator_pointwise : forall candidates actual,
  Forall2 certified_grade candidates actual ->
  Forall (fun grade => grade <= 4) actual ->
  Forall2 le actual (map optimistic_generator_grade candidates).
Proof.
  intros candidates actual Hcert.
  induction Hcert as [|candidate grade cs gs Hhead Htail IH];
    intros Hrange; inversion Hrange; subst; simpl; constructor; auto.
  destruct candidate; simpl in *; lia.
Qed.

Lemma optimistic_checker_pointwise : forall candidates actual,
  Forall2 certified_grade candidates actual ->
  Forall2 le (map optimistic_checker_grade candidates) actual.
Proof.
  intros candidates actual Hcert.
  induction Hcert as [|candidate grade cs gs Hhead Htail IH];
    simpl; constructor; auto.
  destruct candidate; simpl in *; lia.
Qed.

Lemma known_count_bound : forall grade candidates actual,
  Forall2 certified_grade candidates actual ->
  known_grade_count grade candidates <= grade_count grade actual.
Proof.
  intros grade candidates actual Hcert.
  induction Hcert as [|candidate actual cs gs Hhead Htail IH]; simpl; auto.
  destruct candidate; simpl in *; subst; lia.
Qed.

Definition generator_certified_key candidates uses :=
  [4 - generator_worst (map optimistic_generator_grade candidates);
   known_grade_count 0 candidates; known_grade_count 1 candidates;
   known_grade_count 2 candidates; known_grade_count 3 candidates;
   known_grade_count 4 candidates; fold_left Nat.add uses 0].

Definition checker_certified_key candidates uses :=
  [checker_worst (map optimistic_checker_grade candidates);
   known_grade_count 4 candidates; known_grade_count 3 candidates;
   known_grade_count 2 candidates; known_grade_count 1 candidates;
   known_grade_count 0 candidates; fold_left Nat.add uses 0].

Theorem unresolved_generator_bound : forall candidates actual future uses future_uses,
  Forall2 certified_grade candidates actual ->
  Forall (fun grade => grade <= 4) actual ->
  Forall2 le (generator_certified_key candidates uses)
    (generator_counted_key (actual ++ future) (uses ++ future_uses)).
Proof.
  intros candidates actual future uses future_uses Hcert Hrange.
  assert (Hknown : forall grade,
    known_grade_count grade candidates <= grade_count grade actual).
  { intro grade. eapply known_count_bound; eauto. }
  unfold generator_certified_key, generator_counted_key.
  repeat constructor;
    try apply variable_use_prefix_bound;
    try (eapply Nat.le_trans;
         [apply Hknown | rewrite grade_count_app; lia]).
  pose proof (optimistic_generator_pointwise _ _ Hcert Hrange) as Hpoint.
  pose proof (fold_min_monotone _ _ Hpoint 4 4 (le_n 4)) as Hmin.
  pose proof (generator_prefix_bound actual future) as Hprefix.
  unfold generator_worst in *.
  pose proof (fold_min_le_start (map optimistic_generator_grade candidates) 4).
  pose proof (fold_min_le_start actual 4).
  lia.
Qed.

Theorem unresolved_checker_bound : forall candidates actual future uses future_uses,
  Forall2 certified_grade candidates actual ->
  Forall2 le (checker_certified_key candidates uses)
    (checker_counted_key (actual ++ future) (uses ++ future_uses)).
Proof.
  intros candidates actual future uses future_uses Hcert.
  assert (Hknown : forall grade,
    known_grade_count grade candidates <= grade_count grade actual).
  { intro grade. eapply known_count_bound; eauto. }
  unfold checker_certified_key, checker_counted_key.
  repeat constructor;
    try apply variable_use_prefix_bound;
    try (eapply Nat.le_trans;
         [apply Hknown | rewrite grade_count_app; lia]).
  pose proof (optimistic_checker_pointwise _ _ Hcert) as Hpoint.
  pose proof (fold_max_monotone _ _ Hpoint 0 0 (le_n 0)) as Hmax.
  pose proof (checker_prefix_bound actual future) as Hprefix.
  unfold checker_worst in *.
  lia.
Qed.

(* Resolving a needed dependency is useful immediately: replacing an unknown
   grade by its exact value can only tighten the partial bound. *)
Definition grade_refines (old new : option nat) : Prop :=
  match old with None => True | Some grade => new = Some grade end.

Lemma refined_generator_grades : forall old new,
  Forall2 grade_refines old new ->
  Forall (fun candidate => match candidate with
          | Some grade => grade <= 4 | None => True end) new ->
  Forall2 le (map optimistic_generator_grade new)
    (map optimistic_generator_grade old).
Proof.
  intros old new Href.
  induction Href as [|old new olds news Hstep Hrest IH];
    intro Hrange; inversion Hrange; subst; simpl; constructor; auto.
  destruct old as [old|], new as [new|]; simpl in *;
    try discriminate; try lia; inversion Hstep; subst; lia.
Qed.

Lemma refined_checker_grades : forall old new,
  Forall2 grade_refines old new ->
  Forall2 le (map optimistic_checker_grade old)
    (map optimistic_checker_grade new).
Proof.
  intros old new Href.
  induction Href as [|old new olds news Hstep Hrest IH];
    simpl; constructor; auto.
  destruct old as [old|], new as [new|]; simpl in *;
    try discriminate; try lia; inversion Hstep; subst; lia.
Qed.

Lemma refined_grade_count : forall grade old new,
  Forall2 grade_refines old new ->
  known_grade_count grade old <= known_grade_count grade new.
Proof.
  intros grade old new Href.
  induction Href as [|old new olds news Hstep Hrest IH]; simpl; auto.
  destruct old as [old|], new as [new|]; simpl in *;
    try discriminate; try lia; inversion Hstep; subst; lia.
Qed.

Theorem resolving_generator_dependency_tightens_bound :
  forall old new uses,
  Forall2 grade_refines old new ->
  Forall (fun candidate => match candidate with
          | Some grade => grade <= 4 | None => True end) new ->
  Forall2 le (generator_certified_key old uses)
    (generator_certified_key new uses).
Proof.
  intros old new uses Href Hrange.
  unfold generator_certified_key.
  repeat constructor;
    try (apply refined_grade_count; exact Href);
    try apply Nat.le_refl.
  pose proof (refined_generator_grades _ _ Href Hrange) as Hpoint.
  pose proof (fold_min_monotone _ _ Hpoint 4 4 (le_n 4)) as Hmin.
  pose proof (fold_min_le_start (map optimistic_generator_grade old) 4).
  pose proof (fold_min_le_start (map optimistic_generator_grade new) 4).
  unfold generator_worst. lia.
Qed.

Theorem resolving_checker_dependency_tightens_bound :
  forall old new uses,
  Forall2 grade_refines old new ->
  Forall2 le (checker_certified_key old uses)
    (checker_certified_key new uses).
Proof.
  intros old new uses Href.
  unfold checker_certified_key.
  repeat constructor;
    try (apply refined_grade_count; exact Href);
    try apply Nat.le_refl.
  pose proof (refined_checker_grades _ _ Href) as Hpoint.
  pose proof (fold_max_monotone _ _ Hpoint 0 0 (le_n 0)) as Hmax.
  unfold checker_worst. lia.
Qed.

Fixpoint producer_count (steps : list bool) : nat :=
  match steps with
  | [] => 0
  | true :: rest => S (producer_count rest)
  | false :: rest => producer_count rest
  end.

Fixpoint check_count (steps : list bool) : nat :=
  match steps with
  | [] => 0
  | true :: rest => check_count rest
  | false :: rest => S (check_count rest)
  end.

(* A producer consumes at least one fresh variable; a check consumes none.
   This transition relation models plain positive direct-variable hypotheses,
   not arbitrary type arguments, forced bindings, or source rewrites. *)
Inductive completion : nat -> list bool -> nat -> Prop :=
| completion_done : forall unbound, completion unbound [] unbound
| completion_check : forall unbound rest final,
    completion unbound rest final ->
    completion unbound (false :: rest) final
| completion_produce : forall unbound next rest final,
    next < unbound -> completion next rest final ->
    completion unbound (true :: rest) final.

Lemma producers_use_fresh_variables : forall unbound steps final,
  completion unbound steps final -> producer_count steps <= unbound.
Proof.
  intros unbound steps final Hrun.
  induction Hrun; simpl; lia.
Qed.

Lemma checks_plus_producers : forall steps,
  check_count steps + producer_count steps = length steps.
Proof.
  induction steps as [|[|] rest IH]; simpl; lia.
Qed.

Lemma remaining_check_bound : forall unbound steps final,
  completion unbound steps final ->
  length steps - unbound <= check_count steps.
Proof.
  intros unbound steps final Hrun.
  pose proof (producers_use_fresh_variables _ _ _ Hrun) as Hproducers.
  pose proof (checks_plus_producers steps) as Htotal.
  lia.
Qed.

Lemma check_count_app : forall prefix suffix,
  check_count (prefix ++ suffix) = check_count prefix + check_count suffix.
Proof.
  induction prefix as [|[|] rest IH]; intros suffix; simpl;
    try rewrite IH; lia.
Qed.

Theorem counted_check_prefix_bound : forall committed remaining unbound final,
  completion unbound remaining final ->
  check_count committed + (length remaining - unbound) <=
  check_count (committed ++ remaining).
Proof.
  intros committed remaining unbound final Hrun.
  rewrite check_count_app.
  pose proof (remaining_check_bound _ _ _ Hrun).
  lia.
Qed.
