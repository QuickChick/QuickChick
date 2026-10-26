(* Scoring policies with proved pruning bounds.

   [fold_policy] scores a schedule by combining its step scores in an
   ordered monoid; [lex_policy] compares two policies' scores
   lexicographically. Both come with proofs that their bounds are
   admissible, so the plugin prunes with them, and both declare how their
   scores combine over independent hypothesis groups. *)
From Coq Require Import List Arith Lia.
From QuickChick Require Import SchedulingPolicy.
Import ListNotations.

Set Universe Polymorphism.

(* A total preorder with a monotone combination whose unit is neutral.
   Lower is better. *)
Record ordered_monoid (S : Type) := {
  m_compare : S -> S -> comparison;
  m_unit : S;
  m_combine : S -> S -> S;
  m_le a b := m_compare a b <> Gt;
  m_refl : forall a, m_le a a;
  m_trans : forall a b c, m_le a b -> m_le b c -> m_le a c;
  m_mono : forall a a' b b', m_le a a' -> m_le b b' -> m_le (m_combine a b) (m_combine a' b');
  m_unit_right : forall a, m_le a (m_combine a m_unit)
}.
Arguments m_compare {S} _ _ _.
Arguments m_unit {S} _.
Arguments m_combine {S} _ _ _.
Arguments m_le {S} _ _ _.
Arguments m_refl {S} _ _.
Arguments m_trans {S} _ {_ _ _} _ _.
Arguments m_mono {S} _ {_ _ _ _} _ _.
Arguments m_unit_right {S} _ _.

Section FoldPolicy.
  Variable S : Type.
  Variable M : ordered_monoid S.

  (* A step's score may depend on the steps before it, as variable uses do,
     and is never better than the unit. *)
  Record step_scorer := {
    step_score : score_context S -> list step_view -> step_view -> density -> S;
    step_above_unit : forall ctx prev step grade, m_le M (m_unit M) (step_score ctx prev step grade)
  }.

  (* Optionally, a score every positive check reaches, so that the remaining
     hypotheses which must become checks count in the bound. *)
  Record check_floor (f : step_scorer) := {
    floor_score : score_context S -> S;
    floor_below_checks : forall ctx prev source grade,
      m_le M (floor_score ctx) (step_score f ctx prev (CheckStep source true) grade)
  }.

  Variable f : step_scorer.
  Variable floor : option (check_floor f).

  Fixpoint step_scores ctx (prev : list step_view) (steps : list (step_view * density)) : list S :=
    match steps with
    | [] => []
    | (step, grade) :: rest => step_score f ctx prev step grade :: step_scores ctx (prev ++ [step]) rest
    end.

  Definition combine_all (start : S) (xs : list S) : S := fold_left (m_combine M) xs start.

  (* The score of a committed step, or the unit when its grade may change. *)
  Fixpoint committed_scores ctx (prev : list step_view) (steps : list committed_step) : list S :=
    match steps with
    | [] => []
    | c :: rest =>
      (if committed_certain c
       then step_score f ctx prev (committed_view c) (committed_grade c)
       else m_unit M) :: committed_scores ctx (prev ++ [committed_view c]) rest
    end.

  Definition forced_scores ctx (node : search_node_view) : list S :=
    match floor with
    | Some h => repeat (floor_score f h ctx) (node_forced_checks node)
    | None => []
    end.

  Definition fold_bound (ctx : score_context S) (node : search_node_view) : S :=
    combine_all (combine_all (m_unit M) (committed_scores ctx [] (node_steps node)))
      (forced_scores ctx node).

  Definition fold_scorer : scorer S := {|
    score_step := fun ctx step grade => step_score f ctx [] step grade;
    score_schedule := fun ctx schedule _ =>
      combine_all (m_unit M) (step_scores ctx [] (schedule_steps schedule));
    score_leaf := fun _ _ xs => combine_all (m_unit M) (map snd xs);
    score_inductive := fun _ _ xs => combine_all (m_unit M) (map snd xs);
    compare_scores := m_compare M
  |}.

  (* Combining one more step score never improves a score. *)
  Lemma worse_with_step : forall a b s, m_le M a b -> m_le M (m_unit M) s -> m_le M a (m_combine M b s).
  Proof.
    intros a b s Hab Hs.
    apply (m_trans M Hab), (m_trans M (m_unit_right M b)), (m_mono M (m_refl M b) Hs).
  Qed.

  Lemma combine_all_mono : forall xs ys a b,
    Forall2 (m_le M) xs ys -> m_le M a b -> m_le M (combine_all a xs) (combine_all b ys).
  Proof.
    intros xs ys a b H. revert a b. unfold combine_all.
    induction H; intros a b Hab; simpl; [exact Hab|].
    apply IHForall2, (m_mono M Hab H).
  Qed.

  Lemma step_scores_app : forall ctx prev xs ys,
    step_scores ctx prev (xs ++ ys) =
    step_scores ctx prev xs ++ step_scores ctx (prev ++ map fst xs) ys.
  Proof.
    intros ctx prev xs. revert prev.
    induction xs as [|[step grade] xs IH]; intros prev ys; simpl.
    - now rewrite app_nil_r.
    - now rewrite IH, <- app_assoc.
  Qed.

  (* A kept step has its committed step's view and predecessors, and its
     grade when that is certain, so it scores no better than the bound
     assumes. *)
  Lemma committed_no_better : forall ctx prev committed kept_steps,
    Forall2 kept committed kept_steps ->
    Forall2 (m_le M) (committed_scores ctx prev committed) (step_scores ctx prev kept_steps)
    /\ map fst kept_steps = map committed_view committed.
  Proof.
    intros ctx prev committed kept_steps H. revert prev.
    induction H as [|c [step grade] committed kept_steps Hkept _ IH]; intros prev.
    - split; constructor.
    - destruct Hkept as [Hview Hgrade]. simpl in Hview, Hgrade. subst step. simpl.
      destruct (IH (prev ++ [committed_view c])) as [Hle Hmap].
      split; [|now rewrite Hmap]. constructor; [|exact Hle].
      destruct (committed_certain c); [rewrite Hgrade by reflexivity; apply (m_refl M)|].
      apply (step_above_unit f).
  Qed.

  (* Further steps never make a score better. *)
  Lemma extension_worse : forall ctx extension prev a b,
    m_le M a b -> m_le M a (combine_all b (step_scores ctx prev extension)).
  Proof.
    intros ctx extension. unfold combine_all.
    induction extension as [|[step grade] extension IH]; intros prev a b Hab; simpl; [exact Hab|].
    apply IH, worse_with_step; [exact Hab | apply (step_above_unit f)].
  Qed.

  (* The extension's checks dominate the forced scores; its other steps only
     make the combination worse. *)
  Lemma extension_no_better : forall ctx node extension prev a b,
    node_forced_checks node <= count_checks extension -> m_le M a b ->
    m_le M (combine_all a (forced_scores ctx node))
           (combine_all b (step_scores ctx prev extension)).
  Proof.
    intros ctx node extension prev a b Hk Hab. unfold forced_scores.
    destruct floor as [h|]; [|apply extension_worse; exact Hab].
    unfold count_checks, combine_all in *. revert prev a b Hk Hab.
    generalize (node_forced_checks node) as k.
    induction extension as [|[step grade] extension IH]; intros k prev a b Hk Hab; simpl in *.
    - destruct k; [exact Hab | inversion Hk].
    - destruct (is_check step) eqn:Hcheck; simpl in Hk; [destruct k as [|k]|].
      + apply (IH 0); [lia|]. apply worse_with_step; [exact Hab | apply (step_above_unit f)].
      + simpl. apply IH; [exact (le_S_n _ _ Hk)|]. apply (m_mono M Hab).
        destruct step as [| |source [|]| |]; try discriminate. apply (floor_below_checks f h).
      + apply IH; [exact Hk|]. apply worse_with_step; [exact Hab | apply (step_above_unit f)].
  Qed.

  Theorem fold_bound_admissible : bound_admissible fold_scorer fold_bound.
  Proof.
    intros ctx node s (kept_steps & extension & Hkept & Hsteps & Hforced & _).
    unfold score_one_schedule, fold_bound; simpl.
    rewrite Hsteps, step_scores_app. unfold combine_all at 3. rewrite fold_left_app.
    destruct (committed_no_better ctx [] _ _ Hkept) as [Hle Hmap].
    apply extension_no_better; [exact Hforced|].
    apply combine_all_mono; [exact Hle | apply (m_refl M)].
  Qed.

  (* A sum is [Additive]; a maximum or minimum [Extremal]. *)
  Definition fold_policy (kind : field_kind) : policy := {|
    score_type := S;
    policy_scorer := fold_scorer;
    lower_bound := fold_bound;
    policy_grouping := Some {| group_unit := m_unit M; group_combine := m_combine M;
                               group_fields := [(kind, m_compare M)] |};
    policy_bound_sound := Some fold_bound_admissible
  |}.
End FoldPolicy.

Arguments fold_policy {S} M f floor kind.

(* Pruning with an admissible bound is safe: if the best schedule found so
   far is no worse than a node's bound, it is no worse than every schedule
   below the node. *)
Corollary prune_safe {S} (M : ordered_monoid S) (f : step_scorer S M) floor ctx node s incumbent :
  completes node s ->
  m_le M incumbent (fold_bound S M f floor ctx node) ->
  m_le M incumbent (score_one_schedule (fold_scorer S M f) ctx s).
Proof.
  intros Hs Hb. exact (m_trans M Hb (fold_bound_admissible S M f floor ctx node s Hs)).
Qed.

Section Lex.
  Variables A B : Type.

  Definition map_state {X Y} (g : X -> Y) (state : dependency_state X) : dependency_state Y :=
    match state with
    | SuppliedInstance => SuppliedInstance
    | Pending => Pending
    | InProgress => InProgress
    | Completed x => Completed (g x)
    end.

  (* A pair policy shows each component its own part of dependency scores. *)
  Definition map_context {X Y} (g : X -> Y) (ctx : score_context X) : score_context Y := {|
    current_spec := current_spec ctx;
    locals := locals ctx;
    original_inputs := original_inputs ctx;
    dependencies := map (fun '(spec, state) => (spec, map_state g state)) (dependencies ctx)
  |}.

  Definition lex_compare (ca : A -> A -> comparison) (cb : B -> B -> comparison)
      (x y : A * B) : comparison :=
    match ca (fst x) (fst y) with Eq => cb (snd x) (snd y) | c => c end.

  Variable p : scorer A.
  Variable q : scorer B.

  Definition lex_scorer : scorer (A * B) := {|
    score_step := fun ctx step grade =>
      (score_step p (map_context fst ctx) step grade,
       score_step q (map_context snd ctx) step grade);
    score_schedule := fun ctx schedule _ =>
      (score_one_schedule p (map_context fst ctx) schedule,
       score_one_schedule q (map_context snd ctx) schedule);
    score_leaf := fun ctx leaf xs =>
      (score_leaf p (map_context fst ctx) leaf (map (fun '(n, x) => (n, fst x)) xs),
       score_leaf q (map_context snd ctx) leaf (map (fun '(n, x) => (n, snd x)) xs));
    score_inductive := fun ctx ind xs =>
      (score_inductive p (map_context fst ctx) ind (map (fun '(l, x) => (l, fst x)) xs),
       score_inductive q (map_context snd ctx) ind (map (fun '(l, x) => (l, snd x)) xs));
    compare_scores := lex_compare (compare_scores p) (compare_scores q)
  |}.

  Variable bp : score_context A -> search_node_view -> A.
  Variable bq : score_context B -> search_node_view -> B.

  Definition lex_bound ctx node : A * B :=
    (bp (map_context fst ctx) node, bq (map_context snd ctx) node).

  Theorem lex_bound_admissible :
    bound_admissible p bp -> bound_admissible q bq ->
    bound_admissible lex_scorer lex_bound.
  Proof.
    intros Hp Hq ctx node s Hs.
    specialize (Hp (map_context fst ctx) node s Hs).
    specialize (Hq (map_context snd ctx) node s Hs).
    unfold no_worse, score_one_schedule in *; simpl; unfold lex_compare, lex_bound; simpl.
    destruct (compare_scores p _ _); [exact Hq | discriminate | contradiction].
  Qed.
End Lex.

Definition project_fields {X Y} (g : Y -> X) (fields : list (field_kind * (X -> X -> comparison))) :=
  map (fun '(kind, c) => (kind, fun a b => c (g a) (g b))) fields.

Definition lex_grouping {A B} (ga : grouping A) (gb : grouping B) : grouping (A * B) := {|
  group_unit := (group_unit ga, group_unit gb);
  group_combine := fun x y => (group_combine ga (fst x) (fst y), group_combine gb (snd x) (snd y));
  group_fields := project_fields fst (group_fields ga) ++ project_fields snd (group_fields gb)
|}.

(* [p] first, then [q]. The bound is proved when both bounds are; grouping
   is kept when both policies group. *)
Definition lex_policy (p q : policy) : policy := {|
  score_type := score_type p * score_type q;
  policy_scorer := lex_scorer _ _ (policy_scorer p) (policy_scorer q);
  lower_bound := lex_bound _ _ (lower_bound p) (lower_bound q);
  policy_grouping :=
    match policy_grouping p, policy_grouping q with
    | Some gp, Some gq => Some (lex_grouping gp gq)
    | _, _ => None
    end;
  policy_bound_sound :=
    match policy_bound_sound p, policy_bound_sound q with
    | Some hp, Some hq => Some (lex_bound_admissible _ _ _ _ _ _ hp hq)
    | _, _ => None
    end
|}.

(* Natural-number scores combined by maximum or by sum. *)

Definition nat_max : ordered_monoid nat.
Proof.
  refine {| m_compare := Nat.compare; m_unit := 0; m_combine := Nat.max |};
    intros; repeat rewrite Nat.compare_gt_iff in *; lia.
Defined.

Definition nat_sum : ordered_monoid nat.
Proof.
  refine {| m_compare := Nat.compare; m_unit := 0; m_combine := Nat.add |};
    intros; repeat rewrite Nat.compare_gt_iff in *; lia.
Defined.

(* Proves order goals over [nat_max] and [nat_sum] scores. *)
Ltac nat_order := unfold m_le in *;
  cbn [m_compare m_unit m_combine nat_max nat_sum] in *;
  repeat rewrite Nat.compare_gt_iff in *; lia.

(* A natural-number step score is never below 0. *)
Lemma nat_above_zero (M : ordered_monoid nat) (n : nat) :
  m_compare M = Nat.compare -> m_unit M = 0 -> m_le M (m_unit M) n.
Proof. intros Hc Hu. unfold m_le. rewrite Hc, Hu. destruct n; discriminate. Qed.

(* The engine's variable uses, summed. Its bound counts the committed steps'
   uses, which depend only on their views, plus the further uses every
   schedule below the node incurs. *)
Section Uses.
  Definition committed_uses (node : search_node_view) : nat :=
    uses_after [] (map (fun c => (committed_view c, committed_grade c)) (node_steps node)).

  Definition uses_scorer : scorer nat := {|
    score_step := fun _ step _ => step_uses [] step;
    score_schedule := fun _ schedule _ => uses_after [] (schedule_steps schedule);
    score_leaf := fun _ _ xs => fold_left Nat.add (map snd xs) 0;
    score_inductive := fun _ _ xs => fold_left Nat.add (map snd xs) 0;
    compare_scores := Nat.compare
  |}.

  Definition uses_bound (_ : score_context nat) (node : search_node_view) : nat :=
    committed_uses node + node_future_uses node.

  Lemma uses_after_app : forall prev xs ys,
    uses_after prev (xs ++ ys) = uses_after prev xs + uses_after (prev ++ map fst xs) ys.
  Proof.
    intros prev xs. revert prev.
    induction xs as [|[step grade] xs IH]; intros prev ys; simpl.
    - now rewrite app_nil_r.
    - rewrite IH, <- app_assoc. simpl. lia.
  Qed.

  (* Uses depend on step views only, so kept steps have the committed uses. *)
  Lemma kept_uses : forall prev committed kept_steps,
    Forall2 kept committed kept_steps ->
    uses_after prev kept_steps =
      uses_after prev (map (fun c => (committed_view c, committed_grade c)) committed)
    /\ map fst kept_steps = map committed_view committed.
  Proof.
    intros prev committed kept_steps H. revert prev.
    induction H as [|c [step grade] committed kept_steps [Hview _] _ IH]; intros prev;
      simpl in *; [split; reflexivity|].
    subst step. destruct (IH (prev ++ [committed_view c])) as [Hu Hm].
    split; [now rewrite Hu | now rewrite Hm].
  Qed.

  Theorem uses_bound_admissible : bound_admissible uses_scorer uses_bound.
  Proof.
    intros ctx node s (kept_steps & extension & Hkept & Hsteps & _ & Hfuture).
    unfold no_worse, score_one_schedule, uses_bound, committed_uses; simpl.
    rewrite Hsteps, uses_after_app.
    destruct (kept_uses [] _ _ Hkept) as [Hu Hm]. rewrite Hu, Hm. simpl.
    intro H. apply Nat.compare_gt_iff in H. lia.
  Qed.
End Uses.

(* Fewer variable uses first; a sum, so additive over groups. *)
Definition uses_policy : policy := {|
  score_type := nat;
  policy_scorer := uses_scorer;
  lower_bound := uses_bound;
  policy_grouping := Some {| group_unit := 0; group_combine := Nat.add;
                             group_fields := [(Additive, Nat.compare)] |};
  policy_bound_sound := Some uses_bound_admissible
|}.
