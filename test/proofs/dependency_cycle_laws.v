(* A completed dependency traversal is closed under the dependencies it
   actually scored. An unseen later root cannot form a new cycle with it. *)
From Coq Require Import List Lia.
Import ListNotations.

Section DependencyClosure.
  Context {Key : Type}.
  Variable next : Key -> list Key.

  Inductive depends_on : Key -> Key -> Prop :=
  | depends_direct : forall parent child,
      In child (next parent) -> depends_on parent child
  | depends_transitive : forall parent middle child,
      In middle (next parent) ->
      depends_on middle child -> depends_on parent child.

  Definition completed_in (seen : list Key) (root : Key) : Prop :=
    forall child, depends_on root child -> In child seen.

  Theorem completed_key_cannot_gain_unseen_dependency :
    forall seen root later,
      completed_in seen root ->
      ~ In later seen ->
      ~ depends_on root later.
  Proof.
    intros seen root later Hclosed Hunseen Hpath.
    apply Hunseen. apply Hclosed. exact Hpath.
  Qed.

  Theorem unseen_key_cannot_join_completed_cycle :
    forall seen root later,
      completed_in seen root ->
      ~ In later seen ->
      ~ (depends_on root later /\ depends_on later root).
  Proof.
    intros seen root later Hclosed Hunseen [Hforward _].
    eapply completed_key_cannot_gain_unseen_dependency; eauto.
  Qed.
End DependencyClosure.

(* Once every dependency of a key has a smaller rank, deterministic local
   scoring equations have a unique solution. This models the grades marked
   cycle-independent by the plugin, provided its visited edges are complete. *)
Section AcyclicScores.
  Context {Key : Type}.
  Variable next : Key -> list Key.
  Variable rank : Key -> nat.
  Hypothesis rank_decreases : forall parent child,
    In child (next parent) -> rank child < rank parent.
  Variable combine : Key -> list nat -> nat.

  Definition satisfies (score : Key -> nat) : Prop :=
    forall key, score key = combine key (map score (next key)).

  Theorem acyclic_score_unique : forall score1 score2,
    satisfies score1 -> satisfies score2 ->
    forall key, score1 key = score2 key.
  Proof.
    intros score1 score2 Hscore1 Hscore2.
    assert (Hbelow : forall limit key, rank key < limit ->
      score1 key = score2 key).
    { induction limit as [|limit IH]; intros key Hrank; [lia|].
      rewrite Hscore1, Hscore2.
      f_equal.
      apply map_ext_in. intros child Hchild.
      apply IH. specialize (rank_decreases key child Hchild).
      lia. }
    intro key. apply (Hbelow (S (rank key))). lia.
  Qed.
End AcyclicScores.
