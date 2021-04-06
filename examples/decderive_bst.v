From Coq Require Import Init.Nat Lia.
From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.
Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.

Inductive tree :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.
Derive Show for tree.
Derive Arbitrary for tree.

Derive ArbitrarySizedSuchThat for (fun n => le n n').
Derive ArbitrarySizedSuchThat for (fun n' => le n n').

Inductive bst : nat -> nat -> tree -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node n t1 t2).

(* Derive DecOpt for (le n m). *)
Derive DecOpt for (bst min max t).

Derive ArbitrarySizedSuchThat for (fun b => bst min max b).


Compute (sample (@arbitrarySizeST _ (fun t => bst 0 30 t) _ 10)).


Conjecture expand_range : forall t,
    bst 0 30 t ->
    bst 0 40 t.
QuickChick expand_range.
Conjecture contract_range : forall t,
    bst 0 30 t ->
    bst 0 1 t.
QuickChick expand_range.
(* this shouldn't work *)

Fixpoint insert t x :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node a l r =>
    if a <= x ? then
      Node x (insert l x) r
    else
      Node x r (insert r x)
  end.


Inductive inrange : nat -> nat -> tree -> nat -> Prop :=
| InRange : forall t n max x,
    le n max ->
    bst 0 max t ->
    le x max ->
    inrange n max t x.
Derive DecOpt for (inrange n m t x).
Derive ArbitrarySizedSuchThat for (fun n => inrange n m t x).


(* Testing here doesn't work *)
(* Conjecture insert_invariant : *)
(*   forall t, *)
(*     inrange 30 30 t 30 -> *)
(*     bst 0 30 t. *)
(* QuickChick insert_invariant. *)


Section BSTProofs.


  Ltac inv H := inversion H; subst.

  Lemma checker_backtrack_spec l :
    checker_backtrack l = Some true <->
    exists f, List.In f l /\ f tt = Some true.
  Proof.
    unfold checker_backtrack. generalize false at 2.
    induction l.
    - intros b. destruct b; split; try (intros; congruence).
      * intros H. inv H. inv H0. inv H1.
      * intros H. inv H. inv H0. inv H1.
    - intros b. split.
      + intros H.
        destruct (a tt) eqn:Hdec.
        * destruct b0. exists a. split; eauto. now left.
          eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
        * eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
      + intros H. inv H. inv H0. inv H1. rewrite H2. reflexivity.
        destruct (a tt). destruct b0. reflexivity.
        * eapply IHl. eexists. split; eauto.
        * eapply IHl. eexists. split; eauto.
  Qed.

  (* Generalize instance DecOpt from Decidable *)

  Lemma DecOptle_sound k m n :
    @decOpt (le m n) _ k = Some true -> le m n.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct DecidableClass.Decidable_le_nat.  
    simpl. destruct Decidable_witness; firstorder.
    congruence.
  Qed.

  Lemma DecOptle_complete k m n :
    le m n -> @decOpt (le m n) _ k = Some true.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct DecidableClass.Decidable_le_nat. intros Hleq. 
    simpl. destruct Decidable_witness; firstorder.
    congruence.
  Qed.
  
  
  Lemma DecOptbst_correct k m n t :
    @decOpt _ (DecOptbst m n t) k = Some true ->
    bst m n t.
  Proof.
    revert m n t. induction k; intros m n t Hdec.
    + destruct t. now constructor.
      inversion Hdec.
    + unfold decOpt, DecOptbst in *.
      eapply checker_backtrack_spec in Hdec.
      destruct Hdec as [f [Hin Htrue]]. destruct Hin; subst.
      * destruct t. now constructor. congruence.
      * destruct H; subst; [ | contradiction ]. 
        destruct t. congruence.      

        destruct (@decOpt (m <= n) _ 42) eqn:Hdle; [ | congruence ].
        destruct b; [ | congruence ].
        
        destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'; [ | congruence ].
        destruct b; [ | congruence ].

        destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''; [ | congruence ].
        destruct b; [ | congruence ].

        eapply DecOptle_sound in Hdle.
        eapply DecOptle_sound in Hdle'.
        eapply DecOptle_sound in Hdle''.

        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          remember e as x
        end.
        destruct x eqn:Hdec; [ | congruence ].
        destruct b; [ | congruence ].

        constructor. eassumption. eassumption. eassumption.
        
        now eapply IHk; eauto.

        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          remember e as y
        end.
        destruct y eqn:Hdec'; [ | congruence ].
        destruct b; [ | congruence ].

        now eapply IHk; eauto.

  Qed.

  Lemma DecOptbst_monotonic k1 k2 m n t:
    k1 <= k2 ->
    @decOpt _ (DecOptbst m n t) k1 = Some true ->
    @decOpt _ (DecOptbst m n t) k2 = Some true.
  Proof.
    revert k2 m n t. induction k1; intros k2 m n t Hleq Hdec.
    - simpl in Hdec. destruct t; inv Hdec.
      destruct k2; simpl. eassumption.
      eapply checker_backtrack_spec.
      eexists. split. now left. reflexivity.
    - destruct k2; try lia.
      unfold decOpt, DecOptbst in *. 
      eapply checker_backtrack_spec in Hdec.
      destruct Hdec as [f [[H1 | [ H2 | [] ]] H3]].
      destruct t; subst; try congruence.

      + eapply checker_backtrack_spec.
        eexists. split. now left. reflexivity.

      + subst. destruct t; try congruence.

        eapply checker_backtrack_spec.
        eexists. split. right. now left.
        
        destruct (@decOpt (m <= n) _ 42) eqn:Hdle; [ | congruence ].
        destruct b; [ | congruence ].
        
        destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'; [ | congruence ].
        destruct b; [ | congruence ].

        destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''; [ | congruence ].
        destruct b; [ | congruence ].

        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          destruct e eqn:Heqb
        end; [ | congruence ].
        destruct b; [ | congruence ]. 
        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          destruct e eqn:Heqb'
        end; [ | congruence ].
        destruct b; [ | congruence ].       
        rewrite IHk1. rewrite IHk1.
        reflexivity. lia. eassumption. lia. eassumption.
  Qed.  
  

  Lemma DecOptbst_complete m n t :
    bst m n t ->
    exists k, @decOpt _ (DecOptbst m n t) k = Some true.
  Proof.
    intros H. induction H.
    - exists 0. reflexivity.
    - destruct IHbst1 as [k1 IH1].
      destruct IHbst2 as [k2 IH2].    
      exists (S (Nat.max k1 k2)).
      unfold decOpt, DecOptbst.
      eapply checker_backtrack_spec.
      eexists.
      split. right. now left.
      erewrite !DecOptle_complete; eauto.

      assert (Hmax1 : @decOpt (bst min n t1) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      assert (Hmax2 : @decOpt (bst n max t2) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      unfold decOpt, DecOptbst in Hmax1, Hmax2. 
      rewrite Hmax1, Hmax2.

      reflexivity.
  Qed.
  
End BSTProofs.
