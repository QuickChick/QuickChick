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


Section TypeClasses.
    
  Class DecOptSizeMonotonicPos (P : Prop) {H : DecOpt P} :=
    size_mon : forall s1 s2, s1 <= s2 -> decOpt s1 = Some true -> decOpt s2 = Some true.
  
  Class DecOptSizeMonotonicNeg (P : Prop) {H : DecOpt P} :=
    size_mon' : forall s1 s2, s1 <= s2 -> decOpt s1 = Some false -> decOpt s2 = Some false.
  

  Class DecOptDecidable (P : Prop) {H : DecOpt P} :=
    { wit : exists s a, decOpt s = Some a }.

  Class DecOptCorrectPos (P : Prop) {H : DecOpt P} :=
    { sound : forall s, decOpt s = Some true -> P; 
      complete : P -> exists s, decOpt s = Some true }.

  Class DecOptCorrectNeg (P : Prop) {H : DecOpt P} :=
    { sound' : forall s, decOpt s = Some false -> ~ P; 
      complete' :~ P -> exists s, decOpt s = Some false }.

  
  (* Coersions from [Dec] *)
  
  Global Instance decSizeMonotonicPos (P : Prop) {_ : Dec P} : DecOptSizeMonotonicPos P.
  Proof. firstorder. Qed.

  Global Instance decSizeMonotonicNeg (P : Prop) {_ : Dec P} : DecOptSizeMonotonicNeg P.
  Proof. firstorder. Qed.

  
  Global Instance decCorrectPos (P : Prop) {_ : Dec P} : DecOptCorrectPos P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      destruct dec. now firstorder. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      exists 0. 
      destruct dec. now firstorder. congruence.
  Qed.

  Global Instance decCorrectNeg (P : Prop) {_ : Dec P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      destruct dec. now firstorder. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      exists 0. 
      destruct dec. now firstorder. congruence.
  Qed.

  Global Instance decOptCorrectNeg (P : Prop) {H : DecOpt P}
         {Hmonp : DecOptSizeMonotonicPos P} 
         {Hmonn : DecOptSizeMonotonicNeg P}
         {Hdec : DecOptDecidable P}
         {Hcor : DecOptCorrectPos P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s Hopt. intros HP. eapply Hcor in HP.
      destruct HP.
      edestruct (Compare_dec.le_lt_dec s x).
      + eapply Hmonn in Hopt; eauto. congruence.
      + eapply Hmonp in H0.
        2:{ eapply PeanoNat.Nat.lt_le_incl. eassumption. } congruence.
    - intros Hn.
      destruct Hdec. destruct wit0 as [s [a Hopt]].
      destruct a; eauto.
      eapply Hcor in Hopt. contradiction. 
  Qed.


  Inductive wf_list : list nat -> Prop :=
  | lnil : wf_list nil
  | lcons :
      forall l,
        wf_list l -> wf_list l.

  Derive DecOpt for (wf_list l).
  
  
  
End TypeClasses.


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

  Lemma checker_backtrack_spec_false l :
    checker_backtrack l = Some false <->
    (forall f, List.In f l -> f tt = Some false).
  Proof.
    unfold checker_backtrack.
    induction l.
    - split; eauto. intros Heq; intros f Hin; inv Hin.
    - destruct (a tt) eqn:Hdec.
      * destruct b.
        -- split; try congruence.
           intros Hin.
           assert (Hc : a tt = Some false).
           { eapply Hin. now left. } congruence.
        -- split.
           ++ intros Haux f Hin. inv Hin; eauto.
              eapply IHl; eauto.
           ++ intros Hin. eapply IHl. intros.
              eapply Hin. now right. 
      * split.
        -- intros H1 f Hin.
           exfalso. 
           revert H1. clear. intros H1; induction l.
           congruence.
           destruct (a tt).
           ++ destruct b. congruence. eauto.
           ++ eauto.
        -- intros Hall. 
           assert (Hc : a tt = Some false).
           { eapply Hall. now left. } congruence.
  Qed.

  Lemma DecOptle_complete k m n :
    le m n -> @decOpt (le m n) _ k = Some true.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct DecidableClass.Decidable_le_nat. intros Hleq.
    simpl. destruct Decidable_witness; firstorder.
    congruence.
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

  Instance decOptbstSizeMonotonic m n t : DecOptSizeMonotonicPos (bst m n t).
  Proof. intro; intros. eapply DecOptbst_monotonic; eauto. Qed.

  Lemma DecOptbst_monotonic_neg k1 k2 m n t:
    k1 <= k2 ->
    @decOpt _ (DecOptbst m n t) k1 = Some false ->
    @decOpt _ (DecOptbst m n t) k2 = Some false.
  Proof.
    revert k2 m n t. induction k1; intros k2 m n t Hleq Hdec.
    - simpl in Hdec. destruct t; inv Hdec.
    - destruct k2; try lia. 
      unfold decOpt, DecOptbst in *.
      assert (Hf := proj1 (checker_backtrack_spec_false _) Hdec). 
      eapply checker_backtrack_spec_false.
      intros f Hin. inv Hin.
      + destruct t; eauto.
      + inv H; eauto.
  Abort.

  Instance decOptbstSizeMonotonicPos m n t : DecOptSizeMonotonicPos (bst m n t).
  Proof. intro; intros. eapply DecOptbst_monotonic; eauto. Qed.

  
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
        
        eapply sound in Hdle.
        eapply sound in Hdle'.
        eapply sound in Hdle''.

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

  Instance decOptbstCorrect m n t : DecOptCorrectPos (bst m n t).
  Proof.
    constructor.
    - intros. eapply DecOptbst_correct. eassumption.
    - intros. eapply DecOptbst_complete. eassumption.
  Qed.
  
End BSTProofs.
