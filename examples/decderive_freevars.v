From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.
Open Scope qc_scope.
From Coq Require Import Init.Nat Lia.
Open Scope nat_scope.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

Inductive term :=
| Var : nat -> term
| Abs : nat ->  term -> term
| App : term -> term -> term.
Derive Show for term.
Derive Sized for term.
Derive Arbitrary for term.

Sample (arbitrary : G term).

Inductive elem : nat -> list nat -> Prop :=
| ElemMatch : forall n1 n2 lst,
    n1 = n2 -> elem n1 (n2 :: lst)
| ElemRecur : forall n1 n2 rst,
    elem n1 rst ->
    elem n1 (n2 :: rst).
Derive (DecOpt) for (elem n l).
Derive ArbitrarySizedSuchThat for (fun n => elem n l).
Sample (@arbitrarySizeST _ (fun n => elem n [1;2;3;4;5;6;7]) _ 20).




Inductive closedunder : list nat -> term -> Prop :=
| ClosedVar : forall n ctxt,
    elem n ctxt -> closedunder ctxt (Var n)
| ClosedAbs : forall n body ctxt,
    closedunder (n :: ctxt) body ->
    closedunder ctxt (Abs n body)
| ClosedApp : forall t1 t2 ctxt,
    closedunder ctxt t1 ->
    closedunder ctxt t2 ->
    closedunder ctxt (App t1 t2).
Derive DecOpt for (closedunder lst t).
Derive ArbitrarySizedSuchThat for (fun t => closedunder l t).

Inductive closed : term -> Prop :=
| Closed : forall t, closedunder [] t -> closed t.
Derive DecOpt for (closed t).
Derive ArbitrarySizedSuchThat for (fun t => closed t).

Sample (@arbitrarySizeST _ (fun t => closed t) _ 10).

Inductive tree {a : Type} :=
| Empty : tree
| Node : a -> tree -> tree -> tree.
Derive Show for tree.
Derive Arbitrary for tree.

(* Sample (arbitrary : G (tree)). *)

Section TypeClasses.

  Definition decideOpt : Type := nat -> option bool.

  (* Class decOptSizeMonotonic (decOpt : decideOpt) := *)
  (*   size_mon : forall s1 s2, s1 <= s2 -> decOpt s1 = Some true -> decOpt s2 = Some true. *)

  Class DecOptSizeMonotonic (P : Prop) {H : DecOpt P} :=
    size_mon : forall s1 s2, s1 <= s2 -> decOpt s1 = Some true -> decOpt s2 = Some true.


  (* Class decOptCorrect (P : Prop) (decOpt : decideOpt) := *)
  (*   { sound : forall s, decOpt s = Some true -> P;  *)
  (*     complete : forall s, P -> decOpt s = Some true }. *)

  Class DecOptCorrect (P : Prop) {H : DecOpt P} :=
    { sound : forall s, decOpt s = Some true -> P;
      complete : P -> exists s, decOpt s = Some true }.


  (* Coersions from [Dec] *)

  Global Instance decSizeMonotonic (P : Prop) {_ : Dec P} : DecOptSizeMonotonic P.
  Proof. firstorder. Qed.

  (* Instance DecSizeMonotonic P {_ : Dec P} : @DecOptSizeMonotonic P _ _ := {}. *)

  Global Instance decCorrect (P : Prop) {_ : Dec P} : DecOptCorrect P.
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

  (* Instance DecCorrect  P {_ : Dec P} : @DecOptCorrect P _ _ := {}.   *)

End TypeClasses.


Section ElemProofs.

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

  (* Lemma DecOptle_sound k m n : *)
  (*   @decOpt (le m n) _ k = Some true -> le m n. *)
  (* Proof. *)
  (*   unfold decOpt, dec_decOpt, dec. *)
  (*   destruct DecidableClass.Decidable_le_nat.   *)
  (*   simpl. destruct Decidable_witness; firstorder. *)
  (*   congruence. *)
  (* Qed. *)

  (* XXX fix typeclass *)
  Lemma DecOptle_complete k m n :
    le m n -> @decOpt (le m n) _ k = Some true.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct DecidableClass.Decidable_le_nat. intros Hleq.
    simpl. destruct Decidable_witness; firstorder.
    congruence.
  Qed.

  Check elem.
  Lemma DecOptelem_monotonic k1 k2 n lst:
    k1 <= k2 ->
    @decOpt _ (DecOptelem n lst) k1 = Some true ->
    @decOpt _ (DecOptelem n lst) k2 = Some true.
  Proof.
    revert k2 n lst. induction k1; intros k2 n lst Hleq Hdec.
    - simpl in Hdec.
      (* destruct the second fuel value *)
      destruct k2. 
      + (* if it's zero, it's exactly the same as the Hdec assumption *)
        eassumption.
      + simpl.
        (* otherwise we have:
           Hdec : checker_backtrack checkers1 = Some true,
           for some list of checkers checkers1

           and we have to show that
           checker_backtrack checkers2 = Some true,
           for some list of checkers checkers2.

           (Note: recall the spec of checker_backtrack checker_backtrack_spec)

           But each checker that can return true in checkers1,
           is also in checkers2, therefore we can show the goal *) 
           
      
        (* we apply checker_backtrack_spec in Hdec and we get that one
           of the checkers in checkers1 must return Some true *) 
        eapply checker_backtrack_spec in Hdec.
        destruct Hdec as [f [Hin Heq]].

        (* we apply checker_backtrack_spec in our goal, and
           we must provide a checker in checkers2 that returns Some true *)
        eapply checker_backtrack_spec.

        (* the witness is the checker f in checkers1 that returns Some true *)
        eexists f. split; [| eassumption ].

        (* f is either the first or the second element of checkers1 *) 
        destruct Hin as [H1 | [H2 | [] (* impossible, the rest of the list is empty *) ]].

        (* if its the first element in checkers1, then it's also the first element in checkers2 *) 

        now left; eauto.

        (* if it's the second element in checkers1, it's a contradiction because it always returns None *)
        
        subst. congruence. 
        
    - destruct k2.
      lia.
      (* Again, we have:
         Hdec : checker_backtrack checkers1 = Some true,
         for some list of checkers checkers1

         and we have to show that
         checker_backtrack checkers2 = Some true,
         for some list of checkers checkers2.
         
         Each checker in checkers2, either appears in 
         checkers1 as it is (for the non-inductive cases),
         or it in in checkers1 with a smaller fuel value
         (k1 instead of k2) in recursive calls (for the inductive cases). 
       *)
      

      (* we apply checker_backtrack_spec in Hdec and we get that one
         of the checkers in checkers1 must return Some true *) 
      unfold decOpt, DecOptelem in *. (* to avoid simple because it unfold the recursive call and the the IH does not quite match *)
      
      eapply checker_backtrack_spec in Hdec.
      destruct Hdec as [f [Hin Heq]].

      (* we apply checker_backtrack_spec in our goal, and
         we must provide a checker in checkers2 that returns Some true *)
      eapply checker_backtrack_spec.
      
      (* the witness is the checker f in checkers1 that returns Some true *)
        
      (* f is either the first or the second element of checkers1 *) 
      destruct Hin as [H1 | [H2 | [] (* impossible, the rest of the list is empty *) ]].

      (* if its the first element in checkers1,
         then it's also the first element in checkers2 *) 
        
      eexists. split. now left. subst. eassumption. 
        
      
      (* if it's the second element in checkers1, then the second element of
         checkers2 must return Some true because of the inductive hypothesis *)
        
      subst. eexists. split. right. now left. 
      destruct lst. congruence.
                
      match goal with
      | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
        (* here, ?e is the rec call in the checker in hypothesis Heq.
           I use an Ltac pattern match so that I don't have to copy it
           in order to destruct it.  *)        
          destruct e eqn:Heqb
      end; [ | congruence ].
      destruct b; [ | congruence ].

      (* now Heqb says that the call to aux_arb with fuel k1 retruns Some true.
         Therefore, by the IHk1 the same call with fuel k2 returns Some true *)
      
      eapply IHk1 with (k2 := k2) in Heqb; [ | lia (* k1 <= k2 *)].
      rewrite Heqb. reflexivity.
  Qed.

  Ltac pull :=
    match goal with
    | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
      remember e as x
    end.

  Lemma onlyone : forall {X : Type} (a b : X),
      In a [b] -> a = b.
  Proof.
    intros.
    destruct H eqn:Hin.
    - subst. auto.
    - inversion i.
  Qed.



  Lemma DecOptelem_correct k n lst :
    @decOpt _ (DecOptelem n lst) k = Some true ->
    elem n lst.
  Proof.
    revert lst n. induction k; intros lst n decTrue.
    destruct lst.
    - inversion decTrue.
    - unfold decOpt, DecOptelem in *.
      apply checker_backtrack_spec in decTrue.
      destruct decTrue as [f [Hin Htrue]].
      destruct Hin.
      + subst.
        destruct (@decOpt (n = n0) _ 42) eqn:H; [ | congruence ].
        destruct b; [ | congruence ].
        eapply sound in H.
        subst. now constructor.
      + inversion H.
        * subst. congruence.
        * inversion H0.
    - unfold decOpt, DecOptelem in *.
      apply checker_backtrack_spec in decTrue.
      destruct decTrue as [f [Hin Htrue]].
      destruct Hin; subst.
      + destruct lst. congruence.
        destruct (@decOpt (n = n0) _ 42) eqn:H1;
          [ | congruence ].
        destruct b; [ | congruence ].
        eapply sound in H1. subst. now constructor.
      + apply onlyone in H.
        subst.
        destruct lst; try congruence.
        pull. destruct x; [| congruence].
        destruct b; [|congruence].
        destruct k; destruct n; destruct lst;
          symmetry in Heqx; apply checker_backtrack_spec in Heqx;
            destruct Heqx as [f [Hin Htrue']];
            destruct Hin; try (subst; congruence).
        * destruct H. subst. congruence.
          destruct H.
        * subst.
          destruct (@decOpt (0 = n) _ 42) eqn:Heq; [|congruence].
          destruct b; [|congruence].
          apply sound in Heq. subst.
          apply ElemRecur. now constructor.
        * destruct H. subst. congruence.
          inversion H.
        * destruct H. subst. congruence. inversion H.
        * subst.
          destruct (@decOpt ((S n) = n1) _ 42) eqn:H';
            [|congruence].
          destruct b; [|congruence].
          apply sound in H'. subst.
          apply ElemRecur. now constructor.
        * destruct H. subst. congruence.
          destruct H.
        * destruct H. subst. congruence.
          destruct H.
        * destruct H.
          destruct (@decOpt (0 = n) _ 42) eqn:H';
            [|congruence].
          destruct b;[|congruence].
          apply sound in H'.
          subst. apply ElemRecur. now constructor.
        * destruct H.
          subst.










             





        








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

  Instance decOptbstCorrect m n t : DecOptCorrect (bst m n t).
  Proof.
    constructor.
    - intros. eapply DecOptbst_correct. eassumption.
    - intros. eapply DecOptbst_complete. eassumption.
  Qed.

End BSTProofs.
