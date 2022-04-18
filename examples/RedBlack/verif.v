From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.
Require Import List String Lia.
From QuickChick Require Import QuickChick.
Local Open Scope set_scope.

From QuickChick.RedBlack Require Import redblack testing.

(* correspondence between the inductive and the executable definitions *)
Lemma has_black_height :
  forall t h c, is_redblack' t c h -> black_height_bool t = Some h.
Proof.
  elim => [| c t1 IHt1 n t2 IHt2] h c' Hrb; first by inversion Hrb.
  inversion Hrb as [| n' tl tr h' Htl Htr | c'' n' tl tr h' Htl Htr]; subst;
  move: Htl Htr => /IHt1 Htl /IHt2 Htr; simpl; by rewrite Htl Htr eq_refl.
Qed.

Lemma is_redblack'P :
  forall (t : tree) n c,
    reflect (is_redblack' t c n)
            ((black_height_bool t == Some n) && has_no_red_red c t).
Proof.
  elim => [| c t1 IHt1 n t2 IHt2] n' c'.
  - simpl.
    apply (@iffP ((Some 0 == Some n') && true));
    first by apply/idP.
    + move => /andP [/eqP [H1] _]; subst.
      econstructor.
    + move => Hrb. apply/andP. inversion Hrb; subst. split => //.
  - apply (@iffP ((black_height_bool (Node c t1 n t2) == Some n') &&
                   has_no_red_red c' (Node c t1 n t2)));
    first by apply/idP.
    + move => /andP [/eqP /= H1 H2]; subst.
      destruct (black_height_bool t1) eqn:Heqh1,
               (black_height_bool t2) eqn:Heqh2; (try discriminate).
      have Heq : (n0 = n1) by apply/eqP; destruct (n0 == n1). subst.
      rewrite eq_refl in H1.
      destruct c; inversion H1; subst; clear H1;
      destruct c' => //=; move : H2 => /andP [Ht1 Ht2];
      (constructor; [apply/IHt1 | apply/IHt2]); apply/andP; split => //.
    + move => Hrb.
      inversion Hrb as [| n'' tl tr h Hrbl Hrbr | c'' n'' tl tr h Hrbl Hrbr]; subst;
      move: Hrbl Hrbr => /IHt1/andP [/eqP Hbhl Hrrl] /IHt2/andP [/eqP Hbhr Hrrr];
      apply/andP; split => //; simpl; (try by rewrite Hbhl Hbhr eq_refl);
      by (apply/andP; split => //).
Qed.

(* begin is_redblackP *)
Lemma is_redblackP t : reflect (is_redblack t) (is_redblack_bool t).
(* end is_redblackP *)
Proof.
  apply (@iffP (is_redblack_bool t)); first by apply/idP.
  rewrite /is_redblack_bool.
  + move => /andP [Hb Hrr]. rewrite /is_black_balanced in Hb.
    have [h Hbh] : exists h, black_height_bool t = Some h
      by destruct (black_height_bool t) => //; eexists.
    exists h. apply/is_redblack'P. apply/andP; split => //; apply/eqP => //.
  + move => [h /is_redblack'P /andP [/eqP H1 H2]].
    rewrite /is_redblack_bool /is_black_balanced H1. apply/andP; split => //.
Qed.

(* begin semColor *)
Lemma semColor : semProd genColor <--> [set : color].
(* end semColor *)
Proof.
  rewrite /genColor. rewrite semElements.
  intros c. destruct c; simpl; unfold setT; tauto.
Qed.

Corollary genColor_correctSize': forall s, semProdSize genColor s <--> setT.
Proof.
  move => s. rewrite unsized_alt_def. by apply semColor.
Qed.

Ltac returnSolver :=
  try apply returnGenSizeMonotonic;
  try apply ProducerSemanticsGen.
Instance genRBTree_heightMonotonic p :
  @SizeMonotonic _ _ ProducerGen (genRBTree_height p).
Proof.
  move : p.
  eapply (well_founded_induction well_founded_hc).
  move => [[|n] c] IH; rewrite genRBTree_height_eq.
  - case : c {IH}; returnSolver.
    apply oneofMonotonic; returnSolver.
    move => t [H1 | [H2 | //]]; subst; returnSolver.
    eauto with typeclass_instances.
    apply (@bindMonotonic _ ProducerGen _); eauto with typeclass_instances.
    move => x; returnSolver.
  - case : c IH => IH.
    apply (@liftM4Monotonic); returnSolver.
    + eapply IH; eauto; by constructor; lia.
    + eauto with typeclass_instances.
    + eapply IH; eauto; by constructor; lia.
    + unfold genColor.
      apply bindMonotonic; eauto with typeclass_instances.
      move => x /=. apply liftM4Monotonic; returnSolver; eauto with typeclass_instances.
      * eapply IH; eauto; (case : x; [ by right | by left; lia]).
      * eapply IH; eauto; (case : x; [ by right | by left; lia]).      
Qed.

Instance genRBTreeMonotonic : SizeMonotonic genRBTree.
Proof.
  apply bindMonotonic; eauto with typeclass_instances.
Qed.

(*
(* begin semGenRBTreeHeight *)
Lemma semGenRBTreeHeight h c :
  semProd (genRBTree_height (h, c)) <--> [set t | is_redblack' t c h ].
(* end semGenRBTreeHeight *)
Proof.
  replace c with (snd (h, c)); replace h with (fst (h, c)); try reflexivity.
  move : (h, c). clear h c.
  eapply (well_founded_induction well_founded_hc).
  move => [[|h] []] IH /=; rewrite genRBTree_height_eq.
  - rewrite semReturn. split. move => <-. constructor.
    move => H. inversion H; subst; reflexivity.
  - rewrite semOneof. move => t. split.
    + move => [gen [[H1 | [H1 | // _]] H2]]; subst.
      apply @semReturn in H2.
      * rewrite - H2. constructor.
      * apply ProducerSemanticsGen.
      * move : H2 => .
    move => [n [_ /semReturn <-]].
    constructor. constructor. constructor.
    move => H. inversion H; subst.
    { eexists. split. left. reflexivity. inversion H; subst.
        by apply semThunkGen, semReturn. }
    { inversion H0; subst. inversion H1; subst.
      eexists. split. right. left. reflexivity.
      apply semThunkGen, semBindSizeMonotonic; eauto with typeclass_instances.
      eexists. split; last by apply semReturn; reflexivity.
      by apply arbNat_correct. }
  - rewrite semLiftGen4SizeMonotonic. split.
    + move => /= [c [t1 [n [t2 [/semReturn H1 [H2 [H3 [H4 H5]]]]]]]].
      rewrite <- H1 in *. clear H1. subst.
      apply IH in H2; last by left; lia.
      apply IH in H4; last by left; lia. constructor; eauto.
    + move => H. inversion H; subst.
      apply (IH (h, Black)) in H1; last by left; lia.
      apply (IH (h, Black)) in H4; last by left; lia.
      eexists. eexists. eexists. eexists. repeat (split; auto; try reflexivity).
      by apply semReturn. by auto.
      by apply arbNat_correct. by auto.
  - rewrite semBindSizeMonotonic /=. split.
    + move => [c [_ /= /semLiftGen4SizeMonotonic
                    [c' [t1 [n [t2 [/semReturn H1 [H2 [_ [H4 H5]]]]]]]]]].
      rewrite <- H1 in *. clear H1. subst. destruct c.
      apply IH in H2; last by right.
      apply IH in H4; last by right. simpl in *.
      constructor; eauto.
      apply IH in H2; last by left; lia.
      apply IH in H4; last by left; lia. constructor; eauto.
    + move => H. inversion H; subst.
      apply (IH (h.+1, Red)) in H0; last by right.
      apply (IH (h.+1, Red)) in H1; last by right.
      eexists Red. split; first by apply semColor.
      apply semLiftGen4SizeMonotonic; eauto with typeclass_instances.
      eexists. eexists. eexists. eexists. repeat (split; auto; try reflexivity).
      by apply semReturn. by auto.
      by apply arbNat_correct. by auto.
      apply (IH (h, Black)) in H1; last by left; lia.
      apply (IH (h, Black)) in H4; last by left; lia.
      eexists Black. split; first by apply semColor.
      apply semLiftGen4SizeMonotonic; eauto with typeclass_instances.
      eexists. eexists. eexists. eexists. repeat (split; auto; try reflexivity).
      by apply semReturn. by auto.
      by apply arbNat_correct. by auto.
Qed.


(* begin semRBTree *)
Lemma semRBTree : semGen genRBTree <--> [set t | is_redblack t].
(* end semRBTree *)
Proof.
  rewrite /genRBTree /is_redblack.
  rewrite semBindSizeMonotonic. setoid_rewrite semGenRBTreeHeight.
  move => t. split.
  - move => [n [_ H2]].  eexists; eauto.
  - move => [n H3].  eexists. split; eauto.
    by apply arbNat_correct.
Qed.

(* begin insert_preserves_redblack_checker_correct *)
Lemma insert_preserves_redblack_checker_correct:
  semChecker (insert_preserves_redblack_checker genRBTree)
  <-> insert_preserves_redblack.
(* end insert_preserves_redblack_checker_correct *)
Proof.
  rewrite (mergeForAlls arbitrary genRBTree).
  rewrite -> semForAllUnsized2.
  rewrite /genPair. split.
  - move => H n t irt. specialize (H (n,t)). simpl in H.
    rewrite /semCheckable in H. simpl in H.
    rewrite -> semReturnGen in H.
    unfold insert_preserves_redblack.
    { 
    apply semCheckableBool in H; eauto.
    destruct (is_redblack_bool t) eqn:Hyp; simpl in *; try congruence.
    + apply /is_redblackP; auto.
    + move: irt. move => /is_redblackP irt. congruence.
    + apply semLiftGen2SizeMonotonic; eauto with typeclass_instances.
      exists (n, t). split => //. split => //. by apply arbNat_correct.
        by apply semRBTree.
    } 
  - move => H [a t] /semLiftGen2SizeMonotonic [[n t'] [[_ Hg] [<- <-]]].
    simpl.
    rewrite semCheckableBool.
    unfold insert_preserves_redblack in H.
    specialize (H n t').
    destruct (is_redblack_bool t') eqn:Hyp.
    + simpl; move: Hyp => /is_redblackP Hyp. apply H in Hyp. apply /is_redblackP; auto.
    + simpl; auto.
  - simpl. eauto with typeclass_instances.
Qed.

(*
Lemma insert_preserves_redblack_checker_correct' :
  semChecker (insert_preserves_redblack_checker genRBTree)
  <-> insert_preserves_redblack.
Proof.
  rewrite /insert_preserves_redblack_checker /insert_preserves_redblack.
  rewrite -> semForAllSizeMonotonic; try by eauto with typeclass_instances.
  - split.
    + move => H n t irt.
      have HH : semGen arbitrary n by (apply arbNat_correct; reflexivity).
      specialize (H n HH).
      rewrite -> semForAllSizeMonotonic in H;
        try by (try move => ? /=); auto with typeclass_instances.
      specialize (H t).
      rewrite -> (semRBTree t) in H. simpl in H. specialize (H irt).
      rewrite -> semImplication in H. apply /is_redblackP.
      rewrite -> semCheckableBool in H. apply H. by apply /is_redblackP.
    + move => H a _ /=. rewrite -> semForAllSizeMonotonic;
        try by (try move => ? /=); auto with typeclass_instances.
      move => t Hg. rewrite -> semImplication => Hrb.
      rewrite semCheckableBool. apply /is_redblackP; apply H.
        by apply /is_redblackP.
  - move => n /=. apply forAllMonotonic;
      try by (try move => ? /=); auto with typeclass_instances.
Qed.
*)
*)
