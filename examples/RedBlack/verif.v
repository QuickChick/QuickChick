Require Import ssreflect ssrnat ssrbool eqtype. 
Require Import List String.
Require Import QuickChick.
Import GenLow GenHigh.

Require Import redblack.
Require Import testing.

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

Lemma semColor : semGen genColor <--> [set : color].
Proof.
  rewrite /genColor. rewrite semElements.
  intros c. destruct c; simpl; unfold setT; tauto.
Qed.

(* This just says that genColor works the same irrespective of size;
   I'm still currious why we needed this,
   Just for being called from a sized generator?
   Q: Can't we move from semGenSize back to semGen for a generator
      that doesn't use the size at all?
   A (partial): See below how this would look for genColor. *)
(* begin semColorSize *)
Lemma semColorSize s : semGenSize genColor s <--> [set : color].
(* end semColorSize *)
Proof.
  rewrite unsized_alt_def. by apply semColor.
Qed.

Corollary genColor_correctSize': forall s, semGenSize genColor s <--> setT.
Proof.
  move => s. rewrite unsized_alt_def. by apply semColor.
Qed.

(* TODO : move to GenHigh *)
Program Instance oneofMonotonic {A} (x : G A) (l : list (G A))
        `{ SizeMonotonic _ x} `(l \subset SizeMonotonic) 
: SizeMonotonic (oneof x l). 
Next Obligation.
  rewrite !semOneofSize. elim : l H0 => [_ | g gs IH /subconsset [H2 H3]] /=.
  - by apply monotonic_def.
  - specialize (IH H3). move => a [ga [[Hga | Hga] Hgen]]; subst.
    exists ga. split => //. left => //.
    eapply monotonic_def; eauto. exists ga.
    split. right => //.
    apply H3 in Hga. by apply (monotonic_def H1). 
Qed.

Program Instance liftGen4Monotonic {A B C D E} 
        (f : A -> B -> C -> D -> E)
        (g1 : G A) (g2 : G B) (g3 : G C) (g4 : G D) 
        `{ SizeMonotonic _ g1} `{ SizeMonotonic _ g2}
        `{ SizeMonotonic _ g3} `{ SizeMonotonic _ g4} 
: SizeMonotonic (liftGen4 f g1 g2 g3 g4). 
Next Obligation.
  rewrite ! semLiftGen4Size.
  move => t /= [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 H5]]]]]]]]; subst.
  eexists. eexists. eexists. eexists. 
  repeat (split; try reflexivity); by eapply monotonic_def; eauto. 
Qed.

Lemma semLiftGen4SizeMonotonic 
      A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
      (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4) 
  `{SizeMonotonic _ g1} `{SizeMonotonic _ g2}
  `{SizeMonotonic _ g3} `{SizeMonotonic _ g4} :
  semGen (liftGen4 f g1 g2 g3 g4) <-->
  [set b : B | exists a1 a2 a3 a4, semGen g1 a1 /\ semGen g2 a2 /\
                 semGen g3 a3 /\ semGen g4 a4 /\ f a1 a2 a3 a4 = b].
Proof. 
Admitted.


Lemma semLiftGen2SizeMonotonic 
      A1 A2 B (f : A1 -> A2 -> B)
      (g1 : G A1) (g2 : G A2) 
  `{SizeMonotonic _ g1} `{SizeMonotonic _ g2} :
  semGen (liftGen2 f g1 g2) <-->
  [set b : B | exists a1 a2, semGen g1 a1 /\ semGen g2 a2 /\
                                   f a1 a2 = b].
Proof. 
Admitted.

Instance genRBTree_heightMonotonic p : 
  SizeMonotonic (genRBTree_height p).
Proof.
  move : p.  
  eapply (well_founded_induction well_founded_hc).
  move => [[|n] c] IH; rewrite genRBTree_height_eq.
  - case : c {IH}; eauto with typeclass_instances. 
    apply oneofMonotonic; eauto with typeclass_instances.
    move => t [H1 | [H2 | //]]; subst; eauto with typeclass_instances. 
  - case : c IH => IH. apply liftGen4Monotonic; eauto with typeclass_instances.
    eapply IH; eauto. by constructor; omega.
    eapply IH; eauto. by constructor; omega.
    apply bindMonotonic; eauto with typeclass_instances. 
    move => x /=. apply liftGen4Monotonic; eauto with typeclass_instances;
    eapply IH; eauto; (case : x; [ by right | by left; omega]).
Qed.
     
Instance genRBTreeMonotonic : SizeMonotonic genRBTree.
Proof.
  apply bindMonotonic; eauto with typeclass_instances.
Qed.

(* begin semGenRBTreeHeightSize *)
Lemma semGenRBTreeHeightSize h c : 
  semGen (genRBTree_height (h, c)) <--> [set t | is_redblack' t c h ].
(* end semGenRBTreeHeightSize *)
Proof.
  replace c with (snd (h, c)); replace h with (fst (h, c)); try reflexivity.
  move : (h, c). clear h c.
  eapply (well_founded_induction well_founded_hc).
  move => [[|h] []] IH /=; rewrite genRBTree_height_eq.
  - rewrite semReturn. split. move => <-. constructor.
    move => H. inversion H; subst; reflexivity.
  - rewrite semOneof. move => t. split.
    move => [gen [[H1 | [H1 | // _]] H2]]; subst. 
    apply semReturn in H2. rewrite - H2. constructor.
    move : H2 => /semBindSizeMonotonic. move => [n [_ /semReturn <-]].
    constructor. constructor. constructor.
    move => H. inversion H; subst.
    { eexists. split. left. reflexivity. inversion H; subst.
        by apply semReturn. }
    { inversion H0; subst. inversion H1; subst.
      eexists. split. right. left. reflexivity.
      apply semBindSizeMonotonic; eauto with typeclass_instances.
      eexists. split; last by apply semReturn; reflexivity.  
      by apply arbNat_correct. }
  - rewrite semLiftGen4SizeMonotonic. split.
    + move => /= [c [t1 [n [t2 [/semReturn H1 [H2 [H3 [H4 H5]]]]]]]]. 
      rewrite <- H1 in *. clear H1. subst.
      apply IH in H2; last by left; omega. 
      apply IH in H4; last by left; omega. constructor; eauto.
    + move => H. inversion H; subst. 
      apply (IH (h, Black)) in H1; last by left; omega. 
      apply (IH (h, Black)) in H4; last by left; omega. 
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
      apply IH in H2; last by left; omega. 
      apply IH in H4; last by left; omega. constructor; eauto.
    + move => H. inversion H; subst. 
      apply (IH (h.+1, Red)) in H0; last by right. 
      apply (IH (h.+1, Red)) in H1; last by right. 
      eexists Red. split; first by apply semColor.
      apply semLiftGen4SizeMonotonic; eauto with typeclass_instances.
      eexists. eexists. eexists. eexists. repeat (split; auto; try reflexivity).
      by apply semReturn. by auto.
      by apply arbNat_correct. by auto.
      apply (IH (h, Black)) in H1; last by left; omega. 
      apply (IH (h, Black)) in H4; last by left; omega. 
      eexists Black. split; first by apply semColor.
      apply semLiftGen4SizeMonotonic; eauto with typeclass_instances.
      eexists. eexists. eexists. eexists. repeat (split; auto; try reflexivity).
      by apply semReturn. by auto.
      by apply arbNat_correct. by auto.
Qed.


(* begin semRBTreeSize *)
Lemma semRBTree : semGen genRBTree <--> [set t | is_redblack t ].
(* end semRBTreeSize *)
Proof.
  rewrite /genRBTree /is_redblack. 
  rewrite semBindSizeMonotonic. setoid_rewrite semGenRBTreeHeightSize. 
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
  rewrite /insert_preserves_redblack_checker /insert_preserves_redblack.
  rewrite (mergeForAlls arbitraryNat genRBTree).
  rewrite -> semForAllUnsized2.
  rewrite /genPair. split.
  - move => H n t irt. specialize (H (n,t)). simpl in H.
    rewrite /semCheckable in H. simpl in H. rewrite -> semImplication in H.
    rewrite -> semCheckableBool in H.
    apply /is_redblackP. apply : H. 
    apply semLiftGen2SizeMonotonic; eauto with typeclass_instances.
    exists n. exists t. split. by apply arbNat_correct.
    split => //. by apply semRBTree. by apply/is_redblackP.
  - move => H [a t] /semLiftGen2SizeMonotonic [n [t' [_ [Hg [<- <-]]]]]. 
    simpl. rewrite -> semImplication. move => Hb. rewrite semCheckableBool.
    apply /is_redblackP. apply H. by apply /is_redblackP.
  - simpl. eauto with typeclass_instances.
Qed.