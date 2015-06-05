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

(* Some helpful lemmas and definitions *)

(* upper bound on the element of each node *)
Inductive all_nodes_bellow (s : nat) : tree -> Prop :=
| Bellow_l : all_nodes_bellow s Leaf
| Bellow_N :
    forall c t1 n t2,
      all_nodes_bellow s t1 ->
      all_nodes_bellow s t2 ->
      (n <= s)%coq_nat ->
      all_nodes_bellow s (Node c t1 n t2).

Definition max_node : tree -> nat -> nat :=
  fix f t m :=
  match t with
    | Leaf => m
    | Node _ t1 n t2 =>
      max (f t1 (max m n)) (f t2 (max m n))
  end.


Lemma all_nodes_bellow_greater :
  forall m n t,
    n <= m ->
    all_nodes_bellow n t ->
    all_nodes_bellow m t.
Proof.
  move => m n t.
  elim : t m n => [| c tl IHtl nd tr IHtr] m n Hleq Hb; try by constructor.
  inversion Hb; subst; constructor; eauto.
  eapply Le.le_trans; eauto. by apply/leP.
Qed.

Lemma max_node_less:
  forall t n,
    (n <= max_node t n)%coq_nat.
Proof.
    elim => [| /= c tl IHtl nd tr IHtr] n; auto.
    apply Max.max_case_strong => Hcmp; auto;
    apply Max.max_case_strong => Hcmp'; auto;
    eapply Le.le_trans; try eassumption;
    [apply IHtl | apply IHtr].
Qed.

(* begin semGenRBTreeHeightSize *)
Lemma semGenRBTreeHeightSize h c s : semGenSize (genRBTree_height (h, c)) s
  <--> [set t | is_redblack' t c h /\ all_nodes_bellow s t].
(* end semGenRBTreeHeightSize *)
Proof. 
  move : c s. induction h as [| h IHh]; intros c' s t.
  { rewrite genRBTree_height_eq. split.
    - destruct c'.
      + rewrite (semReturnSize _ _ _). by move => <-; split; constructor.
      + move => /semOneofSize [gen [[H1 | [H1 | // _]]  H2]]; subst. 
        * apply semReturnSize in H2. rewrite - H2. split; 
          by constructor.
        * move : H2 => /semBindSize 
                        [n [/arbNat_correctSize H1 /semReturnSize <-]].
          split; try by constructor(constructor).
          constructor; auto; by constructor.
    - move => [H1 H2]. destruct c'; inversion H1; subst.
      * by apply semReturnSize.  
      * apply semOneofSize. exists (returnGen Leaf).
        split; first by left. by apply semReturnSize. 
      * inversion H; inversion H0; subst. 
        apply semOneofSize. eexists. split.
        right. left. reflexivity. 
        apply semBindSize. exists n; split; last by apply semReturnSize. 
        inversion H2; subst. by apply arbNat_correctSize. }
  { rewrite genRBTree_height_eq. split.
    - move => /= H. destruct c'; [ | move: H => / semBindSize [[ | ] [/semColorSize ?]] ?];
      repeat 
        (match goal with 
           | [ H : semGenSize (genRBTree_height _) _ _ |- _ ] => 
             rewrite genRBTree_height_eq in H
           | [ H : semGenSize (liftGen4 _ _ _ _ _) _ _ |- _] =>  
             move: H => 
             /semLiftGen4Size [? [? [? [? [/semReturnSize <- 
                                            [/IHh [? ?] [? [/IHh [? ?] ?]]]]]]]]; subst
            | [ H : semGenSize (liftGen4 _ _ _ _ _) _ _ |- _] =>
              move : H => /semLiftGen4Size 
                           [? [? [? [? [/semReturnSize <- [? [? [? ?]]]]]]]]; subst
         end); by split; repeat constructor; auto ; apply arbNat_correctSize.
    - move => H. inversion H as [Hsize Hb]; clear H;
      inversion Hsize as [| ? ? ? ? Hrbl Hrbr |
                           ? ? ? ? ? Hrbl Hrbr]; subst;
      inversion Hb as [ |? ? ? ? Hbt1 Hbt2]; subst; clear Hb;
      [ inversion Hrbl; inversion Hrbr; subst;
        inversion Hbt1; inversion Hbt2; subst;
        simpl; apply semBindSize; exists Red; split;
        first (by apply genColor_correctSize')
      | destruct c';
        [| simpl; apply semBindSize; exists Black; split;
           first (by apply genColor_correctSize') ]];
      repeat (apply semLiftGen4Size; do 4 (eexists);
              (repeat split); try reflexivity; try (by apply arbNat_correctSize);
              try (by eapply semReturnSize); try (by apply IHh; split);
              rewrite genRBTree_height_eq). }
Qed.

(* begin semRBTreeSize *)
Lemma semRBTreeSize s : semGenSize genRBTree s
  <--> [set t | (exists h, h<=s /\ is_redblack' t Red h) /\ all_nodes_bellow s t].
(* end semRBTreeSize *)
Proof.
  move => t. rewrite /genRBTree /is_redblack. split.
  - move => /semBindSize [n [/arbNat_correctSize/leP H1 
                             /semGenRBTreeHeightSize [H2 H3]]]. 
    split; auto. exists n; split; auto.
  - move => [[h [/leP H1 H2]] H3]. 
    apply semBindSize. exists h. 
    split;  
      [ apply arbNat_correctSize | 
        apply semGenRBTreeHeightSize ]; by auto.
Qed.

Lemma all_nodes_bellow_max_node :
  forall t n,
    all_nodes_bellow (max_node t n) t.
Proof.
  elim => [| c tl IHtl nd tr IHtr] n; try by constructor.
  constructor; simpl;
  try (apply Max.max_case_strong => /leP Hcmp; auto;
       eapply all_nodes_bellow_greater; try eassumption; auto).
  apply (Max.max_case_strong n nd) => Hcmp; eauto;
  [ eapply Le.le_trans; try eassumption |];
  apply (Max.max_case_strong) => Hcmp'; apply max_node_less.
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
    destruct irt as [h irt].
    unfold semGen.
    set s := (max (max_node t n) h). exists s. split. by [].
    erewrite (semLiftGen2Size _ _ _ _ (n, t)).
    unfold imset2, prod_curry, imset, setX. exists (n,t). split; [| by []].
    split; simpl.
    { apply arbNat_correctSize.
      apply Le.le_trans with (m := (max_node t n)).
      apply max_node_less. rewrite /s. apply Max.le_max_l. }
    { apply semRBTreeSize. split.
      - exists h. split => //. rewrite /s. apply/leP. apply Max.le_max_r.
      - rewrite /s. apply Max.max_case_strong => Hcmp; eauto;
        [| apply all_nodes_bellow_greater with (n := max_node t n);
           try by apply/leP]; apply all_nodes_bellow_max_node. }
    by apply /is_redblackP.
  - move => H [a t] Hg. unfold semGen in Hg. destruct Hg as [s [_ Hg]].
    simpl. rewrite -> semImplication. rewrite semCheckableBool.
    intro irb. apply /is_redblackP. apply H. by apply /is_redblackP.
  - simpl. eauto with typeclass_instances.
Qed.

(* unsizedChecker proof *)
(* old proof -- still works, but requires checker lemmas with sizes,
   and it's very hard to explain those that early in the paper;
   should still bring back the views and stuff into the new proof
  split.
  - move => H x t [n' Hrb]. set s := max (max_node t x) n'.
    move : H => /(_ s) /semForAllSize H.
    have /H/semPredQPropSize/semForAllSize Hx : semGenSize arbitraryNat s x.
    { apply arbNat_correctSize.
      apply Le.le_trans with (m := (max_node t x)).
      apply max_node_less. rewrite /s. apply Max.le_max_l. }
    have /Hx/semPredQPropSize/semImplicationSize Ht : semGenSize genRBTree s t.
    { apply semRBTreeSize. split.
      - exists n'. split => //. rewrite /s. apply/leP. apply Max.le_max_r.
      - rewrite /s. apply Max.max_case_strong => Hcmp; eauto;
        [| apply all_nodes_bellow_greater with (n := max_node t x);
           try by apply/leP]; apply all_nodes_bellow_max_node. }
    have /is_redblackP/Ht/semBool Hins : is_redblack t by exists n'.
    by apply/is_redblackP.
  - move => H s. apply semForAllSize => n /arbNat_correctSize Hle.
    apply semPredQPropSize.
    apply semForAllSize => t /semRBTreeSize [[n' [Hle' Hrb]] Hb].
    apply semPredQPropSize. apply semImplicationSize => /is_redblackP Hbool.
    apply semBool. apply/is_redblackP. by eapply H.
*)