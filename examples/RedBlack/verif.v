Require Import ssreflect ssrnat ssrbool eqtype.

Require Import List String.

Require Import QuickChick.
Require Import SetOfOutcomes EndToEnd.

Require Import redblack.
Require Import testing.

Lemma is_redblackP :
  forall (t : tree),
    reflect (is_redblack t)
            (is_redblack_bool t).
Proof.
  move => t. induction t.
  - constructor. rewrite /is_redblack. exists 0. by constructor.
  - admit.
Admitted. (* TODO *)

Lemma genColor_correct:
  genColor <--> all.
Proof.
  rewrite /genColor. intros c. rewrite elements_equiv.
  split => // _. left.
  destruct c;  by [ constructor | constructor(constructor)].
Qed.

(* ugly proof, needs refactoring at some point *)
Lemma genRBTree_height_correct:
  forall c h,
    (genRBTree_height h c) <--> (fun t => is_redblack' t c h).
Proof.
  move => c h. move : c. induction h as [| h]; intros c' t.
  { rewrite /genRBTree_height. split.
    - destruct c'.
      + rewrite returnGen_def. by move => <-; constructor.
      + rewrite oneof_equiv. move => [[gen [H Hgen]] | [// H Hret]].
        inversion H as [HIn | HIn]; subst.
        * rewrite returnGen_def in Hgen; subst. by constructor.
        * inversion HIn as [HIn' |  HIn'] => //; subst.
        move: Hgen => [n [Hn Hret]]. rewrite returnGen_def in Hret; subst.
          by constructor; constructor.
    - move=> H. inversion H; subst.
      + destruct c' => //. rewrite oneof_equiv. left.
        eexists. by split; [by apply in_eq |].
      + rewrite oneof_equiv. left. eexists.
        split. by constructor(apply in_eq).
        eexists. split; first by apply arbNat_correct.
        inversion H0; subst. inversion H1; subst.
        reflexivity. }
  { split.
    - destruct c'.
      + move => [tl [/IHh Hgentl [tr [/IHh Hgentr [n [_ H]]]]]].
        rewrite returnGen_def in H; subst.
        by constructor => //.
      + move => [[] [Hcol Hgen]].
        * move : Hgen =>
          [tl1 [/IHh Htl1 [tl2 [/IHh Htl2 [tr1 [/IHh Htr1 [tr2 [/IHh Htr2 H]]]]]]]].
          move : H => [n [_ [nl [_ [nr [_ H]]]]]].
          rewrite returnGen_def in H; subst.
          constructor; constructor=> //.
       * move : Hgen => [tl [/IHh Hgentl [tr [/IHh Hgentr [n [_ H]]]]]].
         rewrite returnGen_def in H; subst.
         constructor => //.
    - move => H. inversion H as [| n tl tr h' Hrbl Hrbr |
                                   c n tl tr h' Hrbl Hrbr]; subst.
      + inversion Hrbl as [| |c n1 tl1 tr1 h1 Hrbl1 Hrbr1]; subst.
        inversion Hrbr as [| |c n2 tl2 tr2 h2 Hrbl2 Hrbr2]; subst.
        exists Red. split; first by apply genColor_correct.
        exists tl1. split; first by apply IHh.
        exists tl2. split; first by apply IHh.
        exists tr1. split; first by apply IHh.
        exists tr2. split; first by apply IHh.
        exists n. split; first by apply arbNat_correct.
        exists n1. split; first by apply arbNat_correct.
        exists n2. split; first by apply arbNat_correct.
        reflexivity.
      + destruct c'.
        * exists tl. split; first by apply IHh.
          exists tr. split; first by apply IHh.
          exists n. split; first by apply arbNat_correct.
          reflexivity.
        * exists Black. split; first by apply genColor_correct.
          exists tl. split; first by apply IHh.
          exists tr. split; first by apply IHh.
          exists n. split; first by apply arbNat_correct.
          reflexivity. }
Qed.

Lemma genRBTree_correct:
  genRBTree <--> is_redblack.
Proof.
  move => t. split.
  - rewrite /genRBTree sized_def.
    move => [n /genRBTree_height_correct Hgen].
    eexists. eassumption.
  - rewrite /is_redblack. move => [h /genRBTree_height_correct  Hgen].
    rewrite /genRBTree sized_def. by exists h.
Qed.

Lemma insert_is_redblack_checker_correct:
  semChecker (insert_is_redblack_checker genRBTree) <-> insert_preserves_redblack.
Proof.
  rewrite /insert_is_redblack_checker /insert_preserves_redblack semForAll.
  split.
  + move => H x s Hrb.
    have /H/semPredQProp/semForAll H' : @arbitraryNat Pred _ x
      by apply arbNat_correct.
    have /H'/semPredQProp/semImplication H'': @genRBTree Pred _ s
      by apply genRBTree_correct.
    apply/is_redblackP.
    by move/is_redblackP/H''/semBool: Hrb.
  + move=> H a _.
    apply/semPredQProp/semForAll. move => t Hgen.
    apply/semPredQProp/semImplication. move => Hrb.
    apply/semBool. apply/is_redblackP.
    move: Hrb => /is_redblackP [n Hrb]. eapply H.
    eexists. eassumption.
Qed.
