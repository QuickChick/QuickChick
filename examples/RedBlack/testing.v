Require Import QuickChick.
Require Import SetOfOutcomes EndToEnd.
Require Import ssreflect ssrnat ssrbool eqtype.

Require Import redblack.

Require Import List String.
Import ListNotations.

Open Scope string.

Open Scope Checker_scope.

Fixpoint showColor (c : color) :=
  match c with
    | Red => "Red "
    | Black => "Black " 
  end.

Fixpoint RBTree_to_string (t : tree) :=
  match t with
    | Leaf => "Leaf"
    | Node c l x r => "Node " ++ showColor c  ++ show x 
                            ++ " ( " ++ RBTree_to_string l ++ " ) "
                            ++ " ( " ++ RBTree_to_string r ++ " ) "
  end.

Instance showRBTree {A : Type} `{_ : Show A} : Show tree :=
  {|
    show := RBTree_to_string
  |}.

 
Section Generators.
  Context {Gen : Type -> Type}
          {H: GenMonad Gen}.

  
  Definition genColor := elements Red [Red; Black].
  
  Fixpoint genRBTree_height (h : nat) (c : color) :=
    match h with
      | 0 => 
        match c with 
          | Red => returnGen Leaf
          | Black => oneof (returnGen Leaf)
                           [returnGen Leaf; 
                             bindGen arbitraryNat (fun n =>
                             returnGen (Node Red Leaf n Leaf))]
        end
      | S h => 
        match c with 
          | Red => 
            bindGen (genRBTree_height h Black) (fun t1 =>
            bindGen (genRBTree_height h Black) (fun t2 => 
            bindGen arbitraryNat (fun n => 
            returnGen (Node Black t1 n t2))))
          | Black => 
            bindGen genColor (fun c' =>
            match c' with 
              | Red =>
                bindGen (genRBTree_height h Black) (fun tl1 =>
                bindGen (genRBTree_height h Black) (fun tl2 => 
                bindGen (genRBTree_height h Black) (fun tr1 =>
                bindGen (genRBTree_height h Black) (fun tr2 =>
                bindGen arbitraryNat (fun n => 
                bindGen arbitraryNat (fun nl => 
                bindGen arbitraryNat (fun nr => 
                returnGen (Node Red (Node Black tl1 nl tr1) n 
                                (Node Black tl2 nr tr2)))))))))
              | Black =>
                bindGen (genRBTree_height h Black) (fun t1 =>
                bindGen (genRBTree_height h Black) (fun t2 => 
                bindGen arbitraryNat (fun n => 
                returnGen (Node Black t1 n t2))))
            end)
        end
    end.

  Definition genRBTree := sized (fun h => genRBTree_height h Red).
  
End Generators.

Section Checker.
  Context {Gen : Type -> Type}
          {H: GenMonad Gen}.

  Definition insert_is_redblack_checker : Gen QProp :=
    forAll arbitraryNat (fun n =>
    (forAll genRBTree (fun t => 
      (is_redblack_bool t Red ==> 
       is_redblack_bool (insert n t) Red) : Gen QProp)) : Gen QProp).

End Checker.

Definition args := MkArgs None defNumTests defNumDiscards
                             defNumShrinks 9 true.

Definition testInsert :=
  showResult (quickCheckWith args insert_is_redblack_checker).

QuickCheck testInsert.

(* Correctness proofs *)

Lemma genColor_correct:
  genColor <--> (fun _ => True).
Proof.
  rewrite /genColor. intros c. rewrite elements_equiv.
  split => // _. left. 
  destruct c;  by [ constructor | constructor(constructor)].
Qed.

(* ugly proof, needs refactoring at some point *)
Lemma genRBTree_height_correct:
  forall c h,
    (genRBTree_height h c) <--> (fun t => is_redblack t c h).
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
  genRBTree <--> (fun t => exists h, is_redblack t Red h).
Proof.
  move => t. split.
  - rewrite /genRBTree sized_def.  
    move => [n /genRBTree_height_correct Hgen].
      by exists n.
  - move => [n /genRBTree_height_correct Hgen].
    rewrite /genRBTree sized_def. by exists n.
Qed.
    

Lemma insert_is_redblack_checker_correct:
  semChecker insert_is_redblack_checker <-> insert_preserves_redblack.
Proof.
  rewrite /insert_is_redblack_checker /insert_preserves_redblack semForAll. 
  split.
  + move => H x s n Hrb.
    have /H/semPredQProp/semForAll H' : @arbitraryNat Pred _ x 
      by apply arbNat_correct.
    have /H'/semPredQProp/semImplication H'': @genRBTree Pred _ s 
      by apply genRBTree_correct; eexists; eassumption.
    apply/is_redblack_exP. 
    by move/is_redblack_exP/H''/semBool: (ex_intro _ _ Hrb).  
  + move=> H a _.
    apply/semPredQProp/semForAll. move => t Hgen.
    apply/semPredQProp/semImplication. move => Hrb.
    apply/semBool. apply/is_redblack_exP.
    move: Hrb => /is_redblack_exP [n Hrb]. eapply H.
    eassumption. 
Qed.