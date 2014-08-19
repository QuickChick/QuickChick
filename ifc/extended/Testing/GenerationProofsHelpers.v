Require Import QuickChick SetOfOutcomes.

Require Import List. Import ListNotations.
Require Import ZArith.

Require Import Common Generation Indist.

Require Import ssreflect ssrbool ssrnat eqtype.

(* Some Lemmas required for generation proofs.
   Moved here so the main fail is cleaner.
   Maybe they need to be placed somewhere else *)

Lemma powerset_nonempty :
  forall {A} (l : list A), powerset l <> nil.
Proof.
  move => A. elim => //= x xs IHxs.
  case: (powerset xs) IHxs => //=.
Qed.

Lemma powerset_in:
  forall {A} (a : A) (l l' : list A),
    In a l -> In l (powerset l') -> In a l'.
Proof.
  move=> A a l l'. elim : l' l a => //= [|x xs IHxs] l a   HIn HIn'; subst.
  + by case: HIn' => H; subst.
  +  apply in_app_or in HIn'. move : HIn' => [/in_map_iff [x' [Heq HIn']] | HIn']; subst.
     - case: HIn => [Heq | HIn]; subst.
       * by left.
       * right. eapply IHxs; eauto.
     - by right; eapply IHxs; eauto.
Qed.

(*
Lemma elements__label_of_list:
  forall (lst : list Z) x zt,
    List.In x (Zset.elements (fold_left (fun (a : Zset.t) (b : Z) => Zset.add b a) lst zt)) <->
    List.In x (lst ++ (Zset.elements zt)).
Proof.
  move => lst.
  elim : lst => //=  x xs IHxs x' init.
  split.
  + move => H. move/IHxs: H => H. apply in_app_or in H.
    move : H => [H | H].
    * by right; apply in_or_app; left.
    * move/Zset.In_add : H => [Heq | HIn].
      - by left.
      - right. apply in_or_app. by right.
  + move=> [Heq | H]; apply IHxs; subst.
    * apply in_or_app. right.
      by apply/Zset.In_add; left.
    * apply in_app_or in H. move : H => [Heq | HIn].
      - by apply in_or_app; left.
      - apply in_or_app; right. by apply/Zset.In_add; right.
Qed.

Lemma label_of_list__elements:
  forall l,
    label_of_list (Zset.elements l)  = l .
Proof.
  move => l. apply flows_antisymm.
  apply Zset.incl_spec. move => a HIn.
  move/elements__label_of_list : HIn => HIn. apply in_app_or in HIn.
  rewrite Zset.elements_empty in HIn.
  by case : HIn.
  apply Zset.incl_spec. move => a HIn.
  apply/elements__label_of_list/in_or_app.
  by left.
Qed.

*)

Lemma allThingsBelow_nonempty: forall l2, allThingsBelow l2 <> [].
Proof.
  rewrite /allThingsBelow. case; by simpl.
Qed.

Lemma in_nil_powerset :
  forall {A} (l : list A), In [] (powerset l).
Proof.
  move=> A l. elim l => //= [| x xs IHxs]. by left.
  by apply in_or_app; right.
Qed.

Lemma allThingsBelow_isLow :
  forall l l',
    In l (allThingsBelow l') <-> l <: l'.
Proof.
  rewrite /allThingsBelow.
  case; case; simpl; try tauto; firstorder; discriminate.
Qed.

Lemma filter_nil:
  forall {A} (f : A -> bool) l,
    filter f l = [] <->
    l = [] \/ forall x, In x l -> f x = false.
Proof.
  move=> A f l. split.
  - elim: l => //= [_ | x xs  IHxs H].
    * by left.
    * right. move=> x' [Heq | HIn]; subst.
        by case: (f x') H.
        case: (f x) H => //= Hf.
        move : (IHxs Hf) => [Heq | HIn']; subst => //=; auto.
  - move => [Heq | H]; subst => //=.
    elim : l H => // x xs IHxs H.
    simpl. rewrite (H x (in_eq x xs)).
    apply IHxs. move=> x' HIn. apply H.
    by apply in_cons.
Qed.

Lemma powerset_in_refl:
forall {a} (l : list a), In l (powerset l).
Proof.
  move=> a. elim => //= [| x xs IHxs].
  by left.
  by apply in_or_app; left; apply in_map.
Qed.

Lemma join_equiv :
  forall (l1 l2 l : Label),
    isLow l1 l = true->
    (isHigh (join l1 l2) l <-> isHigh l2 l).
Proof.
  rewrite /isHigh /isLow. move => l1 l2 l Hlow. split.
  +  move => Hnotlow. apply/Bool.eq_true_not_negb => Hlow2.
     move: (join_minimal _ _ _ Hlow Hlow2)  => contra. rewrite contra in Hnotlow.
     discriminate.
  + move/Bool.negb_true_iff => Hnotlow.
    eapply not_flows_not_join_flows_right in Hnotlow.
    apply Bool.negb_true_iff. eassumption .
Qed.

Lemma forallb2_forall :
  forall (A : Type) (f : A -> A -> bool) (l1 l2 : list A),
    forallb2 f l1 l2 = true <->
    (length l1 = length l2 /\
     forall x y : A, In (x, y) (seq.zip l1 l2) -> f x y = true).
Proof.
  move=> A f l1 l2. split.
  + elim: l1 l2 => [| x l1 IHxs]; case => //= y l2 /andP [H1 H2].
    move/(_ l2 H2) : IHxs => [-> HIn]. split => //.
    move=> x' y' [[Heq1 Heq2] | HIn']; subst; by auto.
  + elim: l1 l2 => [| x l1 IHxs]; case => [|y l2] //=; try by move => [H _].
    move => [Hlen HIn]. apply/andP; split. by eauto.
    apply IHxs. split; by eauto.
Qed.

Lemma zip_combine:
  forall {A} {B} (l1 : list A) (l2 : list B),
    length l1 = length l2 ->
    seq.zip l1 l2 = combine l1 l2.
Proof.
  move => A B. elim => //= [| x xs IHxs]; case => //= y yx Hlen.
  rewrite IHxs //. by apply/eq_add_S.
Qed.


Lemma in_zip:
  forall {A} {B} (l1 : list A) (l2 : list B) x y,
  (In (x, y) (seq.zip l1 l2) -> (In x l1 /\ In y l2)).
Proof.
  Opaque In.
  move => A B. elim => [| x xs IHxs]; case => // y ys x' y' [[Heq1 Heq2] | HIn].
  + by subst; split; apply in_eq.
  + move/IHxs: HIn => [HIn1 HIn2]. split; constructor(assumption).
Qed.


Lemma in_map_zip :
  forall {A B C} (l1 : list A) (l2 : list B) x y (f : B -> C),
     In (x, y) (seq.zip l1 l2) -> In (x, f y) (seq.zip l1 (map f l2)).
Proof.
  move=> A B C.
  elim => [| x xs IHxs]; case => // y ys x' y' f [[Heq1 Heq2] | HIn]; subst.
  + by constructor.
  + move/IHxs : HIn => /(_ f) HIn.
    by constructor(assumption).
Qed.

Lemma in_map_zip_iff :
  forall {A B C} (l1 : list A) (l2 : list B) x y (f : B -> C),
    In (x, y) (seq.zip l1 (map f l2)) <->
     exists z, f z = y /\ In (x, z) (seq.zip l1 l2).
Proof.
  move=> A B C. split.
  - move: l1 l2 x y.
    elim => [| x xs IHxs]; case => // y ys x' y' [[Heq1 Heq2] | HIn]; subst.
    + exists y. split => //. by constructor.
    + move/IHxs : HIn => [z [Heq HIn]].
      exists z. split => //. by constructor(assumption).
  - move => [z' [Heq HIn]]. subst. by apply/in_map_zip.
Qed.


Lemma in_zip_swap:
    forall {A B} (l1 : list A) (l2 : list B) x y,
     In (x, y) (seq.zip l1 l2) <->  In (y, x) (seq.zip l2 l1).
Proof.
  move=> A B.
  elim => [| x xs IHxs]; case => // y ys x' y'.
  split; move=>  [[Heq1 Heq2] | HIn] ; subst; (try by constructor);
  by move/IHxs: HIn => HIn; constructor(assumption).
Qed.

Lemma in_nth_iff:
  forall {A} (l : list A) x,
    In x l <-> exists n, List.nth n l x = x /\ n < length l.
Proof.
  move=> A l x. split.
  - move=> HIn.  apply in_split in HIn. move : HIn => [l1 [l2 Heq]].
    exists (length l1). subst. split.
    + by rewrite app_nth2 // minus_diag.
    + rewrite app_length. simpl. apply/ltP.
      rewrite -[X in (_ + X)%coq_nat]addn1 [X in (X < _)%coq_nat]plus_n_O.
      apply plus_lt_compat_l.  apply/leP. rewrite addn_gt0.
      apply/orP; by right.
  - move => [n [Heq Hle]]. rewrite -Heq. by apply/nth_In/leP.
Qed.

Lemma nth_seqnth :
  forall {A} (l : list A) n (x : A),
    seq.nth x l n = List.nth n l x.
Proof.
  move=> A. elim. case =>//.
  move=> a l H. move => n x. rewrite -seq.cat1s.
  rewrite seq.nth_cat. simpl. case: n => //= n. rewrite H.
  by rewrite -addn1 -[X in _ - X]add0n subnDr subn0.
Qed.

Lemma nth_foralldef:
  forall {A} (l: list A) n (x x': A),
    n < length l -> List.nth n l x = List.nth n l x'.
Proof.
  move => A. elim=> // x xs IHxs n d d' Hlen.
  case: n Hlen => //= n Hlen. auto.
Qed.

Lemma size_length:
  forall {A} (l :list A), seq.size l = length l.
Proof.
  move=> A. elim => //.
Qed.
