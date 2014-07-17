Require Import QuickChick SetOfOutcomes.

Require Import Common Machine Generation. 

Require Import List.
Require Import ZArith.

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
  
Lemma allThingsBelow_nonempty: forall l2, allThingsBelow l2 <> [].
Proof.
  rewrite /allThingsBelow /allBelow. 
  by move =>  l1 /map_eq_nil/powerset_nonempty c.
Qed.


Lemma in_nil_powerset :
  forall {A} (l : list A), In [] (powerset l).
Proof.
  move=> A l. elim l => //= [| x xs IHxs]. by left.
  by apply in_or_app; right. 
Qed.


Lemma allThingsBelow_isLow : 
  forall l l', 
    In l (allThingsBelow l') -> l <: l'.
Proof. 
  move => l l'. (* split *)  
  + move=> /in_map_iff [x [Heq HIn]]. subst. 
    apply/Zset.incl_spec. move => a /elements__label_of_list H. 
    rewrite Zset.elements_empty app_nil_r in H. 
      by eapply powerset_in; eauto.
Qed.

Lemma allThingsBelow_isLow' : 
  forall l l', 
    l <: l' -> In l (allThingsBelow l').
Proof. 
  move => l l'. move=> Hf. 
  rewrite /allThingsBelow /allBelow.
  rewrite -[X in In X _]label_of_list__elements. apply in_map.
  admit.
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

(* Move it at arbitrary.v ? 
  Sure, at some point. We should prove all the generators 
  at arbitrary.v complete *) 
Lemma arbInt_correct : 
  arbitrary <--> (fun (z : Z) => True).
Proof.
  rewrite /arbitrary /arbInt /arbitraryZ.  
  rewrite sized_def. move => z. split => //= _. 
  exists (Z.abs_nat z).
  split. 
  + apply/Z.compare_le_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
  + apply/Z.compare_ge_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
Qed.