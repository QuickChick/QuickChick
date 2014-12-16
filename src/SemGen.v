Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random Gen.
Import ListNotations.

Set Implicit Arguments.

(* Set of outcomes semantics for generators *)
Require Import Ensembles.

Definition unGen {A : Type} (g : Gen A) : RandomGen -> nat -> A :=
  match g with MkGen f => f end.

Definition semSize {A : Type} (g : Gen A) (size : nat) : Ensemble A :=
  fun a => exists seed, (unGen g) seed size = a.

Definition semGen {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists size, semSize g size a.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall (a : A), m1 a <-> m2 a.

(* CH: was trying to get rewriting of <--> to work,
   but so far I didn't manage; it would be nice to make this work;
   ask Maxime? *)
Section Rel.

Variable A : Type.

Require Import RelationClasses.

Lemma set_eq_refl : Reflexive (@set_eq A).
Admitted.

Lemma set_eq_sym : Symmetric (@set_eq A).
Admitted.

Lemma set_eq_trans : Transitive (@set_eq A).
Admitted.

Global Instance set_eq_equiv : Equivalence (@set_eq A).
Proof. split; [apply set_eq_refl | apply set_eq_sym | apply set_eq_trans]. Qed.

Require Import Morphisms.

Global Instance app_Proper (a : A) :
  Proper (set_eq ==> iff) (fun x => x a).
Proof. intros s1 s2. by rewrite /set_eq. Qed.

End Rel.

Infix "<-->" := set_eq (at level 70, no associativity) : sem_gen_scope.

(* the set f outcomes m1 is a subset of m2 *)
Definition set_incl {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A -> m2 A.

Infix "--->" := set_incl (at level 70, no associativity) : sem_gen_scope.

Open Scope sem_gen_scope.

Axiom randomSeedInhabitant : RandomGen.

Lemma semReturnSize : forall A (x : A) (size : nat),
  semSize (returnG x) size <--> eq x.
Proof.
  move => A x a. rewrite /semSize. split.
  - move => [seed H]. by [].
  - move => H /=. rewrite H.
    exists randomSeedInhabitant. reflexivity.
Qed.

Lemma semReturn : forall A (x : A),
  semGen (returnG x) <--> eq x.
Proof. (* this kind of proof should be "trivial by rewriting",
          but this doesn't quite work as easy at it should *)
  move => A x. rewrite /semGen.
  (* was hoping to do the rest by rewriting: setoid_rewrite semReturnSize. *)
  pose proof (semReturnSize x) as G. unfold set_eq in G.
  (* setoid_rewrite G. -- failed constraints *)
  move => a /=. split.
  - move => [size H]. (* or rewrite -> G in H. exact H. *)
    rewrite <- G. exact H.
  - move => H. exists 0. by rewrite G.
Qed.

(* For cardinality reasons this requires RandomGen to be infinite;
   this is just an abstraction of what's happening at the lower levels *)
Axiom rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).

Lemma semBindSize : forall A B (g : Gen A) (f : A -> Gen B) (size : nat),
  semSize (bindG g f) size <-->
  fun b => exists a, (semSize g size) a /\
                     (semSize (f a) size) b.
Proof.
  move => A B [g] f size b. rewrite /semSize /bindG => /=. split.
  - case => [seed H]. move : H.
    case (rndSplit seed) => [seed1 seed2] H.
    exists (g seed1 size). split; eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[seed1 H1] [seed2 H2]]].
    case (rndSplitAssumption seed1 seed2) => [seed Hseed].
    exists seed. rewrite Hseed. rewrite H1. move : H2. by case (f a).
Qed.

Lemma semFMapSize : forall A B (f : A -> B) (g : Gen A) (size : nat),
  semSize (fmapG f g) size <-->
    (fun b => exists a, (semSize g size) a /\ b = f a).
Proof.
  move => A B f [g] size b. rewrite /semSize /fmapG => /=. split.
  - move => [seed [H]]. exists (g seed size). by eauto.
  - move => [a [[seed [H1]] H2]].
    eexists. rewrite H2. rewrite <- H1. reflexivity.
Qed.

(* This should just use semFMapSize *)
Lemma semFMap : forall A B (f : A -> B) (g : Gen A),
  semGen (fmapG f g) <-->
    (fun b => exists a, (semGen g) a /\ b = f a).
Proof.
  move => A B f [g] b. rewrite /semGen /semSize /fmapG => /=. split.
  - move => [size [seed [H]]]. exists (g seed size). by eauto.
  - move => [a [[size [seed [H1]]] H2]].
    do 2 eexists. rewrite H2. rewrite <- H1. reflexivity.
Qed.

Lemma semChoose : forall A `{Random A} a1 a2,
  semGen (chooseG (a1,a2)) <--> (fun a => Random.leq a1 a /\ Random.leq a a2).
Proof.
  move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
  - by move => [_ /randomRCorrect H].
  - move => /randomRCorrect H. by exists 0.
Qed.  

Lemma semSizedSize : forall A (f : nat -> Gen A),
  semGen (sizedG f) <--> (fun a => exists n, semSize (f n) n a).
Proof.
  move => A f a. rewrite /semGen /semSize /sizedG => /=. split.
  - move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. rewrite /semSize. by eauto.
  - move => [size [seed H]]. exists size. exists seed.
    move : H. case (f size) => g H. rewrite /semSize. by eauto.
Qed.

Lemma semResize : forall A (n : nat) (g : Gen A),
  semGen (resize n g) <--> semSize g n .
Proof.
  move => A n [g] a. rewrite /semGen /semSize /resize => /=. split.
  - move => [_ [seed H]]. by eauto.
  - move => [seed H]. exists 0. by eauto.
Qed.

Lemma semGenSuchThatMaybeAux_sound:
  forall {A} g p k n (a : A) seed size,
    unGen (suchThatMaybeAux g p k n) seed size = Some a ->
    (exists size seed, (unGen g) seed size = a) /\ p a.
Proof. 
  move=> /= A g p k n. elim : n k =>  [//=| n IHn] k a seed size H.
  simpl in *. unfold unGen, bindG in H.
  remember (resize (2 * k + n.+1) g) as g'.
  case: g' H Heqg'=> /= g' H Heqg'.
  case: (rndSplit seed) H Heqg'=> /= r1 r2 H Heqg'. 
  remember (p (g' r1 size)) as b.
  case: b H Heqb => /= H Heqb. inversion H; subst.
  rewrite /resize in Heqg'.
  destruct g as [g]. inversion Heqg'; subst.
  split =>  //=. by eexists; eexists.
  eapply (IHn k.+1 a r2 size). rewrite -H.
  by destruct (suchThatMaybeAux g p k.+1 n).
Qed.
 
(* Lemma semGenSuchThatMaybeAux_complete: *)
(*   forall {A} g (p : A -> bool) (a : A) seed size, *)
(*     (unGen g) seed size = a -> p a -> *)
(*     exists seed size n k,  *)
(*       unGen (suchThatMaybeAux g p k n) seed size = Some a. *)
(* Proof.   *)
(*   move=> A [g] /= p a seed size H pa.  *)
(*   move/(_ seed seed): rndSplitAssumption => [s Hs]. *)
(*   exists s. *)
(*   exists 0. exists (size.+1). exists 0 => //=.  *)
(*   rewrite Hs /=. by rewrite muln0 add0n H pa. *)
(* Qed. *)
   
Lemma semSuchThatMaybe : forall A (g : Gen A) (f : A -> bool),
  semGen (suchThatMaybeG g f) --->
         (fun o => o = None \/
                   (exists y, o = Some y /\ semGen g y /\ f y)).
(* Not an exact spec !!! *)
Proof.  
  move => A g f a. rewrite /semGen /semSize. 
  - case : a => [a|] [n [s H]]; last by left. right.
    eexists; split=> //=.
    remember (match n with
                 | 0 => 1
                 | m'.+1 => m'.+1
               end) as n'.  
    apply (semGenSuchThatMaybeAux_sound g f 0 n' s n). rewrite -H /= -Heqn'.
    by destruct (suchThatMaybeAux g f 0 n').
Qed.
      
Definition roseRoot {A : Type} (ra : Rose A) : A :=
  match ra with
    | MkRose r _ => r
  end.


Definition generates_Rose {A} (r : Rose (Gen A)) (seed: RandomGen) (size : nat) 
           (t : Rose A) : Prop :=

  t = (fmapRose (fun (g : Gen A) => unGen g seed size) r).  


Lemma semPromote : forall A (m : Rose (Gen A)),
  semGen (promoteG m) <--> 
         fun (t : (Rose A)) => 
           exists seed size, 
             generates_Rose m seed size t.
Proof.
  move => A m [a [l]]. split.
  - move => [size [seed H]]. exists seed. exists size. 
    rewrite -H {H} => /=. move: m. fix 1.
    destruct m as [[g] [l']] => /=.
    elim : l' => [//=|//= m' ls IHl].
    unfold generates_Rose in *. simpl in *.
    repeat (apply f_equal) => /=. apply f_equal2.
    apply semPromote. by inversion IHl.
  - move =>  [seed [size H]]. exists size. exists seed.
    rewrite H {H}. move: m. fix 1 => [[g] [l']] => /=. 
    elim : l' => [//=|//= m' ls IHl]. 
    + apply f_equal2 => //=. by case: g.
    + apply f_equal2 => //=. by case: g {IHl}.
      apply f_equal. apply f_equal2 => //=. 
      by rewrite -semPromote.  by inversion IHl.
Qed.