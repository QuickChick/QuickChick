Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random Gen.
Import ListNotations.

Set Implicit Arguments.

(* Set of outcomes semantics for generators *)
Require Import Ensembles.

Definition unGen {A : Type} (g : Gen A) : RandomGen -> nat -> A :=
  match g with MkGen f => f end.

Definition semGen {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists size, exists seed, (unGen g) seed size = a.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A <-> m2 A.

Infix "<-->" := set_eq (at level 70, no associativity) : pred_scope.

(* the set f outcomes m1 is a subset of m2 *)
Definition set_incl {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A -> m2 A.

Infix "-->" := set_incl (at level 70, no associativity) : pred_scope.

Open Scope pred_scope.

Axiom randomSeedInhabitant : RandomGen.

Lemma semReturn : forall A (x : A),
  semGen (returnG x) <--> eq x.
Proof.
  move => A x a. rewrite /semGen. split.
  - move => [size [seed H]] //.
  - move => H /=. rewrite H.
    exists 0. exists randomSeedInhabitant. reflexivity.
Qed.

(* This seems like a very strong assumption;
   for cardinality reasons it requires RandomGen to be infinite *)
Axiom rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).

(* We will clearly need to reason about sizes:
   generators need to be size-monotonous functions *)
(* Currently can't assume this of all generators,
   but this will probably need to be part of Gen
   (sigma type? this would break the non-intrusiveness of our solution)
   / or of some type class (Arbitrary? a super class if it so that
   users can choose how much they want to prove) *)
Axiom genSize : forall A (a : A) g seed1 size1 size2,
  (size1 <= size2)%coq_nat ->
  (unGen g) seed1 size1 = a ->
  exists seed2, (unGen g) seed2 size2 = a.

Lemma semBind : forall A B (g : Gen A) (f : A -> Gen B),
  semGen (bindG g f) <--> fun b => exists a, (semGen g) a /\ (semGen (f a)) b.
Proof.
  move => A B g f b. rewrite /semGen /bindG => /=. split.
  - case : g => [g] /= [size [seed H]]. move : H.
    case (rndSplit seed) => [seed1 seed2].
    exists (g seed1 size). split; do 2 eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[size1 [seed1 H1]] [size2 [seed2 H2]]]].
    assert (Hs1 : (size1 <= max size1 size2)%coq_nat) by apply Max.le_max_l.
    case (genSize _ _ Hs1 H1) => [seed1' H1'].
    assert (Hs2 : (size2 <= max size1 size2)%coq_nat) by apply Max.le_max_r.
    case (genSize _ _ Hs2 H2) => [seed2' H2'].
    eexists (max size1 size2). clear H1 H2.
    case (rndSplitAssumption seed1' seed2') => [seed Hs].
    exists seed.
    move : H1' H2'. case : g => [g] /= H1' H2'.
    rewrite Hs. rewrite H1'. move : H2'. by case (f a).
Qed.

Lemma semFMap : forall A B (f : A -> B) (g : Gen A),
  semGen (fmapG f g) = semGen (bindG g (fun a => returnG (f a))).
Proof.
  (* Should be able to prove this without any extra axioms!? *)
Admitted.

Lemma semChoose : forall A `{Random A} a1 a2,
  semGen (chooseG (a1,a2)) <--> (fun a => Random.leq a1 a /\ Random.leq a a2).
Proof.
  move => A H a1 a2. rewrite /semGen. simpl.
  admit. (* this seems like a reasonable thing to assume of randomR,
            why not add it directly to the Random type class? *)
Admitted.

Lemma semSized : forall A (f : nat -> Gen A),
  (forall size1 size2,
    (size1 <= size2)%coq_nat -> semGen (f size2) --> semGen (f size2)) ->
  semGen (sizedG f) <--> (fun a => exists n, semGen (f n) a).
Proof.
  move => A f Mon a. rewrite /semGen /sizedG => /=. split.
  - move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. by eauto.
  - move => [n [size [seed H]]].
    exists (max n size).
    admit. (* Hopefully this follows from something like Mon *)
Admitted.

Lemma semSuchThatMaybe : forall A (g : Gen A) (f : A -> bool),
  semGen (suchThatMaybeG g f) <-->
  (fun o => (o = None) \/ (exists y, o = Some y /\ semGen g y /\ f y)).
Proof.
  move => A g f a. rewrite /suchThatMaybeG.
  admit. (* looks a bit scarry *)
Admitted.

Lemma semPromote : forall A (m : Rose (Gen A)),
  semGen (promoteG m) <-->
  match m with
    | MkRose g _ =>
      semGen(bindG g (fun x : A => returnG (MkRose x (lazy nil))))
  end.
Proof.
  move => A m a. rewrite /promoteG /fmapRose.
  admit. (* looks a bit scarry *)
Admitted.
