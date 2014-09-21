Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random Gen.
Import ListNotations.

Set Implicit Arguments.

(* Set of outcomes semantics for generators *)
Require Import Ensembles.

(* also fixing counterintuitive order of arguments *)
Definition unGen {A : Type} (g : Gen A) : nat -> RandomGen -> A :=
  match g with MkGen f => fun n r => f r n end.

Definition semSize {A : Type} (g : RandomGen -> A) : Ensemble A :=
  fun a => exists seed, g seed = a.

Definition semGen {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists size, semSize ((unGen g) size) a.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A <-> m2 A.

Infix "<-->" := set_eq (at level 70, no associativity) : sem_gen_scope.

(* the set f outcomes m1 is a subset of m2 *)
Definition set_incl {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A -> m2 A.

Infix "-->" := set_incl (at level 70, no associativity) : sem_gen_scope.

Open Scope sem_gen_scope.

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

(* We clearly need to reason about sizes:
   generators need to be size-monotonous functions *)
(* Went for the most explicit way of doing this,
   could later try to use type classes to beautify/automate things *)
Definition sizeMonGen {A : Type} (g : Gen A) := forall a size1 size2,
  (size1 <= size2)%coq_nat ->
  semSize ((unGen g) size1) a ->
  semSize ((unGen g) size2) a.

Lemma semBind : forall A B (g : Gen A) (f : A -> Gen B),
  sizeMonGen g ->
  (forall a, sizeMonGen (f a)) ->
  semGen (bindG g f) <--> fun b => exists a, (semGen g) a /\ (semGen (f a)) b.
Proof.
  move => A B g f MonG MonF b. rewrite /semGen /bindG => /=. split.
  - move : MonG. case : g => [g] MonG /= [size [seed H]]. move : H.
    case (rndSplit seed) => [seed1 seed2].
    exists (g seed1 size). split; do 2 eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[size1 H1] [size2 H2]]].
    assert (Hs1 : (size1 <= max size1 size2)%coq_nat) by apply Max.le_max_l.
    case (MonG _ _ _ Hs1 H1) => [seed1' H1'].
    assert (Hs2 : (size2 <= max size1 size2)%coq_nat) by apply Max.le_max_r.
    case (MonF _ _ _ _ Hs2 H2) => [seed2' H2'].
    eexists (max size1 size2). clear H1 H2.
    case (rndSplitAssumption seed1' seed2') => [seed Hs].
    exists seed.
    move : H1' H2'. move : MonG. case : g => [g] MonG /= H1' H2'.
    rewrite Hs. rewrite H1'. move : H2'. by case (f a).
Qed.

Lemma semFMap : forall A B (f : A -> B) (g : Gen A),
  semGen (fmapG f g) <-->
    (fun b => exists a, (semGen g) a /\ b = f a).
Proof.
  move => A B f [g] b. rewrite /semGen /semSize /fmapG => /=. split.
  - move => [size [seed [H]]]. exists (g seed size). by eauto.
  - move => [a [[size [seed [H1]]] H2]].
    do 2 eexists. rewrite H2. rewrite <- H1. reflexivity.
Qed.

(* This seems like a reasonable thing to assume of randomR,
   why not add it directly to the Random type class? *)
Axiom randomRAssumption : forall A `{Random A} (a1 a2 a : A),
  (exists seed, fst (randomR (a1, a2) seed) = a) <->
  leq a1 a /\ leq a a2.

Lemma semChoose : forall A `{Random A} a1 a2,
  semGen (chooseG (a1,a2)) <--> (fun a => Random.leq a1 a /\ Random.leq a a2).
Proof.
  move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
  - move => [_ [seed H]]. rewrite <- randomRAssumption. by eauto.
  - move => H. exists 0. by rewrite randomRAssumption.
Qed.  

Lemma semSized : forall A (f : nat -> Gen A),
  (forall size1 size2,
    (size1 <= size2)%coq_nat -> semGen (f size2) --> semGen (f size2)) ->
  semGen (sizedG f) <--> (fun a => exists n, semGen (f n) a).
Proof.
  move => A f Mon a. rewrite /semGen /sizedG => /=. split.
  - move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. rewrite /semSize. by eauto.
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
