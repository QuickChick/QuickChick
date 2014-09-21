Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random AbstractGen Gen.
Import ListNotations.

Set Implicit Arguments.

(* Set of outcomes semantics for generators *)
Require Import Ensembles.

Definition unGen {A : Type} (g : Gen A) : RandomGen -> nat -> A :=
  match g with MkGen f => f end.

Definition semGen {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists seed, exists size, (unGen g) seed size = a.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A <-> m2 A.

Infix "<-->" := set_eq (at level 70, no associativity) : pred_scope.

Open Scope pred_scope.

Axiom randomSeedInhabitant : RandomGen.

Lemma semReturn : forall {A} (x : A),
  semGen (returnG x) <--> eq x.
Proof.
  move => A x a. rewrite /semGen. split.
  - move => [seed [size H]] //.
  - move => H /=. rewrite H.
    exists randomSeedInhabitant. exists 0. reflexivity.
Qed.

(* This seems like a very strong assumption;
   for cardinality reasons it requires RandomGen to be infinite *)
Axiom rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).

(* We will clearly need to reason about sizes:
   generators need to be size-monotonous functions *)
(* Currently can't assume this of all generators,
   but this will probably need to be part of Gen (sigma type?)
   / or of some type class(Arbitrary?) *)
Axiom genSize : forall {A : Type} (a : A) g seed1 size1 size2,
  (size1 <= size2)%coq_nat ->
  (unGen g) seed1 size1 = a ->
  exists seed2, (unGen g) seed2 size2 = a.

Lemma semBind : forall {A B} (g : Gen A) (f : A -> Gen B),
  semGen (bindG g f) <--> fun b => exists a, (semGen g) a /\ (semGen (f a)) b.
Proof.
  move => A B g f b. rewrite /semGen /bindG => /=. split.
  - case : g => [g] /= [seed [size H]]. move : H.
    case (rndSplit seed) => [seed1 seed2].
    exists (g seed1 size). split; do 2 eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[seed1 [size1 H1]] [seed2 [size2 H2]]]].
    assert (Hs1 : (size1 <= max size1 size2)%coq_nat) by apply Max.le_max_l.
    case (genSize _ _ Hs1 H1) => [seed1' H1'].
    assert (Hs2 : (size2 <= max size1 size2)%coq_nat) by apply Max.le_max_r.
    case (genSize _ _ Hs2 H2) => [seed2' H2'].
    clear H1 H2.
    case (rndSplitAssumption seed1' seed2') => [seed Hs].
    exists seed. eexists (max size1 size2).
    move : H1' H2'. case : g => [g] /= H1' H2'.
    rewrite Hs. rewrite H1'. move : H2'. by case (f a).
Qed.
