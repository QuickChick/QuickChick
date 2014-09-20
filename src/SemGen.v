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
  move => A x. rewrite /semGen /set_eq => a. split.
  - move => [seed [size H]] //.
  - move => H /=. rewrite H.
    exists randomSeedInhabitant. exists 0. reflexivity.
Qed.
