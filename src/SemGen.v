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
  forall A, m1 A <-> m2 A.

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

(* We clearly need to reason about sizes:
   generators need to be size-monotonous functions *)
(* Went for the most explicit way of doing this,
   could later try to use type classes to beautify/automate things *)
Definition sizeMon {A : Type} (g : Gen A) := forall size1 size2,
  (size1 <= size2)%coq_nat ->
  semSize g size1 ---> semSize g size2.

(* One alternative (that doesn't really seem to work)
   is to add size-monotonicity directly into semGen *)
Definition semGenMon {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists size, forall size',
   (size <= size')%coq_nat ->
   semSize g size' a.

(* Sanity check: the size-monotonic semantics corresponds to the
   natural one on all size-monotonic generators *)
Lemma semGenSemGenMon : forall A (g : Gen A),
  sizeMon g ->
  semGen g <--> semGenMon g.
Proof.
  rewrite /semGen /semGenMon /sizeMon.
  move => A g Mon a. split.
  - move => [size H]. exists size => size' Hsize'.
    eapply Mon. exact Hsize'. exact H.
  - move => [size H]. specialize (H size (le_refl _)). eexists. exact H.
Qed.

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
  (* setoid_rewrite H. -- failed constraints *)
  move => a. split.
  - move => [size H]. (* setoid_rewrite semReturnSize in H. *)
    rewrite <- G. exact H.
  - move => H. exists 0. by rewrite G.
Qed.

Lemma semReturnMon : forall A (x : A),
  semGenMon (returnG x) <--> eq x.
Proof.
  move => A x a. rewrite /semGenMon. split.
  - move => [size H]. specialize (H size (le_refl _)). by move : H => /= [y H].
  - move => H /=. rewrite H.
    exists 0 => [size _]. exists randomSeedInhabitant. reflexivity.
Qed.

(* This seems like a very strong assumption;
   for cardinality reasons it requires RandomGen to be infinite *)
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

(* This should just use semBindSize *)
Lemma semBind : forall A B (g : Gen A) (f : A -> Gen B),
  sizeMon g ->
  (forall a, sizeMon (f a)) ->
  semGen (bindG g f) <--> fun b => exists a, (semGen g) a /\ (semGen (f a)) b.
Proof.
  move => A B g f MonG MonF b. rewrite /semGen /bindG => /=. split.
  - move : MonG. case : g => [g] MonG [size [seed H]]. move : H. simpl.
    case (rndSplit seed) => [seed1 seed2].
    exists (g seed1 size). split; do 2 eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[size1 H1] [size2 H2]]].
    assert (Hs1 : (size1 <= max size1 size2)%coq_nat) by apply Max.le_max_l.
    case (MonG _ _ Hs1 _ H1) => [seed1' H1'].
    assert (Hs2 : (size2 <= max size1 size2)%coq_nat) by apply Max.le_max_r.
    case (MonF _ _ _ Hs2 _ H2) => [seed2' H2'].
    exists (max size1 size2). clear H1 H2.
    case (rndSplitAssumption seed1' seed2') => [seed Hs].
    exists seed.
    move : H1' H2'. move : MonG. case : g => [g] MonG /= H1' H2'.
    rewrite Hs. rewrite H1'. move : H2'. by case (f a).
Qed.

(* This should just use semBindSize *)
Lemma semBindMon : forall A B (g : Gen A) (f : A -> Gen B),
  semGenMon (bindG g f) <-->
  fun b => exists a, (semGenMon g) a /\ (semGenMon (f a)) b.
Proof.
  move => A B g f b. rewrite /semGenMon /bindG => /=. split.
  - (* couldn't prove this (previously easy) case any more;
       the quantifier alternation is bad, we can no longer choose a so early *)
    case : g => [g] /= [size H]. pose proof (H size (le_refl _)) as H'.
    move : H' => [seed H']. move : H'.
    case (rndSplit seed) => [seed1 seed2].
    exists (g seed1 size). split; exists size => size' Hsize'.
    compute. admit. (* stuck *)
    rewrite <- H'. case (f (g seed1 size)). compute. admit. (* stuck *)
  - (* this other case got easier, and it holds unconditionally *)
    move => [a [[size1 H1] [size2 H2]]].
    exists (max size1 size2) => size Hsize.
    assert (Hs1 : (size1 <= max size1 size2)%coq_nat) by apply Max.le_max_l.
    assert (Hs2 : (size2 <= max size1 size2)%coq_nat) by apply Max.le_max_r.
    specialize (H1 size (le_trans _ _ _ Hs1 Hsize)).
    specialize (H2 size (le_trans _ _ _ Hs2 Hsize)).
    case H1 => [seed1' H1'].
    case H2 => [seed2' H2']. clear H1 H2.
    case (rndSplitAssumption seed1' seed2') => [seed Hs].
    exists seed.
    move : H1' H2'. case : g => [g] /= H1' H2'.
    rewrite Hs. rewrite H1'. move : H2'. by case (f a).
Abort.

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

(* This has the nice abstract conclusion we want, but a super gory premise *)
Lemma semSized : forall A (f : nat -> Gen A),
  (forall size1 size1' size2,
    (size1 <= size2)%coq_nat ->
    (size1' <= size2)%coq_nat ->
    (semSize (f size1) size1' --->
     semSize (f size2) size2)) ->
  semGen (sizedG f) <--> (fun a => exists n, semGen (f n) a).
Proof.
  move => A f Mon a. rewrite /semGen /sizedG => /=. split.
  - rewrite /semSize => /=.
    move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. rewrite /semSize. by eauto.
  - move => [n [size H]]. exists (max n size).
    assert (MaxL : (n <= max n size)%coq_nat) by apply Max.le_max_l.
    assert (MaxR : (size <= max n size)%coq_nat) by apply Max.le_max_r.
    case (Mon _ _ _ MaxL MaxR _ H) => [seed H'].
    exists seed. move : H'. simpl. by case (f (max n size)).
Qed.

(* This is a stronger (i.e. unconditionally correct) spec, but still
   not as abstract as I was hoping for (and in particular not as
   abstract at what we have in SetOfOutcomes.v). C'est la vie?
   Should we just give up on completely abstracting away the sizes? *)
Lemma semSizedSize : forall A (f : nat -> Gen A),
  semGen (sizedG f) <--> (fun a => exists n, semSize (f n) n a).
Proof.
  move => A f a. rewrite /semGen /semSize /sizedG => /=. split.
  - move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. rewrite /semSize. by eauto.
  - move => [size [seed H]]. exists size. exists seed.
    move : H. case (f size) => g H. rewrite /semSize. by eauto.
Qed.

(* If we get concrete about sizes, we can also support combinators
   like resize *)
Lemma semResize : forall A (n : nat) (g : Gen A),
  semGen (resize n g) <--> semSize g n .
Proof.
  move => A n [g] a. rewrite /semGen /semSize /resize => /=. split.
  - move => [_ [seed H]]. by eauto.
  - move => [seed H]. exists 0. by eauto.
Qed.

Lemma semSuchThatMaybe : forall A (g : Gen A) (f : A -> bool),
  semGen (suchThatMaybeG g f) <-->
  (fun o => (o = None) \/ (exists y, o = Some y /\ semGen g y /\ f y)).
Proof.
  move => A g f a. rewrite /suchThatMaybeG.
  admit. (* looks a bit scarry *)
Admitted.

Definition roseRoot {A : Type} (ra : Rose A) : A :=
  match ra with
    | MkRose r _ => r
  end.

Lemma semPromote : forall A (m : Rose (Gen A)),
  semGen (promoteG m) <-->
  fun b => exists a, semGen (roseRoot m) a /\ b = (MkRose a (lazy nil)).
Proof.
  move => A m a. rewrite /promoteG /fmapRose.
  admit. (* looks a bit scarry *)
Admitted.
