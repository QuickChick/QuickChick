Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random.
Require Import Ensembles.

Set Implicit Arguments.

Import ListNotations.

(* Do we want to keep seq_eq, set_incl? There are similar definitions
      at Ensembles library *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall (a : A), m1 a <-> m2 a.

Infix "<-->" := set_eq (at level 70, no associativity) : sem_gen_scope.

Definition set_incl {A} (m1 m2 : Ensemble A) :=
  forall (a : A), m1 a -> m2 a.

Infix "--->" := set_incl (at level 70, no associativity) : sem_gen_scope.

Open Scope sem_gen_scope.

Module Type GenPrimitiveInterface.
   Parameter G : Type -> Type.

   (* Standard (primitive) generator interface *)
   Parameter returnGen  : forall {A : Type}, A -> G A.
   Parameter bindGen :  forall {A B : Type}, G A -> (A -> G B) -> G B.
   Parameter run  : forall {A : Type}, G A -> RandomSeed -> nat -> A.
   Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
   Parameter sized : forall {A: Type}, (nat -> G A) -> G A.
   Parameter resize : forall {A: Type}, nat -> G A -> G A.
   Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A).
   Parameter suchThatMaybe : forall {A : Type}, G A -> (A -> bool) ->
                                                G (option A).
   Parameter choose : forall {A : Type} `{Random A}, (A * A) -> G A.
   Parameter sample : forall {A : Type}, G A -> list A.


   (* Set of outcomes definitions *)
   Parameter semSize : forall {A : Type}, G A -> nat -> Ensemble A.

   Definition semGen {A : Type} (g : G A) : Ensemble A :=
     fun a => exists size, semSize g size a.

   Hypothesis semReturn :
     forall A (x : A), semGen (returnGen x) <--> eq x.
   Hypothesis semReturnSize :
     forall A (x : A) (size : nat), semSize (returnGen x) size <--> eq x.

   Hypothesis semBindSize :
     forall A B (g : G A) (f : A -> G B) (size : nat),
       semSize (bindGen g f) size <-->
       fun b => exists a, (semSize g size) a /\
                          (semSize (f a) size) b.

   Hypothesis semFmap :
     forall A B (f : A -> B) (g : G A),
       semGen (fmap f g) <-->
       (fun b => exists a, (semGen g) a /\ b = f a).
   Hypothesis semFmapSize :
     forall A B (f : A -> B) (g : G A) (size : nat),
       semSize (fmap f g) size <-->
       (fun b => exists a, (semSize g size) a /\ b = f a).

   Hypothesis semChoose :
     forall A `{Random A} a1 a2,
       semGen (choose (a1,a2)) <-->
       (fun a => Random.leq a1 a /\ Random.leq a a2).
   Hypothesis semChooseSize :
     forall A `{Random A} a1 a2 (size : nat),
       semSize (choose (a1,a2)) size <-->
       (fun a => Random.leq a1 a /\ Random.leq a a2).


   Hypothesis semSized :
     forall A (f : nat -> G A),
       semGen (sized f) <--> (fun a => exists n, semSize (f n) n a).

   Hypothesis semSizedSize :
     forall A (f : nat -> G A) s,
       semSize (sized f) s <--> (fun a => semSize (f s) s a).

   Hypothesis semResize :
     forall A (n : nat) (g : G A),
       semGen (resize n g) <--> semSize g n .

   (* We need an completeness as well - this is not exact *)
   Hypothesis semSuchThatMaybe_sound:
     forall A (g : G A) (f : A -> bool),
       semGen (suchThatMaybe g f) --->
       (fun o => o = None \/
                 (exists y, o = Some y /\ semGen g y /\ f y)).

   (* This is too concrete, but I need it to prove shrinking.
      Does this reveal a weakness in our framework?
      Should we try to get rid of this?  *)

   Hypothesis semPromote :
     forall A (m : Rose (G A)),
       semGen (promote m) <-->
       fun (t : (Rose A)) =>
         exists seed size,
          (fmapRose (fun (g : G A) => run g seed size) m) = t.
   Hypothesis semPromoteSize :
     forall (A : Type) (m : Rose (G A)) n,
       semSize (promote m) n <-->
       (fun t : Rose A =>
          exists (seed : Axioms.RandomSeed),
            fmapRose (fun g : G A => run g seed n) m = t).


   (* These are the two statements we prove about generators *)
   Hypothesis semGenCorrect :
     forall A (g : G A) (x : A),
         semGen g x <-> exists size seed, run g seed size = x.

   (* Those are too concrete, but I need them to prove shrinking.
      Does this reveal a weakness in our framework?
      Should we try to get rid of this?
      This is expected since the spec of promote is too concrete. *)

   Hypothesis runFmap :
     forall (A B : Type) (f : A -> B) (g : G A) seed size b,
       run (fmap f g) seed size = b  <->
       (exists a : A, run g seed size = a /\ b = f a).
   Hypothesis runPromote :
     forall A (m : Rose (G A)) seed size o,
       run (promote m) seed size = o <->
       (fmapRose (fun (g : G A) => run g seed size) m) = o.

End GenPrimitiveInterface.

Module Gen : GenPrimitiveInterface.

   Inductive GenType (A : Type) : Type :=
   | MkGen : (RandomSeed -> nat -> A (** RandomSeed*)) -> GenType A.

   Definition G := GenType.

   Definition run {A : Type} (g : G A) : RandomSeed -> nat -> A :=
     match g with MkGen f => f end.

   Definition returnGen {A : Type} (x : A) : G A :=
     MkGen (fun _ _ => x).

   Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
     MkGen (fun r n =>
              let (r1,r2) := randomSplit r in
               run (k (run g r1 n)) r2 n).

   Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
     MkGen (fun r n => f ((run g) r n)).

   Definition sized {A : Type} (f : nat -> G A) : G A :=
     MkGen (fun r n => match f n with MkGen m => m r n end).

   Definition resize {A : Type} (n : nat) (g : G A) : G A :=
     match g with
       | MkGen m => MkGen (fun r _ => m r n)
     end.

   Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
     MkGen (fun r n => fmapRose (fun g => run g r n) m).

   (* ZP: Split suchThatMaybe into two different functions
        to make a proof easier *)
   Definition suchThatMaybeAux {A : Type} (g : G A) (p : A -> bool) :=
     fix aux (k : nat) (n : nat) : G (option A) :=
     match n with
       | O => returnGen None
       | S n' =>
         bindGen (resize (2 * k + n) g) (fun x =>
                                           if p x then returnGen (Some x)
                                           else aux (S k) n')
     end.

   Definition suchThatMaybe {A : Type} (g : G A) (p : A -> bool)
   : G (option A) :=
     sized (fun x => suchThatMaybeAux g p 0 (max 1 x)).

   Fixpoint rnds (rnd : RandomSeed) (n' : nat) : list RandomSeed :=
     match n' with
       | O => nil
       | S n'' =>
         let (rnd1, rnd2) := randomSplit rnd in
         cons rnd1 (rnds rnd2 n'')
     end.

   Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
     match n with
       | O => List.rev (cons O acc)
       | S n' => createRange n' (cons n acc)
     end.

   Definition choose {A : Type} `{Random A} (range : A * A) : G A :=
     MkGen (fun r _ => fst (randomR range r)).

   Definition sample (A : Type) (g : G A) : list A :=
     match g with
       | MkGen m =>
         let rnd := mkRandomSeed 0 in
         let l := List.combine (rnds rnd 20) (createRange 20 nil) in
         List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m r n) l
     end.

   Definition semSize {A : Type} (g : G A) (size : nat) : Ensemble A :=
     fun a => exists seed, run g seed size = a.

   Definition semGen {A : Type} (g : G A) : Ensemble A :=
     fun a => exists size, semSize g size a.

   Lemma semReturnSize :
     forall A (x : A) (size : nat),
       semSize (returnGen x) size <--> eq x.
   Proof.
     move => A x a. rewrite /semSize. split.
     - move => [seed H]. by [].
     - move => H /=. rewrite H.
       exists randomSeedInhabitant. reflexivity.
   Qed.

   Lemma semReturn : forall A (x : A),
                       semGen (returnGen x) <--> eq x.
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

   Lemma semBindSize : forall A B (g : G A) (f : A -> G B) (size : nat),
                         semSize (bindGen g f) size <-->
                                 fun b => exists a, (semSize g size) a /\
                                                    (semSize (f a) size) b.
   Proof.
     move => A B [g] f size b. rewrite /semSize /bindGen => /=. split.
     - case => [seed H]. move : H.
       case (randomSplit seed) => [seed1 seed2] H.
       exists (g seed1 size). split; eexists. reflexivity.
       rewrite <- H. case (f (g seed1 size)). reflexivity.
     - move => [a [[seed1 H1] [seed2 H2]]].
       case (randomSplitAssumption seed1 seed2) => [seed Hseed].
       exists seed. rewrite Hseed. rewrite H1. move : H2. by case (f a).
   Qed.

   Lemma semFmapSize : forall A B (f : A -> B) (g : G A) (size : nat),
                         semSize (fmap f g) size <-->
                                 (fun b => exists a, (semSize g size) a /\ b = f a).
   Proof.
     move => A B f [g] size b. rewrite /semSize /fmap => /=. split.
     - move => [seed H]. exists (g seed size). by eauto.
     - move => [a [[seed H1] H2]].
       eexists. rewrite H2. rewrite <- H1. reflexivity.
   Qed.

   (* This should just use semFMapSize *)
   Lemma semFmap : forall A B (f : A -> B) (g : G A),
                     semGen (fmap f g) <-->
                            (fun b => exists a, (semGen g) a /\ b = f a).
   Proof.
     move => A B f [g] b. rewrite /semGen /semSize /fmap => /=. split.
     - move => [size [seed H]]. exists (g seed size). by eauto.
     - move => [a [[size [seed H1]] H2]].
       do 2 eexists. rewrite H2. rewrite <- H1. reflexivity.
   Qed.

   Lemma semChooseSize :
     forall A `{Random A} a1 a2 s,
       semSize (choose (a1,a2)) s <-->
       (fun a => Random.leq a1 a /\ Random.leq a a2).
   Proof.
     move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
     - move => [seed H]. apply randomRCorrect. by exists seed.
     - by move => /randomRCorrect H.
   Qed.

   Lemma semChoose :
     forall A `{Random A} a1 a2,
       semGen (choose (a1,a2)) <-->
       (fun a => Random.leq a1 a /\ Random.leq a a2).
   Proof.
     move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
     - by move => [_ /randomRCorrect H].
     - move => /randomRCorrect H. by exists 0.
   Qed.


   Lemma semSized :
     forall A (f : nat -> G A),
       semGen (sized f) <--> (fun a => exists n, semSize (f n) n a).
   Proof.
     move => A f a. rewrite /semGen /semSize /sized => /=. split.
     - move => [size [seed H]]. exists size. move : H.
       case (f size) => g H. rewrite /semSize. by eauto.
     - move => [size [seed H]]. exists size. exists seed.
       move : H. case (f size) => g H. rewrite /semSize. by eauto.
   Qed.

   Lemma semSizedSize :
     forall A (f : nat -> G A) s,
       semSize (sized f) s <--> (fun a => semSize (f s) s a).
   Proof.
     move => A f s a. rewrite /semGen /semSize /sized => /=. split.
     - move => [seed H]. exists seed. move : H.
       case (f s) => g H. rewrite /semSize. by eauto.
     - move => [seed H]. exists seed.
       move : H. case (f s) => g H. rewrite /semSize. by eauto.
   Qed.

   Lemma semResize :
     forall A (n : nat) (g : G A), semGen (resize n g) <--> semSize g n .
   Proof.
     move => A n [g] a. rewrite /semGen /semSize /resize => /=. split.
     - move => [_ [seed H]]. by eauto.
     - move => [seed H]. exists 0. by eauto.
   Qed.

   Lemma semGenSuchThatMaybeAux_sound:
     forall {A} g p k n (a : A) seed size,
       run (suchThatMaybeAux g p k n) seed size = Some a ->
       (exists size seed, run g seed size = a) /\ p a.
   Proof.
     move=> /= A g p k n. elim : n k =>  [//=| n IHn] k a seed size H.
     simpl in *. unfold run, bindGen in H.
     remember (resize (2 * k + n.+1) g) as g'.
     case: g' H Heqg'=> /= g' H Heqg'.
     case: (randomSplit seed) H Heqg'=> /= r1 r2 H Heqg'.
     remember (p (g' r1 size)) as b.
     case: b H Heqb => /= H Heqb. inversion H; subst.
     rewrite /resize in Heqg'.
     destruct g as [g]. inversion Heqg'; subst.
     split =>  //=. by eexists; eexists.
     eapply (IHn k.+1 a r2 size). rewrite -H.
       by destruct (suchThatMaybeAux g p k.+1 n).
   Qed.


   Lemma semSuchThatMaybe_sound :
     forall A (g : G A) (f : A -> bool),
       semGen (suchThatMaybe g f) --->
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

   Lemma semPromote :
     forall A (m : Rose (G A)),
       semGen (promote m) <-->
       fun (t : (Rose A)) =>
         exists seed size,
           (fmapRose (fun (g : G A) => run g seed size) m) = t.
   Proof.
     move => A rg r. split;
     move => [size [seed H]]; exists seed; exists size=> //=.
   Qed.

   Lemma semPromoteSize
   : forall (A : Type) (m : Rose (G A)) n,
       semSize (promote m) n <-->
               (fun t : Rose A =>
                  exists (seed : Axioms.RandomSeed),
                    fmapRose (fun g : G A => run g seed n) m = t).
   Proof.
     move => A rg r. split;
     move => [seed H]; exists seed=> //=.
   Qed.

   (* Those are too concrete, but I need them to prove shrinking.
      Does this reveal a weakness in our framework?
      Should we try to get rid of this?
      This is expected since the spec of promote is too concrete.
    *)
   Lemma runFmap :
     forall (A B : Type) (f : A -> B) (g : G A) seed size b,
       run (fmap f g) seed size = b  <->
       (exists a : A, run g seed size = a /\ b = f a).
   Proof.
     move => A B f g seed size b'. split => /=.
     - move => <-. eexists; split => //.
     - by move => [a [Heq1 Heq2]]; subst.
   Qed.

   Lemma runPromote :
     forall A (m : Rose (G A)) seed size o,
       run (promote m) seed size = o <->
       (fmapRose (fun (g : G A) => run g seed size) m) = o.
   Proof.
     move => A g x. split => //=.
   Qed.

   Lemma semGenCorrect :
     forall A (g : G A) (x : A),
       semGen g x <-> exists size seed, run g seed size = x.
   Proof.
     move => A g x. split => //=.
   Qed.

End Gen.
