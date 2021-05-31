(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.

From ExtLib.Structures Require Export
     Functor Applicative Monads.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import Sets Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Rename? *)
Class Producer (G : Type -> Type) :=
  {
  super :> Monad G;

  sample : forall {A}, G A -> list A;
  
  sized  : forall {A: Type}, (nat -> G A) -> G A;
  resize : forall {A: Type}, nat -> G A -> G A;
  
  semProdSize :
    forall {A : Type}, G A -> nat -> set A;
  semProd :
    forall {A : Type}, G A -> set A :=
    fun _ g => \bigcup_size semProdSize g size;
  semProdSizeOpt :
    forall {A}, G (option A) -> nat -> set A :=
    fun _ g s => somes (semProdSize g s);
  semProdOpt :
    forall {A}, G (option A) -> set A :=
    fun _ g => somes (semProd g);

  bindPf :
    forall {A B : Type} (g : G A),
      (forall (a : A), (a \in semProd g) -> G B) -> G B;
  
  }.

Lemma semProdOpt_equiv {A} {G} `{PG: Producer G}
      (g : G (option A)) :
    semProdOpt g <--> \bigcup_s semProdSizeOpt g s.
  Proof.
    split; move => [n [Hn H]];
    exists n; split; auto.
  Qed.

(** A generator is [Unsized] if its semantics does not
    depend on the runtime size *)
Class Unsized {A} {G} `{Producer G} (g : G A) :=
  unsized :
    forall s1 s2, semProdSize g s1 <--> semProdSize g s2.
  
(** Sized generators monotonic in the size parameter *)
Class SizedMonotonic {A} {G} `{Producer G}
      (g : nat -> G A) :=
  sizeMonotonic : forall s s1 s2,
    s1 <= s2 ->
    semProdSize (g s1) s \subset semProdSize (g s2) s.

(** Sized generators of option type monotonic in the size
    parameter *)
Class SizedMonotonicOpt {A} {G} `{Producer G}
      (g : nat -> G (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      s1 <= s2 ->
      semProdSizeOpt (g s1) s \subset semProdSizeOpt (g s2) s.
  
(** Generators monotonic in the runtime size parameter *)
Class SizeMonotonic {A} {G} `{Producer G} (g : G A) :=
  monotonic : forall s1 s2,
      s1 <= s2 ->
      semProdSize g s1 \subset semProdSize g s2.

(** Generators monotonic in the runtime size parameter *)
Class SizeMonotonicOpt {A} {G} `{Producer G}
      (g : G (option A)) :=
    monotonicOpt : forall s1 s2,
      s1 <= s2 ->
      semProdSizeOpt g s1 \subset semProdSizeOpt g s2.

Definition isNone {T : Type} (u : option T) :=
  match u with
    | Some _ => false
    | None => true
  end.

(** TODO: Comment *)
Class SizeAntiMonotonicNone {A} {G} `{Producer G}
      (g : G (option A)) :=
    monotonicNone : forall s1 s2,
      s1 <= s2 ->
      isNone :&: semProdSize g s2 \subset isNone :&: semProdSize g s1.

(*
(* TODO: Why does Unsized need _ when A is marked as implict! *)
Parameter unsized_alt_def :
  forall {A} {G} `{Producer G} (g : G A) `{Unsized _ _ g},
    forall s, semProdSize g s <--> semProd g.
 *)
Class ProducerSemantics G `{Producer G} :=
  {
  semReturn :
    forall A (x : A), semProd (ret x) <--> [set x];
  semReturnSize :
    forall A (x : A) size, semProdSize (ret x) size <--> [set x];

  semBindSize :
    forall A B (g : G A) (f : A -> G B) (size : nat),
      semProdSize (bind g f) size <-->
                  \bigcup_(a in semProdSize g size) semProdSize (f a) size;

  semSized :
    forall A (f : nat -> G A),
      semProd (sized f) <--> \bigcup_s semProdSize (f s) s;
  semSizedSize :
    forall A (f : nat -> G A) s,
      semProdSize (sized f) s <--> semProdSize (f s) s;

  semResize :
    forall A (n : nat) (g : G A),
      semProd (resize n g) <--> semProdSize g n;
  semResizeSize :
    forall A (s n : nat) (g : G A),
      semProdSize (resize n g) s <--> semProdSize g n;


  
  
  (*
  semBindSizeOpt :
    forall A B (g : G A) (f : A -> G (option B)) (size : nat),
      semProdSizeOpt (bind g f) size <-->
      \bigcup_(a in semProdSize g size) semProdSizeOpt (f a) size;
   *)
  
  }.

(* TODO: Prove now. 
  Lemma monad_leftid : 
    forall {A B : Type} (a: A) (f : A -> G B),
      semProd (bind (ret a) f) <--> semProd (f a).
  monad_rightid : 
    forall {A : Type} (g : G A),
      semProd (bind g ret) <--> semProd g;
  monad_assoc: 
    forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
      semProd (bind (bind ga fb) fc) <--> 
             semProd (bind ga (fun a => bind (fb a) fc))
*)        

(*
  semBindSize_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G B),
      (forall s, semProdSize g s \subset semProdSize g' s) ->
      (forall x s, semProdSize (f x) s \subset semProdSize (f' x) s) ->
      (forall s, semProdSize (bind g f) s \subset semProdSize (bind g' f') s);
  semBindSizeOpt_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G (option B)),
      (forall s, semProdSize g s \subset semProdSize g' s) ->
      (forall x s, isSome :&: semProdSize (f x) s \subset isSome :&: semProdSize (f' x) s) ->
      (forall s, isSome :&: semProdSize (bind g f) s \subset isSome :&: semProdSize (bind g' f') s);
*)

(* I'm not sure how this universal quantifier will behave *)
Section ProducerProofs.
  Variable G  : Type -> Type.
  Context `{PG: Producer G}.
  Context `{PS: @ProducerSemantics G PG}.

  Instance unsizedReturn {A} (x : A) :
    Unsized (ret x).
  Proof.
    unfold Unsized => s1 s2.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  Instance returnGenSizeMonotonic {A} (x : A) :
    SizeMonotonic (ret x).
  Proof.
    unfold Unsized => s1 s2.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  Instance returnGenSizeMonotonicOpt {A} (x : option A) :
    SizeMonotonicOpt (ret x).
  Proof.
    unfold Unsized => s1 s2 Hs.
    unfold semProdSizeOpt.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  Instance bindUnsized {A B} (g : G A) (f : A -> G B)
           `{@Unsized _ _ PG g}
           `{forall x, Unsized (f x)} :
    Unsized (bind g f).
  Proof.
    unfold Unsized => s1 s2.
    rewrite !semBindSize.
    rewrite (unsized s1 s2).
    apply eq_bigcupr => x.
    apply unsized.
  Qed.

  (* XXX these will always succeed and they have the same priority *)
  Instance bindMonotonic
           {A B} (g : G A) (f : A -> G B)
           `{@SizeMonotonic _ _ PG g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bind g f).
  Proof.
    move => s1 s2 Hs.
    rewrite !semBindSize => b [a [Hsa Hsb]].
    exists a; split => //; eapply monotonic; eauto.
  Qed.
    
  Instance bindMonotonicOpt
           {A B} (g : G A) (f : A -> G (option B))
          `{@SizeMonotonic _ _ PG g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bind g f).
  Proof.
    intros s1 s2 Hs.
    rewrite /semProdSizeOpt /somes.
    move => b /semBindSize [a [Hg Hf]].
    apply semBindSize.
    exists a; split.
    - eapply monotonic; eauto.
    - eapply monotonicOpt; eauto.
  Qed.      
  
  Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B)
          `{@SizeMonotonic _ _ PG g}
          `{forall x, semProd g x -> SizeMonotonic (f x)} : 
    SizeMonotonic (bind g f).
  Proof.
    move => s1 s2 Hleq.
    rewrite !semBindSize => b [a [H3 H4]].
    exists a; split => //.
    - now eapply monotonic; eauto.
    - eapply H0; eauto.
      eexists. split; eauto.
      now constructor.
  Qed.      
  
  Instance bindMonotonicOptStrong
           {A B} (g : G A) (f : A -> G (option B))
           `{@SizeMonotonic _ _ PG g}
           `{forall x, semProd g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bind g f).
  Proof.
    move => s1 s2 Hleq.
    rewrite /semProdSizeOpt !semBindSize /somes;
    move => b [a [H3 H4]]. 
    exists a; split => //.
    - eapply monotonic; eauto.
    - eapply H0; eauto.
      exists s1; split; rewrite /setT; eauto.
  Qed.

  Lemma unsized_alt_def :
    forall A (g : G A) `{@Unsized _ _ PG g},
    forall s, semProdSize g s <--> semProd g.
  Proof.
    move => A f H s a. split.
    move => H'. exists s. split; auto => //.
    move => [s' [_ H']]. eapply unsized; eauto.
  Qed.
  
  Lemma semBindUnsized1 {A B} (g : G A) (f : A -> G B)
        `{H : @Unsized _ _ PG g} :
    semProd (bind g f) <-->
    \bigcup_(a in semProd g) semProd (f a).
  Proof.
    rewrite /semProd. setoid_rewrite semBindSize.
    setoid_rewrite (@unsized_alt_def A g H).
    move => b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split; by [].
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. 
      exists s2. split; first by [].
      exists a. split; by [].
  Qed.

  Lemma semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B),
      (forall a, Unsized (f a)) ->
      semProd (bind g f) <--> \bigcup_(a in semProd g) semProd (f a).
  Proof.
    move=> A B g f H.
    rewrite /semProd. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split => //. 
    - intros [a [[s1 [_ H1]] [s2 [_  H2]]]].
      exists s1. split; first by []. exists a. 
      split; first by []; apply unsized_alt_def; eauto.
        by eapply unsized_alt_def; eauto.
  Qed.

  Lemma semBindSizeMonotonic {A B} (g : G A) (f : A -> G B)
        `{Hg : @SizeMonotonic _ _ PG g} `{Hf : forall a, SizeMonotonic (f a)} :
    semProd (bind g f) <--> \bigcup_(a in semProd g) semProd (f a).
  (* end semBindSizeMonotonic *)
  Proof.
    rewrite /semProd. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; (split; first (compute; by []); first by[]).
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
      split; first (compute; by []).
      exists a. split.
      eapply Hg; last eassumption. by apply/leP; apply Max.le_max_l.
      eapply Hf; last eassumption. by apply/leP; apply Max.le_max_r.
  Qed.
  
  Lemma semBindSizeMonotonicIncl_r {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B) :
    semProd g \subset s1 ->
    (forall x, semProd (f x) \subset Some @: (s2 x) :|: [set None]) -> 
    semProd (bind g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].
  Proof.
    move => H1 H2 [x |] [s [_ /semBindSize [r [Hg Hf]]]].
    - left.
      eexists; split.
      exists r; split; eauto.
      + apply H1. exists s; split; rewrite /setT; auto.
      + destruct (H2 r (Some x)).
        rewrite /semProd /setT.
        exists s; split; auto.
        * move : H => [b [Hb Heq]].
          inversion Heq; subst; clear Heq.
          eauto.
        * inversion H.
      + unfold set1; auto.
    - right; reflexivity.
  Qed.

  Lemma semBindSizeMonotonicIncl_l {A B}
        (g : G A) (f : A -> G (option B)) (s1 : set A)
        (fs : A -> set B) 
        `{Hg : @SizeMonotonic _ _ PG g}
        `{Hf : forall a, SizeMonotonicOpt (f a)} :
    s1 \subset semProd g ->
    (forall x, Some @: (fs x) \subset semProd (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semProd (bind g f).
  Proof.
    move => H1 H2 y [y' [[x [Hs1 Hfs2]] Heq]];
    inversion Heq; subst; clear Heq.
    eapply H1 in Hs1.
    assert (Hin2 : (Some @: fs x) (Some y')).
    { eexists; split; eauto. now constructor. }
    eapply H2 in Hin2.
    unfold SizeMonotonic in Hg.
    edestruct Hs1 as [s [_ Hgen]].
    edestruct Hin2 as [s' [_ Hfgen]].
    assert (Hin2' : ((fun u : option B => u) :&: semProdSize (f x) s') (Some y')).
    { split; eauto. }
    apply Hg with (s2 := s + s') in Hgen; [| now ssromega].
    rewrite /semProd.
    exists (s + s'); split; unfold setT; auto.
    apply semBindSize.
    exists x; split; auto.
    apply monotonicOpt with (s2 := s'); eauto; try ssromega.
Qed.    

  Lemma semBindRetFSize :
    forall (A B : Type) (f : A -> B) (g : G A)
           (size : nat),
      semProdSize (x <- g;; ret (f x)) size <-->
                  f @: semProdSize g size.
  Proof.
    move => A B f g size b; split.
    - move => /semBindSize [a [Ha Hfa]].
      rewrite /imset.
      exists a; split; eauto.
      apply semReturnSize in Hfa.
      inversion Hfa; subst; clear Hfa.
      unfold set1; auto.
    - move => [a [Hb Heq]]; inv Heq; clear Heq.
      apply semBindSize; exists a; split; auto.
      apply semReturnSize; unfold set1; auto.
  Qed.
  
  Lemma semBindRetF : 
    forall (A B : Type) (f : A -> B) (g : G A),
      semProd (x <- g;; ret (f x)) <--> f @: semProd g.
  Proof.
    rewrite /semProd.
    move => A B f g b; split.
    - move => [size [_ /semBindRetFSize [a [Ha Heq]]]];
      inv Heq; clear Heq.
      exists a; split; unfold set1; auto.
      exists size; split; unfold setT; auto.
    - move => [a [[size [_ H]] Heq]]; inv Heq; clear Heq.
      exists size; split; unfold setT; auto.
      apply semBindRetFSize.
      exists a; split; unfold set1; auto.
  Qed.

  Lemma semFmap :
    forall A B (f : A -> B) (g : G A),
      semProd (fmap f g) <--> f @: semProd g.
  Proof.
    rewrite /fmap /Functor_Monad /liftM.
    apply semBindRetF.
  Qed.
      
  Lemma semFmapSize :
    forall A B (f : A -> B) (g : G A) (size : nat),
      semProdSize (fmap f g) size <-->
      f @: semProdSize g size.
  Proof.
    rewrite /fmap /Functor_Monad /liftM.
    apply semBindRetFSize.
  Qed.
    
  Instance fmapUnsized {A B} (f : A -> B) (g : G A)
           `{@Unsized _ _ PG g} : 
    Unsized (fmap f g).
  Proof.
    move => s1 s2; rewrite !semFmapSize => b.
    by split; move => [a [H1 <-]];
       eexists; split; eauto => //; eapply unsized; eauto.
  Qed.

  Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{@SizeMonotonic _ _ PG g} : 
    SizeMonotonic (fmap f g).
  Proof.
    intros s1 s2 Hs.
    rewrite !semFmapSize. move => b.
    move => [a [H1 <-]]; eexists; split; eauto => //; eapply monotonic; eauto.
  Qed.

(* TODO: Move to Generator. 
  Parameter semChoose :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Parameter semChooseSize :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      forall size, (semGenSize (choose (a1,a2)) size <-->
              [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Declare Instance chooseUnsized A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
  *)

  Lemma semSized_alt A (f : nat -> G A)
        `{H : forall n, SizeMonotonic (f n)}
         (H' : forall n m s,
             n <= m ->
             semProdSize (f n) s \subset semProdSize (f m) s) :
    semProd (sized f) <--> \bigcup_n (semProd (f n)).
  Proof.
    rewrite semSized.
    move => x; split.
    - move => [n [HT Hs]].
      eexists. split; eauto. eexists; eauto.
    - move => [n [HT [m [_ Hs]]]].
      eapply semSized. eexists (m + n).
      split; [ constructor |].
      apply semSizedSize.
      eapply (H' n). ssromega.
      eapply (H n); try eassumption. ssromega.
  Qed.
  
  Lemma semSized_opt A (f : nat -> G (option A))
        `{H : forall n, SizeMonotonicOpt (f n)}
        `{H' : @SizedMonotonicOpt _ _ PG f} :
    isSome :&: semProd (sized f) <-->
    isSome :&: \bigcup_n (semProd (f n)).
  Proof.
    rewrite semSized. rewrite !setI_bigcup_assoc.
    move => x; split.
    - move => [n [HT [Hs1 Hs2]]].
      eexists. split; eauto. split; eauto. eexists; eauto.
    - move => [n [HT [Hs1 [m [HT' Hs2]]]]].
      eexists (m + n).
      split. now constructor. 
      split; [ eassumption | ].
      destruct x as [ x | ].
      + eapply monotonicOpt with (s2 := m + n) in Hs2; [| now ssromega ].
        eapply sizeMonotonicOpt with (s1 := n) (s2 := m + n); [now ssromega |].
        auto.
      + inv Hs1.
  Qed.

  Instance sizedSizeMonotonic
           A (gen : nat -> G A)
           `{forall n, SizeMonotonic (gen n)}
           `{@SizedMonotonic _ _ PG gen} :
    SizeMonotonic (sized gen).
  Proof.
    move => s1 s2 Hleq a /semSizedSize H1.
    eapply semSizedSize.
    eapply H. eassumption.
    eapply H0; eassumption.
  Qed.

  Instance sizedSizeMonotonicOpt
           A (gen : nat -> G (option A))
           `{forall n, SizeMonotonic (gen n)}
           `{@SizedMonotonicOpt _ _ PG gen} :
    SizeMonotonicOpt (sized gen).
  Proof.
    move => s1 s2 Hleq a H1.
    eapply semSizedSize.
    eapply H. eassumption.
    eapply sizeMonotonicOpt; eauto.    
    unfold semProdSizeOpt in *; unfold somes in *.
    apply semSizedSize in H1.
    auto.
  Qed.
  
  Instance unsizedResize {A} (g : G A) n :
    Unsized (resize n g).
  Proof.
    move => s1 s2.
    rewrite !semResizeSize.
    split; auto.
  Qed.    

End ProducerProofs.  
