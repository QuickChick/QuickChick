(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat seq eqtype.

From ExtLib.Structures Require Export
     Functor Applicative Monads.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import Sets Tactics RandomQC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope set_scope.

Import ListNotations.

(* Rename? *)
Class Producer (G : Type -> Type) :=
  {
  super :> Monad G;

  sample : forall {A}, G A -> list A;
  
  sized  : forall {A: Type}, (nat -> G A) -> G A;
  resize : forall {A: Type}, nat -> G A -> G A;

  choose : forall {A : Type} `{ChoosableFromInterval A}, (A * A) -> G A;
  
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
    (s1 <= s2)%coq_nat ->
    semProdSize (g s1) s \subset semProdSize (g s2) s.

(** Sized generators of option type monotonic in the size
    parameter *)
Class SizedMonotonicOpt {A} {G} `{Producer G}
      (g : nat -> G (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      (s1 <= s2)%coq_nat ->
      semProdSizeOpt (g s1) s \subset semProdSizeOpt (g s2) s.
  
(** Generators monotonic in the runtime size parameter *)
Class SizeMonotonic {A} {G} `{Producer G} (g : G A) :=
  monotonic : forall s1 s2,
      (s1 <= s2)%coq_nat ->
      semProdSize g s1 \subset semProdSize g s2.

(** Generators monotonic in the runtime size parameter *)
Class SizeMonotonicOpt {A} {G} `{Producer G}
      (g : G (option A)) :=
    monotonicOpt : forall s1 s2,
      (s1 <= s2)%coq_nat ->
      semProdSizeOpt g s1 \subset semProdSizeOpt g s2.

(** A fixed point is reached when the producer no longer produces None *)
Class SizeFP {A} {G} `{Producer G} (g : G (option A)) :=
  sizeFP : forall s1 s2,
    (s1 <= s2)%coq_nat ->
    ~ None \in semProdSize g s1 -> 
    semProdSize g s1 <--> semProdSize g s2.

Class SizedFP {A} {G} `{Producer G} (g :nat -> G (option A)) :=
  sizedFP : forall s s1 s2,
    (s1 <= s2)%coq_nat ->
    ~ None \in semProdSize (g s1) s -> 
    semProdSize (g s1) s <--> semProdSize (g s2) s.

Definition isNone {T : Type} (u : option T) :=
  match u with
    | Some _ => false
    | None => true
  end.

Class SizedAntimonotonicNone {A} {G} `{Producer G}
      (g : nat -> G (option A)) :=
    monotonicNone : forall s s1 s2,
    (s1 <= s2)%coq_nat ->    
    isNone :&: semProdSize (g s2) s \subset isNone :&: semProdSize (g s1) s. 

(** FP + SizeMon *)
Class SizeMonotonicOptFP {A} {G} {H : Producer G}
      (g : G (option A)) :=
  { IsMon :> @SizeMonotonicOpt _ _ H g;
    IsFP  :> @SizeFP _ _ H g }.

Class SizedMonotonicOptFP {A} {G} {H : Producer G}
      (g : nat -> G (option A)) :=
  { IsMonSized :> @SizedMonotonicOpt _ _ H g;
    IsFPSized  :> @SizedFP _ _ H g;
    IsAntimon  :> @SizedAntimonotonicNone _ _ _ g }.

#[global] Instance SizeMonotonicOptFP_FP {A} {G}
       (g : G (option A))
       `{SizeMonotonicOptFP A G g} : SizeFP g.
Proof. inv H0. eassumption. Qed.

#[global] Instance SizeMonotonicOptFP_SizeMonotonic {A} {G}
       (g : G (option A))
       `{SizeMonotonicOptFP A G g} : SizeMonotonicOpt g.
Proof. inv H0. eassumption. Qed.


#[global] Instance SizedMonotonicOptFP_FP {A} {G}
       (g : nat -> G (option A))
       `{SizedMonotonicOptFP A G g} : SizedFP g.
Proof. inv H0. eassumption. Qed.

#[global] Instance SizedMonotonicOptFP_SizeMonotonic {A} {G}
       (g : nat -> G (option A))
       `{SizedMonotonicOptFP A G g} : SizedMonotonicOpt g.
Proof. inv H0. eassumption. Qed.


#[global] Instance SizedMonotonicOptFP_Antimonotonic {A} {G}
       (g : nat -> G (option A))
       `{SizedMonotonicOptFP A G g} : SizedAntimonotonicNone g.
Proof. inv H0. eassumption. Qed.




(*
(* TODO: Why does Unsized need _ when A is marked as implict! *)
Parameter unsized_alt_def :
  forall {A} {G} `{Producer G} (g : G A) `{Unsized _ _ g},
    forall s, semProdSize g s <--> semProd g.
 *)

#[global] Instance unsizedMonotonic {A} {G} `{PG :Producer G}
         (g : G A) `{@Unsized A G PG g} :
SizeMonotonic g. 
Proof.
    intros s1 s2 Hleq.
    rewrite /unsized /monotonic => a H12.
    eapply unsized; eauto.
Qed.

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

  semChoose :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]);

  semChooseSize :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      forall size, (semProdSize (choose (a1,a2)) size <-->
              [set a | RandomQC.leq a1 a && RandomQC.leq a a2]);

  (* semChooseSizeEmpty : *)
  (*   forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A), *)
  (*     ~ (RandomQC.leq a1 a2) -> *)
  (*     forall size, (semProdSize (choose (a1,a2)) size <--> *)
  (*                               set0); *)
  
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

(*
*)

(* I'm not sure how this universal quantifier will behave *)
Section ProducerProofs.
  Variable G  : Type -> Type.
  Context `{PG: Producer G}.
  Context `{PS: @ProducerSemantics G PG}.

  Lemma monad_leftid : 
    forall {A B : Type} 
           (a: A) (f : A -> G B),
      semProd (bind (ret a) f) <--> semProd (f a).
  Proof.
    intros.
    rewrite /semProd.
    apply eq_bigcupr => size.
    rewrite semBindSize semReturnSize bigcup_set1.
    reflexivity.
  Qed.

  Lemma monad_rightid : 
    forall {A : Type} (g : G A),
      semProd (bind g ret) <--> semProd g.
  Proof.
    intros; rewrite /semProd.
    apply: eq_bigcupr => size; rewrite semBindSize.
    rewrite (eq_bigcupr _ (fun x => semReturnSize x size)).
    apply coverE.
  Qed.
  
  Lemma monad_assoc A B C (ga : G A) (fb : A -> G B) (fc : B -> G C) :
    semProd (bind (bind ga fb) fc) <--> 
    semProd (bind ga (fun a => bind (fb a) fc)).
  Proof.
    apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
    by apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
  Qed.

  #[global] Instance unsizedReturn {A} (x : A) :
    Unsized (ret x).
  Proof.
    unfold Unsized => s1 s2.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  #[global] Instance returnGenSizeMonotonic {A} (x : A) :
    SizeMonotonic (ret x).
  Proof.
    unfold Unsized => s1 s2.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  #[global] Instance returnGenSizeMonotonicOpt {A} (x : option A) :
    SizeMonotonicOpt (ret x).
  Proof.
    unfold Unsized => s1 s2 Hs.
    unfold semProdSizeOpt.
    repeat rewrite semReturnSize.
    firstorder.
  Qed.

  #[global] Instance returnGenSizeFP {A} (x : (option A)) :
    SizeFP (ret x).
  Proof.
    unfold SizeFP => s1 s2 Hleq Hnin.
    repeat rewrite semReturnSize. reflexivity. 
  Qed.


  #[global] Instance bindUnsized {A B} (g : G A) (f : A -> G B)
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
  #[global] Instance bindMonotonic
           {A B} (g : G A) (f : A -> G B)
           `{@SizeMonotonic _ _ PG g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bind g f).
  Proof.
    move => s1 s2 Hs.
    rewrite !semBindSize => b [a [Hsa Hsb]].
    exists a; split => //; eapply monotonic; eauto.
  Qed.   
    
  #[global] Instance bindMonotonicOpt
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

  #[global] Instance bindMonotonicStrong
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

  #[global] Instance bindMonotonicOptStrong
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
      eapply Hg; last eassumption. lia.
      eapply Hf; last eassumption. lia.
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
    apply monotonicOpt with (s1 := s'); eauto; try ssromega.
Qed.    

  Lemma semBindSize_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G B) :
      (forall s, semProdSize g s \subset semProdSize g' s) ->
      (forall x s, semProdSize (f x) s \subset semProdSize (f' x) s) ->
      (forall s, semProdSize (bind g f) s \subset semProdSize (bind g' f') s).
  Proof.
    intros Hs1 Hs2 s.
    rewrite !semBindSize.
    specialize (Hs1 s). 
    eapply incl_bigcup_compat; eauto.
  Qed.
  
  (* semBindSizeOpt_subset_compat : *)
  (*   forall {A B : Type} (g g' : G A) (f f' : A -> G (option B)), *)
  (*     (forall s, semProdSize g s \subset semProdSize g' s) -> *)
  (*     (forall x s, isSome :&: semProdSize (f x) s \subset isSome :&: semProdSize (f' x) s) -> *)
  (*     (forall s, isSome :&: semProdSize (bind g f) s \subset isSome :&: semProdSize (bind g' f') s); *)
  
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

  (* Needs decidability to be agnostic of impl *)
  (*
  Instance chooseUnsized A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
  Proof.
    unfold Unsized => s1 s2.
    
    split => /semChooseSize C.
    apply semChooseSize.
   *)
  
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
    
  #[global] Instance fmapUnsized {A B} (f : A -> B) (g : G A)
           `{@Unsized _ _ PG g} : 
    Unsized (fmap f g).
  Proof.
    move => s1 s2; rewrite !semFmapSize => b.
    by split; move => [a [H1 <-]];
       eexists; split; eauto => //; eapply unsized; eauto.
  Qed.

  #[global] Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{@SizeMonotonic _ _ PG g} : 
    SizeMonotonic (fmap f g).
  Proof.
    intros s1 s2 Hs.
    rewrite !semFmapSize. move => b.
    move => [a [H1 <-]]; eexists; split; eauto => //; eapply monotonic; eauto.
  Qed.

  Lemma semSized_alt A (f : nat -> G A)
        `{H : forall n, SizeMonotonic (f n)}
         (H' : forall n m s,
             (n <= m)%coq_nat ->
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

  #[global] Instance sizedSizeMonotonic
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

  #[global] Instance sizedSizeMonotonicOpt
           A (gen : nat -> G (option A))
           `{forall n, SizeMonotonicOpt (gen n)}
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

  #[global] Instance sizedSizeFP
         A (gen : nat -> G (option A))
         `{forall n, SizeFP (gen n)}
         `{@SizedFP _ _ PG gen}
         `{@SizedAntimonotonicNone _ _ _ gen}
    : SizeFP (sized gen).
  Proof.
    move => s1 s2 Hleq Hn.
    rewrite !semSizedSize.
    rewrite H0; [ | eassumption | ].
    2:{ intros Hc. eapply Hn.
        eapply semSizedSize. eassumption. }

    rewrite H; [ | eassumption | ].
    reflexivity.

    intros Hc. eapply Hn.
    eapply semSizedSize.
    assert (Hnone : None \in isNone :&: semProdSize (gen s2) s1).
    { split; eauto. }
    eapply H1 in Hnone; [| eassumption ].
    inv Hnone. eassumption. 
  Qed.
  
  #[global] Instance unsizedResize {A} (g : G A) n :
    Unsized (resize n g).
  Proof.
    move => s1 s2.
    rewrite !semResizeSize.
    split; auto.
  Qed.    

  
End ProducerProofs.  

Section ProducerHigh.
  Context {G : Type -> Type}.
  Context `{PG: Producer G}.

  Definition vectorOf {A : Type} (k : nat) (g : G A)
    : G (list A) :=
    foldr (fun m m' =>
                bind m (fun x =>
                bind m' (fun xs => ret (cons x xs)))
             ) (ret nil) (nseq k g).
  
  Definition listOf {A : Type} (g : G A) : G (list A) :=
    sized (fun n => bind (choose (0, n)) (fun k => vectorOf k g)).

  Definition oneOf_ {A : Type} (def: G A) (gs : list (G A)) : G A :=
    bind (choose (0, length gs - 1)) (nth def gs).

  Definition oneOfT_ {A : Type} (def: unit -> G A) (gs : list (unit -> G A)) : G A :=
    bind (choose (0, length gs - 1)) (fun i => nth def gs i tt).
  
  Definition elems_ {A : Type} (def : A) (l : list A) :=
    let n := length l in
    bind (choose (0, n - 1)) (fun n' =>
    ret (List.nth n' l def)).
  
  Definition liftProd4 {A1 A2 A3 A4 R}
             (F : A1 -> A2 -> A3 -> A4 -> R)
             (m1 : G A1) (m2 : G A2) (m3 : G A3) (m4: G A4)
    : G R := nosimpl(
                 x1 <- m1;;
                 x2 <- m2;;
                 x3 <- m3;;
                 x4 <- m4;;
                 ret (F x1 x2 x3 x4)).

  Definition liftProd5 {A1 A2 A3 A4 A5 R}
           (F : A1 -> A2 -> A3 -> A4 -> A5 -> R)
           (m1 : G A1) (m2 : G A2) (m3 : G A3) (m4: G A4) (m5 : G A5)
    : G R := nosimpl(
                 x1 <- m1;;
                 x2 <- m2;;
                 x3 <- m3;;
                 x4 <- m4;;
                 x5 <- m5;;
                 ret (F x1 x2 x3 x4 x5)).

  Definition sequenceProd {A : Type} (ms : list (G A)) : G (list A) :=
    foldr (fun m m' => x <- m;;
                       xs <- m';;
                       ret (x :: xs)) (ret nil) ms. 

  Fixpoint foldProd {A B : Type} (f : A -> B -> G A) (l : list B) (a : A)
    : G A := nosimpl(
                 match l with
                 | nil => ret a
                 | (x :: xs) => bind (f a x) (foldProd f xs)
                 end).

  Definition bindOpt {A B}
             (g : G (option A)) (f : A -> G (option B)) : G (option B) :=
    bind g (fun ma =>
              match ma with
              | None => ret None
              | Some a => f a
              end).
  
End ProducerHigh.

Module BindOptNotation.

  Notation "x <-- c1 ;; c2" := (@bindOpt _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

End BindOptNotation.  

Section ProducerHighProofs.
  Variable G  : Type -> Type.
  Context `{PG: Producer G}.
  Context `{PS: @ProducerSemantics G PG}.

(* * Semantics *)

Lemma semLiftGen {A B} (f: A -> B) (g: G A) :
  semProd (liftM f g) <--> f @: semProd g.
Proof.
  rewrite imset_bigcup. apply: eq_bigcupr => size.
    by rewrite semBindSize (eq_bigcupr _ (fun a => semReturnSize (f a) size)).
Qed.

Ltac solveLiftProdX :=
intros; split; intros;
repeat
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H as [? [? ?]]
    | [ H : semProdSize _ _ _ |- _ ] =>
      try (apply semBindSize in H; destruct H as [? [? ?]]);
      try (apply semReturnSize in H; subst)
  end;
  [ by repeat (eexists; split; [eassumption |])
  | repeat (apply semBindSize; eexists; split; try eassumption);
      by apply semReturnSize ].

Lemma semLiftProdSize {A B} (f: A -> B) (g: G A) size :
  semProdSize (liftM f g) size <--> f @: (semProdSize g size).
Proof. 
    by rewrite semBindSize (eq_bigcupr _ (fun a => semReturnSize (f a) size)).
 Qed.

Program Instance liftProdUnsized {A B} (f : A -> B) (g : G A) 
        `{@Unsized _ _ PG g} : Unsized (liftM f g).
Next Obligation.
  by rewrite ! semLiftProdSize (unsized s1 s2).
Qed.

Program Instance liftProdMonotonic {A B} (f : A -> B) (g : G A) 
        `{@SizeMonotonic _ _ PG g} : SizeMonotonic (liftM f g).
Next Obligation.
  rewrite ! semLiftProdSize. apply imset_incl. by apply monotonic.
Qed.

Lemma semLiftProd2Size {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s :
  semProdSize (liftM2 f g1 g2) s <-->
  f @2: (semProdSize g1 s, semProdSize g2 s).
Proof. 
  rewrite semBindSize curry_imset2l; apply: eq_bigcupr => x.
    by rewrite semBindSize; apply: eq_bigcupr => y; rewrite semReturnSize.
Qed.

     
Lemma semLiftProd2SizeMonotonic {A1 A2 B} (f: A1 -> A2 -> B)
                               (g1 : G A1) (g2 : G A2) 
                               `{@SizeMonotonic _ _ PG g1} `{@SizeMonotonic _ _ PG g2} :
  semProd (liftM2 f g1 g2) <--> f @2: (semProd g1, semProd g2).
Proof.
  rewrite /semProd. setoid_rewrite semLiftProd2Size.
  move => b. split. 
  - move => [sb [_ Hb]]. (* point-free reasoning would be nice here *)
    destruct Hb as [a [[Hb11 Hb12] Hb2]]. exists a. split; [| by apply Hb2].
    split; eexists; by split; [| eassumption].
  - move => [[a1 a2] [[[s1 [_ G1]] [s2 [_ G2]]] Hf]]. compute in Hf.
    exists (max s1 s2). split; first by [].
    exists (a1,a2). split; last by [].
    split => /=; (eapply monotonic; last eassumption). lia. lia.
Qed.

Lemma semLiftProd2Unsized1 {A1 A2 B} (f: A1 -> A2 -> B)
      (g1 : G A1) (g2 : G A2) `{@Unsized _ _ PG g1}:
  semProd (liftM2 f g1 g2) <--> f @2: (semProd g1, semProd g2).
Proof.
  rewrite /semProd. setoid_rewrite semLiftProd2Size.
  move=> b. split.
  - move => [n [_ [[a1 a2] [[/= H2 H3] H4]]]]. exists (a1, a2).
    split; auto; split; eexists; split; eauto; reflexivity.
  - move => [[a1 a2] [[[s1 /= [H2 H2']] [s2 [H3 H3']]] H4]].
    eexists. split; first by eauto. 
    exists (a1, a2); split; eauto.
    split; last by eauto. simpl. 
    eapply unsized; eauto; apply (unsized2 H); eauto.
Qed.
  
Lemma semLiftProd2Unsized2 {A1 A2 B} (f: A1 -> A2 -> B)
      (g1 : G A1) (g2 : G A2) `{@Unsized _ _ PG g2}:
  semProd (liftM2 f g1 g2) <--> f @2: (semProd g1, semProd g2).
Proof.
  rewrite /semProd. setoid_rewrite semLiftProd2Size.
  move=> b. split. 
  - move => [n [_ [[a1 a2] [[/= H2 H3] H4]]]]. exists (a1, a2).
    split; auto; split; eexists; split; eauto; reflexivity.
  - move => [[a1 a2] [[[s1 /= [H2 H2']] [s2 [H3 H3']]] H4]].
    eexists. split; first by auto.
    exists (a1, a2). split; eauto.
    split; first by eauto. simpl. 
    eapply unsized; eauto.
Qed.

Lemma semLiftProd3Size :
forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B)
       (g1: G A1) (g2: G A2) (g3: G A3) size,
  semProdSize (liftM3 f g1 g2 g3) size <-->
  fun b =>
    exists a1, semProdSize g1 size a1 /\
               (exists a2, semProdSize g2 size a2 /\
                           (exists a3, semProdSize g3 size a3 /\
                                       (f a1 a2 a3) = b)).
Proof. solveLiftProdX. Qed.

#[global] Program Instance liftM2Unsized {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{@Unsized _ _ PG g1} (g2 : G A2) `{@Unsized _ _ PG g2} : Unsized (liftM2 f g1 g2).
Next Obligation.
  rewrite ! semLiftProd2Size. 
  rewrite ! curry_imset2l. by setoid_rewrite (unsized s1 s2).
Qed.

#[global] Program Instance liftM2Monotonic {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{@SizeMonotonic _ _ PG g1} (g2 : G A2)
        `{@SizeMonotonic _ _ PG g2} : 
  SizeMonotonic (liftM2 f g1 g2).
Next Obligation.
  rewrite ! semLiftProd2Size. rewrite ! curry_imset2l. 
  move => b [a1 [Ha1 [a2 [Ha2 <-]]]].
  do 2 (eexists; split; first by eapply (monotonic H1); eauto).
  reflexivity.
Qed.


(* CH: Made this more beautiful than the rest *)
(* CH: Should anyway use dependent types for a generic liftMN *)
Lemma semLiftProd4Size A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
                     (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4) s :
  semProdSize (liftProd4 f g1 g2 g3 g4) s <-->
  [set b : B | exists a1 a2 a3 a4, semProdSize g1 s a1 /\ semProdSize g2 s a2 /\
                 semProdSize g3 s a3 /\ semProdSize g4 s a4 /\ f a1 a2 a3 a4 = b].
Proof.
  split; unfold liftProd4; intros.
  - repeat match goal with
    | [ H : semProdSize _ _ _ |- _ ] =>
      try (apply semBindSize in H; destruct H as [? [? ?]]);
      try (apply semReturnSize in H; subst)
    end.
    do 4 eexists. repeat (split; [eassumption|]). assumption.
  - repeat match goal with
    | [ H : exists _, _ |- _ ] => destruct H as [? [? ?]]
    | [ H : and _ _ |- _ ] => destruct H as [? ?]
    end.
    repeat (apply semBindSize; eexists; split; [eassumption|]).
    apply semReturnSize. assumption.
Qed.

(* begin semLiftProd4SizeMonotonic *)
Lemma semLiftProd4SizeMonotonic A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
                               (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4)
                               `{@SizeMonotonic _ _ PG g1} `{@SizeMonotonic _ _ PG g2}
                               `{@SizeMonotonic _ _ PG g3} `{@SizeMonotonic _ _ PG g4} :
  semProd (liftProd4 f g1 g2 g3 g4) <-->
  [set b : B | exists a1 a2 a3 a4, semProd g1 a1 /\ semProd g2 a2 /\
                 semProd g3 a3 /\ semProd g4 a4 /\ f a1 a2 a3 a4 = b].
(* end semLiftProd4SizeMonotonic *)
Proof.
  rewrite /semProd. setoid_rewrite semLiftProd4Size. 
  move => b. split. 
  - move => [s [_ [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 Hb]]]]]]]]]]; subst.
    exists a1. exists a2. exists a3. exists a4. 
    repeat split; exists s; (split; [reflexivity | eassumption ]). 
  -  move => [a1 [a2 [a3 [a4 [[s1 [_ Ha1]] 
                                [[s2 [_ Ha2]] 
                                   [[s3 [_ Ha3]] 
                                      [[s4 [_ Ha4]] Hb]]]]]]]]; subst.
     exists (max s1 (max s2 (max s3 s4))). 
     split; first by [].
     exists a1. exists a2. exists a3. exists a4.  
     repeat split; (eapply monotonic; last eassumption); lia.
Qed.

#[global] Program Instance liftM4Monotonic {A B C D E} 
        (f : A -> B -> C -> D -> E)
        (g1 : G A) (g2 : G B) (g3 : G C) (g4 : G D) 
        `{ @SizeMonotonic _ _ PG g1} `{ @SizeMonotonic _ _ PG g2}
        `{ @SizeMonotonic _ _ PG g3} `{ @SizeMonotonic _ _ PG g4} 
: SizeMonotonic (liftProd4 f g1 g2 g3 g4). 
Next Obligation.
  rewrite ! semLiftProd4Size.
  move => t /= [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 H5]]]]]]]]; subst.
  eexists. eexists. eexists. eexists. 
  repeat (split; try reflexivity); by eapply monotonic; eauto. 
Qed.

Lemma semLiftProd5Size :
forall {A1 A2 A3 A4 A5 B} (f: A1 -> A2 -> A3 -> A4 -> A5 -> B)
       (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) (g5: G A5) size,
  semProdSize (liftProd5 f g1 g2 g3 g4 g5) size <-->
  fun b =>
    exists a1, semProdSize g1 size a1 /\
               (exists a2, semProdSize g2 size a2 /\
                           (exists a3, semProdSize g3 size a3 /\
                                       (exists a4, semProdSize g4 size a4 /\
                                                   (exists a5, semProdSize g5 size a5 /\
                                                               (f a1 a2 a3 a4 a5) = b)))).
Proof. solveLiftProdX. Qed.

Lemma Forall2_cons T U (P : T -> U -> Prop) x1 s1 x2 s2 :
  List.Forall2 P (x1 :: s1) (x2 :: s2) <-> P x1 x2 /\ List.Forall2 P s1 s2.
Proof.
split=> [H|[? ?]]; last by constructor.
by inversion H.
Qed.

Lemma semSequenceProdSize A (gs : list (G A)) n :
  semProdSize (sequenceProd gs) n <-->
  [set l | length l = length gs /\
    List.Forall2 (fun y => semProdSize y n) gs l].
Proof.
elim: gs => [|g gs IHgs].
  by rewrite semReturnSize /set1; case=> // a l; split=> // [[]].
rewrite /= semBindSize; setoid_rewrite semBindSize; setoid_rewrite semReturnSize.
setoid_rewrite IHgs; case=> [| x l].
  split; first by case=> ? [? [? [?]]].
  by move=> H; inversion H.
rewrite Forall2_cons; split; first by case=> y [gen_y [s [[<- ?]]]] [<- <-].
by case=> [[<-] [? ?]]; exists x; split => //; exists l; split.
Qed.

Lemma Forall2_SizeMonotonic {A} x n (gs : list (G A)) l :
  (x <= n)%coq_nat -> gs \subset SizeMonotonic -> 
  List.Forall2 (semProdSize^~ x) gs l ->
  List.Forall2 (semProdSize^~ n) gs l.
Proof. 
  intros. induction H1; auto.
  apply subconsset in H0. destruct H0; auto. 
  constructor; auto. eapply H0; eauto.
Qed.

Lemma semSequenceProdSizeMonotonic A (gs : list (G A)) :
  (gs \subset SizeMonotonic) ->
  semProd (sequenceProd gs) <-->
  [set l | length l = length gs /\
    List.Forall2 semProd gs l].
Proof.
  intros. rewrite /semProd. setoid_rewrite semSequenceProdSize.
  move => l. split.
  - move => [n [ _ [H1 H2]]]. split; auto.
    induction H2; subst; simpl; constructor.
    + exists n. split; auto. reflexivity. 
    + apply IHForall2; eauto. 
      apply subconsset in H. destruct H; auto. 
  - move => [H1 H2]. revert gs H H1 H2. induction l; intros gs H H1 H2.
    + destruct gs; try discriminate. exists 0. 
      split; auto. reflexivity.
    + destruct gs; try discriminate.
      apply subconsset in H. move : H => [H3 H4].  
      inversion H2; subst. destruct H6 as [n [ _ H5]].
      eapply IHl in H8; auto. destruct H8 as [x [_ [H7 H8]]].
      
      destruct (le_dec x n) eqn:Hle. 
      { exists n. split; eauto; first by reflexivity. split; auto. 
        constructor; auto. eapply Forall2_SizeMonotonic; eauto. }
      { exists x.  split; first by reflexivity. split; auto.
        constructor; auto. eapply H3; last by eassumption. lia. }
Qed.
 
Lemma semVectorOfSize {A : Type} (k : nat) (g : G A) n :
  semProdSize (vectorOf k g) n <-->
  [set l | length l = k /\ l \subset (semProdSize g n)].
Proof.
elim: k => [|k IHk].
  rewrite /vectorOf /= semReturnSize.
  by move=> s; split=> [<-|[] /size0nil ->] //; split.
rewrite /vectorOf /= semBindSize; setoid_rewrite semBindSize.
setoid_rewrite semReturnSize; setoid_rewrite IHk.
case=> [|x l]; first by split=> [[? [? [? [?]]]] | []].
split=> [[y [gen_y [l' [[length_l' ?] [<- <-]]]]]|] /=.
  split; first by rewrite length_l'.
  exact/subconsset.
by case=> [[?]] /subconsset [? ?]; exists x; split => //; exists l.
Qed.

Lemma semVectorOfUnsized {A} (g : G A) (k : nat) `{@Unsized _ _ PG g}: 
  semProd (vectorOf k g) <--> [set l | length l = k /\ l \subset semProd g ]. 
Proof.
  rewrite /semProd.
  setoid_rewrite semVectorOfSize.
  move => l; split.
  - move => [k' [_ [H1 H2]]]. split; auto. exists k'. split; auto.
    reflexivity.
  - move => [H1 H2]. 
    exists k. split; first by reflexivity.
    split; auto. move => a /H2 [x [_ Hx]]. 
    by eapply unsized; eauto.
Qed.

#[global] Program Instance vectorOfUnsized {A} (k : nat) (g : G A) 
        `{@Unsized _ _ PG g } : Unsized (vectorOf k g).
Next Obligation.
  rewrite ! semVectorOfSize. 
  split; move => [H1 H2]; split => //; by rewrite unsized; eauto.
Qed.

#[global] Program Instance vectorOfMonotonic {A} (k : nat) (g : G A) 
        `{@SizeMonotonic _ _ PG g } : SizeMonotonic (vectorOf k g).
Next Obligation.
  rewrite ! semVectorOfSize. 
  move => l [H1 H2]; split => // a Ha. by eapply (monotonic H0); eauto.
Qed.


Lemma semListOfSize {A : Type} (g : G A) size :
  semProdSize (listOf g) size <-->
  [set l | length l <= size /\ l \subset (semProdSize g size)].
Proof.
rewrite /listOf semSizedSize semBindSize; setoid_rewrite semVectorOfSize.
rewrite semChooseSize // => l; split=> [[n [/andP [_ ?] [-> ?]]]| [? ?]] //.
by exists (length l).
Qed.

Lemma semListOfUnsized {A} (g : G A) (k : nat) `{@Unsized _ _ PG g} : 
  semProd (listOf g) <--> [set l | l \subset semProd g ]. 
Proof.
  rewrite /semProd.
  setoid_rewrite semListOfSize. 
  move => l; split.
  - move => [k' [_ [H1 H2]]]. exists k'. split; auto.
    reflexivity.
  - move => Hl. exists (length l). repeat split => //.
    move => a /Hl [s [_ Ha]]. by eapply unsized; eauto.
Qed.

#[global] Program Instance listOfMonotonic {A} (g : G A) 
        `{@SizeMonotonic _ _ PG g } : SizeMonotonic (listOf g).
Next Obligation.
  rewrite ! semListOfSize.
  move => l [/leP H1 H2]; split => //.

  destruct (@leP (length l)  s2); eauto.
  exfalso. eapply n. lia.
  move => a /H2 Ha. by eapply monotonic; eauto.
Qed.


Lemma In_nth_exists {A} (l: list A) x def :
  List.In x l -> exists n, nth def l n = x /\ (n < length l)%coq_nat.
Proof.
elim : l => [| a l IHl] //=.
move => [H | /IHl [n [H1 H2]]]; subst.
  exists 0; split => //; lia.
exists n.+1; split => //; lia.
Qed.

Lemma nthE T (def : T) s i : List.nth i s def = nth def s i.
Proof.
elim: s i => [|x s IHs i]; first by case.
by case: i.
Qed.

Lemma nth_imset T (def : T) l : nth def l @: [set n | n < length l] <--> l.
Proof.
case: l => [|x l] t; first by split=> //; case=> ?; rewrite ltn0; case.
split; first by case=> n [? <-]; rewrite -nthE; apply/List.nth_In/ltP.
by case/(In_nth_exists def) => n [? ?]; exists n; split=> //; apply/ltP.
Qed.

Lemma semOneofSize {A} (l : list (G A)) (def : G A) s : semProdSize (oneOf_ def l) s
  <--> if l is nil then semProdSize def s else \bigcup_(x in l) semProdSize x s.
Proof.
case: l => [|g l].
  rewrite semBindSize semChooseSize //.
  rewrite (eq_bigcupl [set 0]) ?bigcup_set1 // => a; split=> [/andP [? ?]|<-] //.
  by apply/antisym/andP.
rewrite semBindSize semChooseSize //.
set X := (fun a : nat => is_true (_ && _)).
by rewrite (reindex_bigcup (nth def (g :: l)) X) // /X subn1 nth_imset.
Qed.

Lemma semOneof {A} (l : list (G A)) (def : G A) :
  semProd (oneOf_ def l) <-->
  if l is nil then semProd def else \bigcup_(x in l) semProd x.
Proof.
by case: l => [|g l]; rewrite 1?bigcupC; apply: eq_bigcupr => sz;
  apply: semOneofSize.
Qed.

#[global] Program Instance oneofMonotonic {A} (x : G A) (l : list (G A))
        `{ @SizeMonotonic _ _ PG x} `(l \subset SizeMonotonic) 
: SizeMonotonic (oneOf_ x l). 
Next Obligation.
  rewrite !semOneofSize. elim : l H0 => [_ | g gs IH /subconsset [H2 H3]] /=.
  - by apply monotonic.
  - specialize (IH H3). move => a [ga [[Hga | Hga] Hgen]]; subst.
    exists ga. split => //. left => //.
    eapply monotonic; eauto. exists ga.
    split. right => //.
    apply H3 in Hga. by apply (monotonic H1). 
Qed.

Lemma semElementsSize {A} (l: list A) (def : A) s :
  semProdSize (elems_ def l) s <--> if l is nil then [set def] else l.
Proof.
rewrite semBindSize.
setoid_rewrite semReturnSize.
rewrite semChooseSize //=.
setoid_rewrite nthE. (* SLOW *)
case: l => [|x l] /=.
  rewrite (eq_bigcupl [set 0]) ?bigcup_set1 // => n.
  by rewrite leqn0; split=> [/eqP|->].
rewrite -(@reindex_bigcup _ _ _ (nth def (x :: l)) _ (x :: l)) ?coverE //.
by rewrite subn1 /= nth_imset.
Qed.

Lemma semElements {A} (l: list A) (def : A) :
  (semProd (elems_ def l)) <--> if l is nil then [set def] else l.
Proof.
rewrite /semProd; setoid_rewrite semElementsSize; rewrite bigcup_const //.
by do 2! constructor.
Qed.

#[global] Program Instance elementsUnsized {A} {def : A} (l : list A) : 
  Unsized (elems_ def l).
Next Obligation.
  rewrite ! semElementsSize. by case: l.
Qed.

#[global] Instance bindOptMonotonic
         {A B} (g : G (option A)) (f : A -> G (option B))
         {_ : SizeMonotonic g} `{forall x, SizeMonotonic (f x)} :
  SizeMonotonic (bindOpt g f).
Proof.
  intros s1 s2 Hleq.
  intros x Hx. unfold bindOpt in *.
  eapply (@semBindSize G _ _) in Hx.
  eapply (@semBindSize G _ _).
  destruct Hx. destruct H1.

  eexists. split. now eapply H0; eauto.
  destruct x0; eauto.

  eapply H; eauto.

  eapply semReturnSize. eapply semReturnSize in H2.
  eassumption. 
Qed.

Lemma semReturnSizeOpt (A : Type) (x : A) (size : nat) :
  semProdSizeOpt (ret (Some x)) size <--> [set x].
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdSizeOpt, somes in *.
    eapply semReturnSize in Hin. inv Hin. reflexivity.

  - unfold semProdSizeOpt, somes in *.
    eapply semReturnSize. inv Hin. reflexivity.
Qed. 

Lemma semReturnSizeOpt_None (A : Type) (size : nat) :
  semProdSizeOpt (ret None) size <--> @set0 A.
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturnSize in Hin. inv Hin.
  - inv Hin.
Qed. 

Lemma semReturnOpt (A : Type) (x : A) :
  semProdOpt (ret (Some x)) <--> [set x].
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturn in Hin. inv Hin. reflexivity.
    
  - unfold semProdOpt, somes in *.
    eapply semReturn. inv Hin. reflexivity.
Qed. 


Lemma semReturnOpt_None (A : Type) :
  semProdOpt (ret None) <--> @set0 A.
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturn in Hin. inv Hin.
  - inv Hin.
Qed. 

Lemma semOptBind A B (g : G A) (f : A -> G (option B)) :
  SizeMonotonic g ->
  (forall a : A, SizeMonotonicOpt (f a)) ->
  semProdOpt (bind g f) <-->
  \bigcup_(a in semProd g) semProdOpt (f a).
Proof.
  intros Hs Hsf.
  rewrite /semProdOpt /semProd. setoid_rewrite semBindSize.
  intro b. split.
  - intros [s [_ [a [H1 H2]]]].
    exists a. split; exists s; (split; first (compute; by []); first by[]).
  - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
      split; first (compute; by []).
      exists a. split.
      eapply Hs; last eassumption. lia.
      eapply Hsf; last eassumption. lia.
  Qed.

Lemma semOptBindSize A B (g : G A) (f : A -> G (option B)) size :
  semProdSizeOpt (bind g f) size <-->
  \bigcup_(a in semProdSize g size) semProdSizeOpt (f a) size.
Proof.
  unfold semProdSizeOpt.
  rewrite semBindSize; eauto.

  split.
  - intros Hin. inv Hin. inv H.
    eexists. split; eauto.

  - intros Hin. inv Hin. inv H.
    eexists. split; eauto.
Qed. 

Lemma semOptBindOpt A B (g : G (option A)) (f : A -> G (option B)) :
  SizeMonotonicOpt g ->
  (forall a : A, SizeMonotonicOpt (f a)) ->
  semProdOpt (bindOpt g f) <-->
  \bigcup_(a in semProdOpt g) semProdOpt (f a).
Proof.
  intros Hs Hsf.
  rewrite /semProdOpt /semProd /bindOpt. setoid_rewrite semBindSize.
  intro b. split.
  - intros [s [_ [a [H1 H2]]]].
    destruct a.
    2:{ eapply semReturnSize in H2. inv H2. }
    
    exists a. split; exists s; (split; first (compute; by []); first by[]).
  - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
    split; first (compute; by []).    
    exists (Some a). split.
    eapply Hs; last eassumption. lia.
    eapply Hsf; last eassumption. lia.
  Qed.


Lemma semOptBindOptSize A B (g : G (option A)) (f : A -> G (option B)) size :
  semProdSizeOpt (bindOpt g f) size <-->
  \bigcup_(a in semProdSizeOpt g size) semProdSizeOpt (f a) size.
Proof.
  unfold bindOpt. rewrite semOptBindSize; eauto.
  
  - split. 
    + intros Hin. inv Hin. inv H.
      destruct x. eexists. split; eauto.
      eapply semReturnSizeOpt_None in H1. inv H1.

    + intros Hin. inv Hin. inv H.
      eexists. split; eauto.
Qed.

#[global] Instance bindOptMonotonicOpt
       {A B} (g : G (option A)) (f : A -> G (option B))
       `{@SizeMonotonicOpt _ _ PG g} `{forall x, SizeMonotonicOpt (f x)} : 
  SizeMonotonicOpt (bindOpt g f).
Proof.
  intros s1 s2 Hs.  
  rewrite !semOptBindOptSize.
  move => b [a [Hg Hf]].
  exists a; split.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.      


Lemma semBindOptSizeOpt_subset_compat      
      (A B : Type) (g g' : G (option A)) (f f' : A -> G (option B)) s : 
  semProdSizeOpt g s \subset semProdSizeOpt g' s ->
  (forall (x : A),
      semProdSizeOpt (f x) s \subset semProdSizeOpt (f' x) s) ->
  semProdSizeOpt (bindOpt g f) s \subset semProdSizeOpt (bindOpt g' f') s.
Proof.
  intros Hyp1 Hyp2.
  rewrite !semOptBindOptSize.
  eapply incl_bigcup_compat; eauto.
Qed. 

Lemma semBindSizeOpt_subset_compat
      (A B : Type) (g g' : G A) (f f' : A -> G (option B)) s : 
  semProdSize g s \subset semProdSize g' s ->
  (forall (x : A),
      semProdSizeOpt (f x) s \subset semProdSizeOpt (f' x) s) ->
  semProdSizeOpt (bind g f) s \subset semProdSizeOpt (bind g' f') s.
Proof.
  intros Hyp1 Hyp2.
  rewrite !semOptBindSize.
  eapply incl_bigcup_compat; eauto.
Qed.


End ProducerHighProofs.
