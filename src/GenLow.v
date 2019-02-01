Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
Require Import ExtLib.Data.Monads.ListMonad.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     GenLowInterface RandomQC EnumerationQC RoseTrees Sets Tactics LazyList.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.


Module GenLow : GenLowInterface.Sig.

  (** * Type of generators *)

  (* begin GenType *)
  Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> LazyList A) -> GenType A.
  (* end GenType *)

  Definition G := GenType.

  (** * Primitive generator combinators *)
  
  (* begin run *)
  Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
  (* end run *)

  (* LEO: lnil could have a "reason for failure" included probably. *)
  Definition failGen {A : Type} : G A :=
    MkGen (fun _ _ => lnil).
  
  Definition returnGen {A : Type} (x : A) : G A :=
    MkGen (fun _ _ => ret x).

  Definition returnGenL {A : Type} (x : LazyList A) : G A :=
    MkGen (fun _ _ => x).

  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
    MkGen (fun n r => fmap f (run g n r)).

  (* Go through the lazy list la and run (k a) for each element in la with a different seed. *)
  Fixpoint bindGenAux {A B} (la : LazyList A) (k : A -> G B) n (rs : RandomSeed) : LazyList B :=
    match la with
    | lnil => lnil
    | lsing a => run (k a) n rs
    | lcons a la' =>
      let (r1,r2) := randomSplit rs in
      lazy_append (run (k a) n r1) (bindGenAux (la' tt) k n r2)
    end.
  
  Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             bindGenAux (run g n r1) k n r2
          ).
  
  Definition apGen {A B} (gf : G (A -> B)) (gg : G A) : G B :=
    bindGen gf (fun f => fmap f gg).

  Instance Functor_G : Functor G := {
    fmap A B := fmap;
  }.

  Instance Applicative_G : Applicative G := {
    pure A := returnGen;
    ap A B := apGen;
  }.

  Instance Monad_G : Monad G := {
    ret A := returnGen;
    bind A B := bindGen;
  }.
  
  Definition sized {A : Type} (f : nat -> G A) : G A :=
    MkGen (fun n r => run (f n) n r).
  
  Definition resize {A : Type} (n : nat) (g : G A) : G A :=
    match g with
      | MkGen m => MkGen (fun _ => m n)
    end.

  Fixpoint lazy_rose_flatten {A : Type} (r : Rose (LazyList A)) : LazyList (Rose A) :=
    match r with
    | MkRose las ts =>
      a <- las;;
      lcons (MkRose a (lazy (LazyList_to_list (join_list_lazy_list (map lazy_rose_flatten (force ts)))))) (fun _ => (lnil))
    end.

  Fixpoint promote {A : Type} (m : Rose (G A)) : G (Rose A)
    := MkGen (fun n r => lazy_rose_flatten (fmapRose (fun ga => run ga n r) m)).
  
  (* ZP: Split suchThatMaybe into two different functions
     to make a proof easier *)
  Definition suchThatMaybeAux {A : Type} (g : G A) (p : A -> bool) :=
    fix aux (k : nat) (n : nat) : G A :=
    match n with
      | O => failGen
      | S n' =>
        x <- resize (2 * k + n) g ;;
        if p x then ret x else aux (S k) n'
    end.

  Definition suchThatMaybe {A : Type} (g : G A) (p : A -> bool) : G A :=
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

  Definition choose {A : Type} `{ChoosableFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ r => ret (fst (randomR range r))).

  (* TODO @Calvin: Do these use laziness? *)
  Definition enumR {A : Type} `{EnumFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ _ => enumFromTo (fst range) (snd range)).

  Definition enum {A : Type} `{Serial A} : G A :=
    MkGen (fun n r => series n r).

  Definition enum' {A : Type} `{Serial A} (n : nat) : G A :=
    MkGen (fun _ r => series n r).

  (* TODO: Rethink this.
  Fixpoint sumG {A : Type} (lga : LazyList (G A)) : G A :=
    MkGen (fun n r => bind_helper lga n r).
   *)

  (* TODO: This looks stupid. *)
  Definition sample (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        joint_list_lazy_list_list (List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l)
    end.
  
  (* LL : Things that need to be in GenLow because of MkGen *)
  
  Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.

  Definition reallyUnsafeDelay {A : Type} : G (G A -> LazyList A) :=
    MkGen (fun r n => lsing (fun g => match g with MkGen f => f r n end)).

  (* Leo: Even more unsafe with fail option... 
  Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    eval <- reallyUnsafeDelay ;;
    ret (fun r => match (eval (m r))).
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).
  *)

  (* End Things *)

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated above) *)
  (* begin semGen *)

  Definition semGenSize {A : Type} (g : G A) (s : nat) : set A :=
    possibly_generated (run g s).
  
  Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.
  (* end semGen *)

  (* More things *)
  Program Definition bindGen' {A B : Type} (g : G A) (k : forall (a : A), (a \in semGen g) -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             _).
  Next Obligation.
    remember (run g n r1) as a's.
    destruct a's.
    - exact (lnil).
    - refine (run (k a _) n r2).
      unfold semGen, semGenSize, bigcup, codom, bigcup, possibly_generated.
      exists n. split => //=.
      exists r1. inversion Heqa's. constructor.
    - refine (run (k a _) n r2).
      unfold semGen, semGenSize, bigcup, codom, bigcup, possibly_generated.
      exists n. split => //=.
      exists r1. inversion Heqa's. constructor.
      auto.
  Qed.
  

  (** * Semantic properties of generators *)

  Class Unsized {A} (g : G A) :=
    {
      unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2
    }.
  
  Class SizedMonotonic {A} (g : nat -> G A) :=
    {
      (* TODO remove prime when GenSizedSizeMotonic is modified *)
      sizeMonotonic :
        forall s s1 s2,
          s1 <= s2 ->
          semGenSize (g s1) s \subset semGenSize (g s2) s
    }.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    {
      monotonic :
        forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2
    }.

  (* Unsizedness trivially implies size-monotonicity *)
  Lemma unsizedMonotonic {A} (g : G A) : Unsized g -> SizeMonotonic g. 
  Proof.
    constructor. intros s1 s2 Hleq.
    rewrite /unsized /monotonic => a H12.
      by destruct (unsized s1 s2 a) as [H1 H2]; eauto.
  Qed.
  
  Lemma unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.
  Proof.
    move => A f H s a. split.
    move => H'. exists s. split; auto => //.
    move => [s' [_ H']]. eapply unsized; eauto.
  Qed.

  (** * Semantics of combinators *)

  (* Fail yields the empty set *)
  Lemma semFailSize {A} (s : nat) : semGenSize failGen s <--> @set0 A.
  Proof.
    rewrite /semGenSize /possibly_generated /=; split.
    - move => [? Contra]; inversion Contra.
    - move => Contra; inversion Contra.
  Qed.
  
  Lemma semFail {A} : semGen failGen <--> @set0 A.
  Proof.
    rewrite /semGen /semGenSize /= /possibly_generated; split.
    - move => [? [? [? Contra]]].
      inversion Contra.
    - move => Contra.
      inversion Contra.
  Qed.

  (* begin semReturn *)
  Lemma semReturn {A} (x : A) : semGen (returnGen x) <--> [set x].
  (* end semReturn *)
  Proof.
    rewrite /semGen /semGenSize /= bigcup_const ?codom_const //.
    split.
    - intros H. inversion H. inversion H0. subst. constructor. (* inversion H1.*)
    - intros H. inversion H. unfold possibly_generated. destruct randomSeed_inhabited as [r]. exists r.
      constructor. (* auto.*)
    - do 2! constructor.
  Qed.
  
  (* begin semReturnSize *)
  Lemma semReturnSize A (x : A) (s : nat) :
  semGenSize (returnGen x) s <--> [set x].
  (* end semReturnSize *)
  Proof.
    unfold semGenSize, possibly_generated.
    split.
    - intros [r H]. inversion H.
      + subst; constructor.
    - intros H. inversion H. destruct randomSeed_inhabited as [r]. exists r.
      simpl. auto.
  Qed.
  
  Program Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Next Obligation.
      by rewrite ! semReturnSize; split; auto.
  Qed.
  
  Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Proof.
    firstorder.
  Qed.

  Lemma bind_in_f :
    forall A B (b : B) (g : G A) (f : A -> G B) s r,
      In_ll b (run (bindGen g f) s r) ->
      exists a r', In_ll b (run (f a) s r').
  Proof.
    intros A B b g f s r H.
    simpl in H.
    destruct (randomSplit r) as [r1 r2].
    remember (run g s r1) as runr1 eqn:Hrunr1. clear Hrunr1 r.
    revert r1 r2 H. revert f s g.
    induction runr1; intros f s g r1 r2 HIn; simpl in *.
    - inversion HIn.
    - exists a. exists r2. assumption.
    - unfold bindGenAux in *. simpl in *.
      destruct (randomSplit r2) as [r3 r4]. simpl in *.
      apply lazy_in_app_or in HIn. destruct HIn.
      + exists a. exists r3. auto.
      + eapply H; eauto. 
  Qed.

  Lemma in_bind_aux :
    forall {A B : Type} (la : LazyList A) f s r (b : B),
      In_ll b (bindGenAux la f s r) ->
      exists (a : A),
        (In_ll a la) /\
        (exists r' : RandomSeed, In_ll b (run (f a) s r')).
  Proof.
    move => A B la; induction la => f s r b HIn; simpl in *.
    - inversion HIn.
    - exists a; split; [ | exists r]; auto.
    - destruct (randomSplit r) as [r1 r2].
      apply lazy_in_app_or in HIn; destruct HIn.
      + exists a; split; [ | exists r1]; auto.
      + apply H in H0.
        destruct H0 as [a' [Ha' [r' Hb]]].
        exists a'; split; auto.
        exists r'; auto.
  Qed.
        
  Lemma in_bind:
    forall {A B : Type} f (g : G A) s r (b : B),
      In_ll b (run (bindGen g f) s r) ->
      exists (a : A),
        (exists r1 : RandomSeed, In_ll a (run g s r1)) /\
        (exists r2 : RandomSeed, In_ll b (run (f a) s r2)).
  Proof.
    move => A B f g s r b HIn.
    simpl in *.
    destruct (randomSplit r) as [r1 r2].
    apply in_bind_aux in HIn.
    destruct HIn as [a [HIna [r' HInB]]].
    exists a; split.
    - exists r1; auto.
    - exists r'; auto.
  Qed.

  Lemma bind_aux_in :
    forall {A B} (la : LazyList A) f s r (a : A) (b : B),
      In_ll a la -> In_ll b (run (f a) s r) ->
      exists r, In_ll b (bindGenAux la f s r).
  Proof.
    move => A B la; induction la => f s r x b HInX HInB; simpl in *; subst.
    - inversion HInX.
    - exists r; assumption.
    - destruct HInX as [? | HIn]; subst; simpl in *; auto.
      + (* Second component of rsa could be whatever *)
        destruct (randomSplitAssumption r r) as [r' Hr'].
        exists r'. rewrite Hr'.
        apply lazy_append_in_l.
        assumption.
      + eapply H in HInB; eauto.
        destruct HInB as [r' HInB].
        (* First component of rsa could be whatever *)
        destruct (randomSplitAssumption r r') as [R HR].
        exists R.
        rewrite HR.
        apply lazy_append_in_r.
        assumption.
  Qed.
  
  (* begin semBindSize *)
  Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
               \bigcup_(a in semGenSize g s) semGenSize (f a) s.
  (* end semBindSize *)
  Proof.
    unfold semGenSize.
    unfold bigcup.
    unfold possibly_generated.
    split; rename a into b.
    - intros [r H].
      destruct (randomSplit r) as [r1 r2] eqn:Hrs.
      eapply in_bind; eauto.
    - move => [a [[r1 HIn1] [r2 HIn2]]].
      simpl in *.
      eapply bind_aux_in in HIn2; eauto.
      destruct HIn2 as [r' HIn].
      destruct (randomSplitAssumption r1 r') as [r HSplit].      
      exists r; rewrite HSplit.
      assumption.
  Qed.      

  Lemma semBindSize_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G B) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, semGenSize (f x) s \subset semGenSize (f' x) s) ->
    (forall s, semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply incl_bigcupl. eapply H1.
    eapply incl_bigcupr. intros; eapply H2.
  Qed.
  
  Lemma monad_leftid A B (a : A) (f : A -> G B) :
    semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Proof.
      by apply: eq_bigcupr => size; rewrite semBindSize semReturnSize bigcup_set1.
  Qed.
  
  Lemma monad_rightid A (g : G A) : semGen (bindGen g returnGen) <--> semGen g.
  Proof.
    apply: eq_bigcupr => size; rewrite semBindSize.
    unfold bigcup.
    split.
    - intros [a' [H1 H2]].
      unfold semGenSize in *. simpl in H2. unfold possibly_generated in H2.
      destruct H2. inversion H.
      + subst. auto.
(*      + inversion H0. *)
    - intros H.
      exists a. split.
      + auto.
      + unfold semGenSize. simpl. unfold possibly_generated.
        destruct randomSeed_inhabited as [r]. exists r.
        simpl. auto.
  Qed.
  
  Lemma monad_assoc A B C (ga : G A) (fb : A -> G B) (fc : B -> G C) :
    semGen (bindGen (bindGen ga fb) fc) <--> 
    semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  Proof.
    apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
    by apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
  Qed.

  Program Instance bindUnsized
          {A B} (g : G A) (f : A -> G B) `{Unsized _ g} `{forall x, Unsized (f x)} : 
    Unsized (bindGen g f).
  Next Obligation.
    rewrite !semBindSize !unsized_alt_def. move => b. 
    split; move => [a [H1 H2]]; exists a; split => //; by eapply unsized; eauto.
  Qed.
  
  Program Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).
  Next Obligation.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //; eapply monotonic; eauto.
  Qed.

  Program Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonic (f x)} :
    SizeMonotonic (bindGen g f).
  Next Obligation.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //.
    now eapply monotonic; eauto.
    eapply H0.
    eexists. split; eauto. now constructor.
    eassumption.
    eassumption.
  Qed.

  (* begin semBindUnsized1 *)
  Lemma semBindUnsized1 {A B} (g : G A) (f : A -> G B) `{H : Unsized _ g}:
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindUnsized1 *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    setoid_rewrite (@unsized_alt_def A g H). move => b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split; by [].
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. 
      exists s2. split; first by [].
      exists a. split; by [].
  Qed.
  
  Lemma semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B),
      (forall a, Unsized (f a)) ->
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  Proof.
    move=> A B g f H.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split => //. 
    - intros [a [[s1 [_ H1]] [s2 [_  H2]]]].
      exists s1. split; first by []. exists a. 
      split; first by []; apply unsized_alt_def; eauto.
        by eapply unsized_alt_def; eauto.
  Qed.

  (* begin semBindSizeMonotonic *)
  Lemma semBindSizeMonotonic {A B} (g : G A) (f : A -> G B)
        `{Hg : SizeMonotonic _ g} `{Hf : forall a, SizeMonotonic (f a)} :
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindSizeMonotonic *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; (split; first (compute; by []); first by[]).
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
      split; first (compute; by []).
      exists a. split.
      eapply Hg; last eassumption. by apply/leP; apply Max.le_max_l.
      eapply Hf; last eassumption. by apply/leP; apply Max.le_max_r.
  Qed.

  Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
    semGenSize (fmap f g) size <--> f @: semGenSize g size.
  Proof.
    rewrite /fmap /semGenSize /possibly_generated /= /imset => b; split.
    - move => [r HIn].
      apply lazy_in_map_iff in HIn.
      destruct HIn as [a [HFa HIn]].
      exists a; split; eauto.
    - move => [a [[r Hr] HIn]].
      exists r.
      apply lazy_in_map_iff.
      eexists; eauto.
  Qed.
  
  Lemma semFmap A B (f : A -> B) (g : G A) :
    semGen (fmap f g) <--> f @: semGen g.
  Proof.
      by rewrite imset_bigcup /semGen (eq_bigcupr _ (semFmapSize _ _)).
  Qed.
  
  Program Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} : 
    Unsized (fmap f g).
  Next Obligation.
    rewrite !semFmapSize. move => b.
      by split; move => [a [H1 <-]]; eexists; split; eauto => //; eapply unsized; eauto.
  Qed.
  
  Program Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).
  Next Obligation.
    rewrite !semFmapSize. move => b.
    move => [a [H1 <-]]; eexists; split; eauto => //; eapply monotonic; eauto.
  Qed.
  
  Lemma semChooseSize A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
  Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.
  
  Program Instance chooseUnsized {A} `{ChoosableFromInterval A} (a1 a2 : A) : 
    Unsized (choose (a1, a2)).
  Next Obligation. by []. Qed.
  
  Lemma semChoose A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
  Proof. 
    move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
    move => m /=. rewrite (randomRCorrect m a1 a2) //.
  Qed.

  Lemma semSized A (f : nat -> G A) :
    semGen (sized f) <--> \bigcup_n semGenSize (f n) n.
  Proof. by []. Qed.

  Lemma semSizedSize A(f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
  Proof. by []. Qed.

  Lemma semSized_alt A (f : nat -> G A) (H : forall n, SizeMonotonic (f n))
        (H' : forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) :
    semGen (sized f) <--> \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized.
    move => x; split.
    - move => [n [HT Hs]].
      eexists. split; eauto. eexists; eauto.
    - move => [n [HT [m [_ Hs]]]].
      eapply semSized. eexists (m + n).
      split. constructor. 
      eapply (H' n). ssromega.
      eapply (H n); try eassumption. ssromega.
  Qed.

  Instance sizedSizeMonotonic
           A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).
  Proof.
    constructor. move => s1 s2 Hleq a /semSizedSize H1.
    eapply semSizedSize.
    eapply H. eassumption.
    eapply H0; eassumption.
  Qed.

  Lemma semResize A n (g : G A) : semGen (resize n g) <--> semGenSize g n .
  Proof.
      by case: g => g; rewrite /semGen /semGenSize /= bigcup_const.
  Qed.

  Lemma semSizeResize A (s n : nat) (g : G A) :
    semGenSize (resize n g) s <--> semGenSize g n.
  Proof.
      by case: g => g; rewrite /semGenSize.
  Qed.
  
  Program Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).
  Next Obligation.
    rewrite /Unsized /resize /semGenSize.
    destruct g; split; auto.
  Qed.
  
  Lemma SuchThatMaybeAuxMonotonic {A} :
    forall (g : G A) p k n,
      SizeMonotonic g -> 
      SizeMonotonic (suchThatMaybeAux g p k n).
  Proof.
    intros g p k n Hmon. elim : n k => [| n IHn ] k.
    - constructor. intros s1 s2 Hleq.
      simpl. rewrite !semFailSize. now apply subset_refl.
    - constructor. intros s1 s2 Hleq.
      simpl.
      rewrite !semBindSize. eapply incl_bigcup_compat.
      + rewrite !semSizeResize. eapply Hmon.
        by ssromega.
      + intros x.
        destruct (p x); eauto.
        now apply subset_refl.
        eapply IHn. 
        eassumption.
  Qed.

  (* LEO: No longer true! 
  Lemma semGenSizeInhabited {A} (g : G A) s :
    exists x, semGenSize g s x.
  Proof.
    destruct randomSeed_inhabited as [r].
    eexists (run g s r ). unfold semGenSize, codom.
    exists r. reflexivity.
  Qed.
   *)

  (* LEO: Is this needed?
  Lemma SuchThatMaybeAuxParamMonotonicOpt {A} :
    forall (g : G A) p n1 n2 k s,
      SizeMonotonic g ->
      n1 <= n2 ->
      semGenSize (suchThatMaybeAux g p k n1) s \subset
      semGenSize (suchThatMaybeAux g p k n2) s.
  Proof.
    intros g p. elim  => [| n IHn ] n2 k s Hmon Heq.
    - intros x [r HIn]; inv HIn.
    - intros x [r HIn]; simpl in *.
      destruct (randomSplit r) as [r1 r2] eqn:Split.
      apply in_bind_aux in HIn.
      destruct HIn as [a [HIn [r' HIn']]].
      apply IHn; eauto.
      destruct (p a) eqn:PA; simpl in *; subst; eauto.
      + rewrite /suchThatMaybeAux; simpl.
      esplit; eauto.
      simpl in H2. 
      eapply semBindSize in H2. destruct H2 as [ a[Hg Hf]].
      eapply semSizeResize with (g := g) in Hg. 
      destruct n2; [ now ssromega |].
      + simpl. eapply semBindSize. eexists.
        split. eapply semSizeResize with (g := g).
        eapply Hmon; [| eassumption ]. by ssromega.
        destruct (p a).
        * eassumption.
        * eapply IHn; eauto.
          split; eauto.
  Qed.
  
  Lemma suchThatMaybeAux_subset_compat :
    forall {A : Type} (p : A -> bool) (g1 g2 : G A) n k,
      (forall s, (semGenSize g1 s) \subset (semGenSize g2 s)) ->
      (forall s, (semGenSize (suchThatMaybeAux g1 p k n) s) \subset
            (semGenSize (suchThatMaybeAux g2 p k n) s)).
  Proof.
    intros A p g1 g2 n k H2 s.
    elim : n k => [| n IHn ] k.
    - now apply subset_refl.
    - simpl. rewrite !semBindSize !semSizeResize.
      eapply incl_bigcup_compat.
      + eapply H2.
      + intros x. destruct (p x); [ now apply subset_refl |].
        eauto.
  Qed.
  
  Lemma semGenSuchThatMaybeAux_sound {A} :
    forall g p k n (a : A) size seed,
      run (suchThatMaybeAux g p k n) size seed = Some a ->
      a \in semGen g :&: p.
  Proof.
    case=> g p k n; elim: n k =>  [//=| n IHn] k a size seed /=.
    case: (randomSplit seed) => r1 r2; case: ifP=> [/= ? [<-]|_]; last exact: IHn.
      by split=> //; exists (2 * k + n.+1); split=> //; exists r1.
  Qed.

  (* Not an exact spec !!! *)
  Lemma semSuchThatMaybe_sound' A (g : G A) (f : A -> bool) :
    semGen (suchThatMaybe g f) \subset None |: some @: (semGen g :&: f).
  Proof.
    case=> [a [size [_ [x run_x]]] | ]; last by left.
    by right; exists a; split=> //; apply: (semGenSuchThatMaybeAux_sound run_x).
  Qed.

  Lemma semGenSuchThatMaybeOptAux_sound {A} :
    forall g p k n (a : A) size seed,
      run (suchThatMaybeOptAux g p k n) size seed = Some a ->
      (Some a) \in semGen g :&: (Some @: p).
  Proof.
    case=> g p k n; elim: n k =>  [//=| n IHn] k a size seed /=.
                                             case: (randomSplit seed) => r1 r2 Hrun.
    destruct (g (2 * k + n.+1) r1) as [a' |] eqn:Heq.
    - destruct (p a') eqn:Hpa.
      + inv Hrun.
        split. eexists (2 * k + n.+1). split. constructor.
        eexists. eassumption. eexists. split. eassumption.
        reflexivity.
      + eapply IHn. eassumption.
    - eapply IHn. eassumption. 
  Qed.
   *)

  (* LEO: Why is this here? *)
  Lemma lt_leq_trans n m u : n < m -> m <= u -> n < u.
  Proof.
    intros H1 H2. ssromega.
  Qed.
  
  (*
  Lemma semGenSizeSuchThatMaybeAux_complete {A} :
    forall g (p : A -> bool) k s n,
      n > 0 ->
      n >= s ->
      SizeMonotonic g ->
      (semGenSize g s :&: p) \subset semGenSize (suchThatMaybeAux g p k n) s.
  Proof.
    intros g p k s.
    intros n Hleq1 Hleq2 Hmon x [a [[Hg Hp] Hs]]. destruct x as [x | ]; try discriminate.
    case : n k Hleq1 Hleq2 => [//= | n ] k Hleq1 Hleq2.
    inv Hs. unfold suchThatMaybeAux. eapply semBindSize.
    eexists. split. eapply semSizeResize.
    eapply Hmon; [| eassumption ]. by ssromega.
    rewrite Hp.
    apply semReturnSize. reflexivity.
  Qed.

  Lemma semSuchThatMaybe_complete' A (g : G A) (f : A -> bool) :
    SizeMonotonic g -> 
    Some @: (semGen g :&: f) \subset semGen (suchThatMaybe g f).
  Proof.
    intros Hmon.
    intros x [y [[[s Hg] Hf] Hin]]. exists s.
    split; [ now constructor | eapply semGenSizeSuchThatMaybeAux_complete; try eassumption ].
    eapply lt_leq_trans with (m := 1). by ssromega.
    apply/leP. by eapply Max.le_max_l. 
    apply/leP. by eapply Max.le_max_r. 
    inv Hin. eexists; split; eauto. inv Hg. split; eauto.
  Qed.

  Lemma semSuchThatMaybe_complete:
    forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
      SizeMonotonic g ->
      s \subset semGen g ->
      Some @: (s :&: (fun x : A => f x)) \subset semGen (suchThatMaybe g f).
  Proof.
    intros A g f s Hmon Hsub.
    eapply subset_trans.
    eapply imset_incl. eapply setI_subset_compat.
    eassumption. now apply subset_refl.
    eapply subset_trans; [| eapply semSuchThatMaybe_complete' ].
    now apply subset_refl. eassumption.
  Qed.
  *)

  (*
  Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      apLazyList (run (reallyUnsafePromote (fun a => variant (f a) g)) size r) a = 
      run g size (varySeed (f a) r1).
  Proof. 
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
  Qed.
  *)
  (*
  Lemma semPromote A (m : Rose (G A)) :
    semGen (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
  Proof. by rewrite /codom2 curry_codom2l. Qed.

  Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semGenSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
  Proof. by []. Qed.

  Lemma runFmap (A B : Type) (f : A -> B) (g : G A) seed size :
    run (fmap f g) seed size = f (run g seed size).
  Proof. by []. Qed.
  
  Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  Proof. by []. Qed.
  
  Lemma semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).
  Proof.
    intros. rewrite /semGen. setoid_rewrite semFmapSize.
    setoid_rewrite semBindSize.
    apply eq_bigcupr => s. setoid_rewrite semFmapSize.
    rewrite imset_bigcup. reflexivity.
  Qed.
  
  Instance suchThatMaybeMonotonicOpt
           {A : Type} (g : G A) (f : A -> bool) `{SizeMonotonic _ g} : 
    SizeMonotonicOpt (suchThatMaybe g f).
  Proof.
    unfold suchThatMaybe. eapply sizedSizeMonotonicOpt.
    intros n. now apply SuchThatMaybeAuxMonotonic; eauto.
    constructor. intros s s1 s2 Hleq x H1.
    eapply SuchThatMaybeAuxParamMonotonicOpt; try eassumption.
    apply/leP. eapply Nat.max_le_compat_l. ssromega.
  Qed.

  Lemma semSuchThatMaybe_sound:
    forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
      semGen g \subset s ->
      semGen (suchThatMaybe g f) \subset ((Some @: (s :&: (fun x : A => f x))) :|: [set None]).
  Proof.
    intros. eapply subset_trans.
    eapply semSuchThatMaybe_sound'.
    rewrite setU_comm. eapply setU_set_subset_compat.
    eapply imset_incl.
    eapply setI_subset_compat. eassumption.
    now apply subset_refl.
    now apply subset_refl.
  Qed.

  Lemma suchThatMaybe_subset_compat :
    forall {A : Type} (p : A -> bool) (g1 g2 : G A),
      (forall s, (semGenSize g1 s) \subset (semGenSize g2 s)) ->
      (forall s, isSome :&: (semGenSize (suchThatMaybe g1 p) s) \subset
                   isSome :&: (semGenSize (suchThatMaybe g2 p) s)).
  Proof.
    intros A p g1 g2 H1 s.
    eapply setI_subset_compat.
    now apply subset_refl.
    unfold suchThatMaybe.
    rewrite !semSizedSize.
    eapply suchThatMaybeAux_subset_compat. eassumption.
  Qed.

  Lemma semSuchThatMaybeOpt_sound:
    forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
      semGen g \subset ((Some @: s) :|: [set None]) ->
      semGen (suchThatMaybeOpt g f) \subset (Some @: (s :&: (fun x : A => f x)) :|: [set None]).
  Proof.
    intros A g f s.
    intros Hsub1.
    eapply subset_trans. eapply semSuchThatMaybeOpt_sound'.
    eapply subset_trans. eapply setU_set_subset_compat.
    now apply subset_refl.
    eapply setI_subset_compat. eassumption.
    now apply subset_refl.
    rewrite setI_setU_distr setU_comm.
    eapply setU_l_subset; [| now firstorder ].
    eapply setU_l_subset; [| now firstorder ].
    intros x [[a [H1 Heq1]] [a' [H2 Heq2]]].
    inv Heq1; inv Heq2. left.
    eexists. repeat split; eauto.
  Qed.
  
  Instance suchThatMaybeOptMonotonicOpt
           {A : Type} (g : G (option A)) (f : A -> bool) `{SizeMonotonicOpt _ g} : 
    SizeMonotonicOpt (suchThatMaybeOpt g f).
  Proof.
    unfold suchThatMaybeOpt. eapply sizedSizeMonotonicOpt.
    intros n. eapply unsizedMonotonic.
    eapply SuchThatMaybeAuxOptUnsized.
    constructor. intros s s1 s2 Hleq x H1.
    eapply SuchThatMaybeAuxOptParamMonotonicOpt; try eassumption.
    apply/leP. eapply Nat.max_le_compat_l. ssromega.
  Qed.

  Lemma bigcup_setI {T U} (s1 : set T) (s2 : set U) F :
    \bigcup_(x in s1) (s2 :&: F x) <--> s2 :&: \bigcup_(x in s1) (F x).
  Proof.
    firstorder.
  Qed.

  Lemma suchThatMaybeOptAux_subset_compat :
    forall {A : Type} (p : A -> bool) (g1 g2 : G (option A)) n k,
      (forall s, isSome :&: (semGenSize g1 s) \subset isSome :&: (semGenSize g2 s)) ->
      (forall s, isSome :&: (semGenSize (suchThatMaybeOptAux g1 p k n) s) \subset
            isSome :&: (semGenSize (suchThatMaybeOptAux g2 p k n) s)).
  Proof. 
    intros A p g1 g2 n k H2 s.
    elim : n k => [| n IHn ] k.
    - now apply subset_refl.
    - simpl. rewrite !semBindSize !semSizeResize.
  Admitted.

  Lemma suchThatMaybeOpt_subset_compat {A : Type} (p : A -> bool) (g1 g2 : G (option A)) :
    (forall s, isSome :&: (semGenSize g1 s) \subset isSome :&: (semGenSize g2 s)) ->
    (forall s, isSome :&: (semGenSize (suchThatMaybeOpt g1 p) s) \subset
          isSome :&: (semGenSize (suchThatMaybeOpt g2 p) s)).
  Proof.
    intros H1.
    unfold suchThatMaybeOpt. intros s. rewrite !semSizedSize.
    eapply suchThatMaybeOptAux_subset_compat. eassumption.
  Qed.

  Lemma semSuchThatMaybeOpt_complete:
    forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
      SizeMonotonicOpt g ->
      (Some @: s) \subset semGen g ->
      (Some @: (s :&: (fun x : A => f x))) \subset semGen (suchThatMaybeOpt g f).
  Proof.
    intros A g f s Hmon.
    intros Hsub1.
    eapply subset_trans; [| eapply semSuchThatMaybeOpt_complete'].
    intros x [a [[Hs Hf] Hin]]; inv Hin.
    split. eapply Hsub1. now eexists; split; eauto.
    now eexists; split; eauto. eassumption. 
  Qed.

   *)

  Definition thunkGen {A} (f : unit -> G A) : G A :=
    MkGen (fun n r => run (f tt) n r).

  Lemma semThunkGenSize {A} (f : unit -> G A) s :
    semGenSize (thunkGen f) s <--> semGenSize (f tt) s.
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Lemma semThunkGen {A} (f : unit -> G A) :
    semGen (thunkGen f) <--> semGen (f tt).
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Program Instance thunkGenUnsized {A} (f : unit -> G A)
          `{Unsized _ (f tt)} : Unsized (thunkGen f).
  Next Obligation.
    do 2 rewrite semThunkGenSize.
    apply unsized.
  Qed.

  Program Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{SizeMonotonic _ (f tt)} : SizeMonotonic (thunkGen f).
  Next Obligation.
    do 2 rewrite semThunkGenSize.
    by apply monotonic.
  Qed.

  (*
  Program Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{SizeMonotonicOpt _ (f tt)} : SizeMonotonicOpt (thunkGen f).
  Next Obligation.
    do 2 rewrite semThunkGenSize.
    by apply monotonic_opt.
  Qed.

  Program Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{SizeAntiMonotonicNone _ (f tt)} : SizeAntiMonotonicNone (thunkGen f).
  Next Obligation.
    do 2 rewrite semThunkGenSize.
    by apply monotonic_none.
  Qed.
   *)
End GenLow.
