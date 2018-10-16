Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     GenLowInterface RandomQC RoseTrees Sets Tactics LazyList.

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
  
  Definition returnGen {A : Type} (x : A) : G A :=
    MkGen (fun _ _ => ret x).

  (* Split and use a different random seed on each list *)
  Fixpoint bind_helper {B : Type} (lgb : LazyList (G B)) (n : nat) (rs : RandomSeed) : LazyList B :=
    match lgb with
    | lnil => lnil _
    | lcons gb ts =>
      let (r1, r2) := randomSplit rs in
      lazy_append (run gb n r1) (bind_helper (force ts) n r2)
    end.

  Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             let l := run g n r1 in
             let lgb := fmap k l in
           bind_helper lgb n r2).


  Definition bindGenOpt {A B} (g : G (option A)) (f : A -> G (option B)) : G (option B) :=
    bindGen g (fun ma => 
                 match ma with
                   | None => returnGen None
                   | Some a => f a
                 end).
  
  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
    MkGen (fun n r => fmap f (run g n r)).

  Definition apGen {A B} (gf : G (A -> B)) (gg : G A) : G B :=
    bindGen gf (fun f => fmap f gg).
  
  Definition sized {A : Type} (f : nat -> G A) : G A :=
    MkGen (fun n r => run (f n) n r).
  
  Definition resize {A : Type} (n : nat) (g : G A) : G A :=
    match g with
      | MkGen m => MkGen (fun _ => m n)
    end.

  (*
  Fixpoint promote {A : Type} (n : nat) (m : Rose (G A)) : G (Rose A) :=
    match m with
    | MkRose h ts => fmap (fun h => MkRose h (smoosh n (lazy (map (promote (n-1)) (force ts))))) h
    end.
   *)

  (* To promote a Rose LazyList to a LazyList Rose it makes sense to preserve shrinking order... *)
  (*
  Fixpoint lazy_list_promote `{A : Type} (rl : Rose (LazyList A)) : LazyList (Rose A) :=
    match rl with
    | MkRose h ts =>
      a <- h;;
      let bleh := (map (fun rose => fmapRose lazy_list_promote rose) (force ts)) in
      ret (MkRose a _)
    end.
    
      list_to_LazyList (force ts)
      mapLazyList (fun h => MkRose h _ (*(lazy (lazy_list_promote (force ts))) *)) h
    end.
   *)

  (* 
     Each level of the Rose tree is all of the enumerated tests.

     Makes sense to shrink from left to right (smallest to largest
     enumerated test)...

     - Not clear which children are shrunk versions of which tests...
     - Would we try to shrink enumerated parts as well? Should we bother?
       + Worst case this is just a waste of time... Hmmm.

     I think we need to change the representation of enumerated tests
     to prevent this RoseTree issue.

     Instead of generating a lazy list of values we should take an
     argument for which enumerated test we should spit out (the index
     into the lazy list).

     - Do we always have a test for number x?
       + No, what if we're not enumerating at all!
       + Want to just specify depth and iterate until we run out...
       + Can we do this with current monad, and change how tests are run?
         * Generator will recursively spit out more tests on shrinking.

     If I enumerate and have random tests, e.g., enumerated lists with
     random elements... Should I...

     - One random choice per enumeration?
       + Not very good coverage, no sense for how many tests to run.
     - 10000x per enumeration...
       + I think this makes the most sense. Good coverage of random
       portions.
       + Do I have to run all of the tests, even if there is no randomness...?
     - 10000x across all enumerations?
       + Pick an enumeration at random, and then generate random test...
       + Wouldn't actually hit all enumerations, so this is pointless.
       + Could do at least one of each and then pick randomly, but... Eh.

      What I actually want is a list of generators. So, not this:

      G1 : (size : nat) -> RandomSeed -> (depth : nat) -> LazyList A

      But this:

      G2 : (depth nat) -> LazyList ((size : nat) -> RandomSeed -> A)

      The first may actually be equivalent to this. We call G1 getting
      the list of enumerated values that have random elements. Then we
      check each of these for failure in order, and run again if need
      be.

      The second we generate a list of generator functions that can be
      used to randomly generate values with the enumerations
      elaborated out already...  This is actually more useful, because
      then we can test in order of enumeration more thoroughly.
   *)

  Fixpoint join_list_lazy_list {A : Type} (l : list (LazyList A)) : LazyList A :=
    match l with
    | nil => lnil _
    | cons h ts => lazy_append h (join_list_lazy_list ts)
    end.


  (*
  (*
    Okay, so each rose tree has a list at each spot. Presumably this
    list is then shrunk... Which sounds... Bad.
   *)
  Fixpoint smoosh {A : Type} (rl : Rose (LazyList A)) : LazyList (Rose A) :=
    match rl with
    | MkRose h ts =>
      lazy_append _ _

        (* h (join_list_lazy_list (map smoosh (force ts))) *)
    end.

  Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun n r => fmapRose (fun g => run g n r) m).

   *)
  
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

  Definition suchThatMaybeOptAux {A : Type} (g : G (option A)) (p : A -> bool) :=
    fix aux (k : nat) (n : nat) : G (option A) :=
    match n with
      | O => returnGen None
      | S n' =>
        (* What is this 2 * k + n ? *)
        bindGen (resize (2 * k + n) g) 
                (fun mx => match mx with 
                          | Some x => if p x then returnGen (Some x) else (aux (S k) n')
                          | _ => aux (S k) n'
                        end)
    end.

  Definition suchThatMaybeOpt {A : Type} (g : G (option A)) (p : A -> bool)
  : G (option A) := 
    sized (fun x => suchThatMaybeOptAux g p 0 (max 1 x)).

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
  
  Definition sample (A : Type) (g : G A) : list (LazyList A) :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.
  
  (* LL : Things that need to be in GenLow because of MkGen *)
  
  Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.

  (*
  Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n => _ (*(match g with MkGen f => f r n end) *)).

  Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).
   *)
  (* End Things *)

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated above) *)
  (* begin semGen *)

  Fixpoint All_ll {A : Type} (P : A -> Prop) (l : LazyList A) : Prop :=
    match l with
    | lnil => True
    | lcons h ts => P h /\ All_ll P (force ts)
    end.

  Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := possibly_generated (run g s).
  Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.
  (* end semGen *)

  (* More things *)
  (* TODO Need a better induction principle for lazy lists... *)
  Check LazyList_ind.

  (* LazyList_ind
     : forall (A : Type) (P : LazyList A -> Prop),
       P (lnil A) -> (forall (a : A) (l : Lazy (LazyList A)), P (lcons A a l)) -> forall l : LazyList A, P l
   *)

  Check list_ind.

  (* list_ind
     : forall (A : Type) (P : list A -> Prop),
       P [] -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> forall l : list A, P l
   *)

  Fixpoint LazyList_to_list {A : Type} (l : LazyList A) : list A :=
    match l with
    | lnil => nil
    | lcons x x0 => x :: LazyList_to_list (force x0)
    end.

  Fixpoint list_to_LazyList {A : Type} (l : list A) : LazyList A :=
    match l with
    | nil => lnil _
    | cons x x0 => lcons _ x (lazy (list_to_LazyList x0))
    end.

  Theorem LazyList_to_list_reflect :
    forall (A : Type) (ll : LazyList A) (l : list A),
      LazyList_to_list ll = l -> ll = list_to_LazyList l.
  Proof.
    intros A ll l H.
    generalize dependent ll.
    induction l; intros ll H.
    - simpl. destruct ll.
      + reflexivity.
      + simpl in H. inversion H.
  Admitted.

  Theorem blah :
    forall (A : Type) (f : list A -> list A) (l : list A) P,
      P l -> P l.
  Proof.
    intros A f l.
    remember (f l) as f_l. generalize dependent f_l.
    induction (f l); intros f_l Heqf_l P X.
    - (* Want to know that f l = [] here *) admit.
    - (* Want to know that f l = x :: xs here *) admit.
  Admitted.

  Theorem nil_lazylist :
    forall A (l : LazyList A),
      [] = LazyList_to_list l -> l = lnil A.
  Proof.
    intros A l H.
    destruct l.
    - reflexivity.
    - inversion H.
  Qed.

  Section Ind.
    Variable A : Type.
    Variable P : LazyList A -> Prop.
    Variable Hnil : P (lnil A).
    Variable Hcons : forall (a : A) (l : LazyList A), P l -> P (lcons _ a (lazy l)).

    Fixpoint better_ll_ind (l : LazyList A) : P l :=
      match l with
      | lnil => Hnil
      | lcons a (lazy tl) => @Hcons a tl (better_ll_ind tl)
      end.
  End Ind.

  Program Definition bindGen' {A B : Type} (g : G A) (k : forall (a : A), (a \in semGen g) -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             _).
  Next Obligation.
    remember (run g n r1) as a's.
    destruct a's.
    - exact (lnil _).
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

  (** Sized generators of option type monotonic in the size parameter *)
  (*
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    {
      sizeMonotonicOpt :
        forall s s1 s2,
          s1 <= s2 ->
          isSome :&: semGenSize (g s1) s \subset isSome :&: semGenSize (g s2) s
    }.
   *)
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    {
      monotonic :
        forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2
    }.

  (** Generators monotonic in the runtime size parameter *)
  (*
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    {
      monotonic_opt :
        forall s1 s2, s1 <= s2 -> isSome :&: semGenSize g s1 \subset isSome :&: semGenSize g s2
    }.
   *)

  (*
  Class SizeAntiMonotonicNone {A} (g : G (option A)) :=
    {
      monotonic_none :
        forall s1 s2, s1 <= s2 -> isNone :&: semGenSize g s2 \subset isNone :&: semGenSize g s1
    }.
   *)

  
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

  (* begin semReturn *)
  Lemma semReturn {A} (x : A) : semGen (returnGen x) <--> [set x].
  (* end semReturn *)
  Proof.
    rewrite /semGen /semGenSize /= bigcup_const ?codom_const //.
    split.
    - intros H. inversion H. inversion H0. subst. constructor. inversion H1.
    - intros H. inversion H. unfold possibly_generated. destruct randomSeed_inhabited as [r]. exists r.
      constructor. auto.
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
      + inversion H0.
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

  (*
  Instance returnGenSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnGen x).
  Proof.
    firstorder.
  Qed.
  *)

  (* begin semBindSize *)
  Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
               \bigcup_(a in semGenSize g s) semGenSize (f a) s.
  (* end semBindSize *)
  Proof.
    unfold semGenSize, possibly_generated.
    split.
    - intros [r H]. unfold bigcup.
      remember (run (bindGen g f) s r) as run.
      generalize dependent Heqrun.
      revert g f s r H.
      induction run using better_ll_ind; intros g f s r H Heqrun.
      + inversion H.
      + simpl in H. destruct H.
        * subst. unfold run in Heqrun. simpl in Heqrun.
          pose proof randomSplit_codom. edestruct H.
          destruct (randomSplit r) as [r1 r2].
          eapply IHrun.
          
          induction (run g s r1) using better_ll_ind; inversion Heqrun.
          simpl in *.
          destruct (randomSplit r2) as [r3 r4].
          simpl in *.


    
    - intros [r H]. unfold bigcup.
      simpl in H.
      destruct (randomSplit r) as [r1 r2].
      induction (run g s r1) using better_ll_ind.
      + inversion H.
      + apply IHl.
        simpl in H. destruct (randomSplit r2) as [r3 r4].
        destruct (run (f a0) s r3).
        * simpl in *. 
    
    rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
      by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
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
  
  Lemma semBindSizeOpt_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G (option B)) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
    (forall s, isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply setI_subset_compat. eapply subset_refl.
    eapply incl_bigcupl. eapply H1.
    rewrite !setI_bigcup_assoc. 
    eapply incl_bigcupr. intros. eapply H2.
  Qed.
  
  Lemma monad_leftid A B (a : A) (f : A -> G B) :
    semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Proof.
      by apply: eq_bigcupr => size; rewrite semBindSize semReturnSize bigcup_set1.
  Qed.
  
  Lemma monad_rightid A (g : G A) : semGen (bindGen g returnGen) <--> semGen g.
  Proof.
    apply: eq_bigcupr => size; rewrite semBindSize.
      by rewrite (eq_bigcupr _ (fun x => semReturnSize x size))
                 /semGenSize bigcup_codom codomE.
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

  Program Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGen g f).
  Next Obligation.
    rewrite !semBindSize. move => b.
    move => [Hsome [a [H4 H5]]]. destruct b; try discriminate.
    split; eauto.
    eexists a; split => //. eapply monotonic; eauto.
    assert (Hin : (isSome :&: semGenSize (f a) s1) (Some b)).
    { split; eauto. }
    eapply monotonic_opt in Hin; eauto. now inv Hin.
  Qed.

  Instance bindOptMonotonicOpt
          {A B} (g : G (option A)) (f : A -> G (option B))
          `{SizeMonotonicOpt _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGenOpt g f).
  Proof.
    constructor. intros s1 s2 Hleq.
    rewrite !semBindSize. move => b.
    move => [Hsome [a [H4 H5]]]. destruct b; try discriminate.
    split; eauto.
    eexists a.
    destruct a.
    - split.
      assert (Hin : (isSome :&: semGenSize g s1) (Some a)).
      { split; eauto. }
      eapply monotonic_opt; eauto.
      assert (Hin : (isSome :&: semGenSize (f a) s1) (Some b)).
      { split; eauto. }
      eapply monotonic_opt; eauto.
    - eapply semReturnSize in H5. inv H5.
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
  
  Program Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindGen g f).
  Next Obligation.
    rewrite !semBindSize. move => b.
    move => [Hsome [a [H4 H5]]]. destruct b; try discriminate.
    split; eauto.
    eexists a; split => //. eapply monotonic; eauto.
    assert (Hin : (isSome :&: semGenSize (f a) s1) (Some b)).
    { split; eauto. }
    assert (Hmon : SizeMonotonicOpt (f a)).
    { eapply H0. eexists; split; eauto. now constructor. }
    eapply monotonic_opt in Hin; eauto.
    inv Hin. eassumption.
  Qed.

  Instance bindOptMonotonic
           {A B} (g : G (option A)) (f : A -> G (option B))
           `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGenOpt g f).
  Proof.
    constructor. intros s1 s2 Hleq.
    intros x Hx. eapply semBindSize in Hx.
    destruct Hx as [a [Hg Hf]].
    destruct a as [a | ].
    - eapply H in Hg; try eassumption.
      eapply H0 in Hf; try eassumption.
      eapply semBindSize.
      eexists; split; eauto.
    - eapply H in Hg; try eassumption.
      eapply semReturnSize in Hf. inv Hf.
      eapply semBindSize.
      eexists; split; eauto. simpl.
      eapply semReturnSize.
      reflexivity.
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

  Lemma semBindOptSizeMonotonicIncl_r {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B) :
    semGen g \subset (Some @: s1) :|: [set None] ->
    (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
    semGen (bindGenOpt g f) \subset Some @: (\bigcup_(a in s1) s2 a) :|: [set None].
  Proof.
    intros H1 H2 [x |] [s [_ [r H]]]; [| right; reflexivity ].
    left.
    eexists; split; [| reflexivity ].
    simpl in H. destruct (randomSplit r) as [r1 r2] eqn:Heq.
    destruct (run g s r1) eqn:Heq2; try discriminate.
    eexists a. 
    split.
    + edestruct H1.
      * eexists. split; [| eexists; eauto ]. now constructor.
      * inv H0. inv H3. inv H5. eassumption.
      * inv H0.
    + edestruct H2.
      * eexists. split; [| eexists; eauto ]. now constructor.
      * inv H0. inv H3. inv H5. inv H3. eassumption.
      * inv H0.
  Qed.
  
  Lemma semBindSizeMonotonicIncl_r {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B) :
    semGen g \subset s1 ->
    (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
    semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].
  Proof.
    intros H1 H2 [x |] [s [_ [r H]]]; [| right; reflexivity ].
    left.
    eexists; split; [| reflexivity ].
    simpl in H. destruct (randomSplit r) as [r1 r2] eqn:Heq.
    destruct (run (f (run g s r1)) s r2) eqn:Heq2; try discriminate.
    inv H. eexists (run g s r1). split.
    eapply H1. eexists; split; [| eexists; reflexivity ].
    now constructor.
    edestruct H2.
    * eexists. split; [| eexists; eauto ]. now constructor.
    * inv H0. inv H3. inv H5. eassumption.
    * inv H0.
  Qed.
  
  Lemma semBindOptSizeMonotonicIncl_l {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A)
        (fs : A -> set B) 
        `{Hg : SizeMonotonicOpt _ g}
        `{Hf : forall a, SizeMonotonicOpt (f a)} :
    Some @: s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGenOpt g f).
  Proof.
    intros H1 H2 y [y' [[x [Hs1 Hfs2]] Heq]]; inv Heq; clear Heq.
    assert (Hin1 : (Some @: s1) (Some x)).
    { eexists; split; eauto. now constructor. }
    assert (Hin2 : (Some @: fs x) (Some y')).
    { eexists; split; eauto. now constructor. }
    eapply H1 in Hin1. eapply H2 in Hin2.
    destruct Hg as [Hgmon].
    destruct (Hf x) as [Hfgmon].
    edestruct Hin1 as [s [_ Hgen]].
    edestruct Hin2 as [s' [_ Hfgen]].
    assert (Hin1' : ((fun u : option A => u) :&: semGenSize g s) (Some x)).
    { split; eauto. }
    assert (Hin2' : ((fun u : option B => u) :&: semGenSize (f x) s') (Some y')).
    { split; eauto. }
    eapply Hgmon with (s2 := s + s')  in Hin1'; [| now ssromega ].
    eapply Hfgmon with (s2 := s + s')  in Hin2'; [| now ssromega ].
    edestruct Hin1' as [_ [r1 Hr1]].
    edestruct Hin2' as [_ [r2 Hr2]].
    eexists (s + s'). split; [ now constructor |].
    edestruct (randomSplitAssumption r1 r2) as [r'' Heq].
    eexists r''. simpl. rewrite Heq.
    rewrite Hr1 Hr2. reflexivity.
  Qed.

  Lemma semBindSizeMonotonicIncl_l {A B} (g : G A) (f : A -> G (option B)) (s1 : set A)
        (fs : A -> set B) 
        `{Hg : SizeMonotonic _ g}
        `{Hf : forall a, SizeMonotonicOpt (f a)} :
    s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGen g f).
  Proof.
    intros H1 H2 y [y' [[x [Hs1 Hfs2]] Heq]]; inv Heq; clear Heq.
    eapply H1 in Hs1.
    assert (Hin2 : (Some @: fs x) (Some y')).
    { eexists; split; eauto. now constructor. }
    eapply H2 in Hin2.
    destruct Hg as [Hgmon].
    destruct (Hf x) as [Hfgmon].
    edestruct Hs1 as [s [_ Hgen]].
    edestruct Hin2 as [s' [_ Hfgen]].
    assert (Hin2' : ((fun u : option B => u) :&: semGenSize (f x) s') (Some y')).
    { split; eauto. }
    eapply Hgmon with (s2 := s + s')  in Hgen; [| now ssromega ].
    eapply Hfgmon with (s2 := s + s')  in Hin2'; [| now ssromega ].
    edestruct Hgen as [r1 Hr1].
    edestruct Hin2' as [_ [r2 Hr2]].
    eexists (s + s'). split; [ now constructor |].
    edestruct (randomSplitAssumption r1 r2) as [r'' Heq].
    eexists r''. simpl. rewrite Heq.
    rewrite Hr1 Hr2. reflexivity.
  Qed.
  
  Lemma  semBindOptSizeOpt_subset_compat {A B : Type} (g g' : G (option A)) (f f' : A -> G (option B)) :
    (forall s, isSome :&: semGenSize g s \subset isSome :&: semGenSize g' s) ->
    (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
    (forall s, isSome :&: semGenSize (bindGenOpt g f) s \subset isSome :&: semGenSize (bindGenOpt g' f') s).
  Proof.
    intros Hg Hf s x [Hin1 Hin2].
    split; [ eassumption |].
    unfold bindGenOpt in *.
    eapply semBindSize in Hin2. destruct Hin2 as [a [Hg' Hf']].
    destruct a as [a |].
    - assert (Hg'' : ((fun u : option A => u) :&: semGenSize g s) (Some a)).
      { split; eauto. }
      eapply Hg in Hg''.  destruct Hg'' as [_ Hg''].
      eapply semBindSize. eexists; split; [ eassumption |].
      simpl. eapply Hf. split; eauto.
    - eapply semReturnSize in Hf'.  inv Hf'. discriminate.
  Qed.
  
  Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
    semGenSize (fmap f g) size <--> f @: semGenSize g size.  Proof.
      by rewrite /fmap /semGenSize /= codom_comp.
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

  Lemma semSized_opt A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f) :
    isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).
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
      + assert (Hin: (isSome :&: semGenSize (f n) m) (Some x)).
        { split; eauto. }
        eapply (H n) with (s2 := m + n) in Hin; [| now ssromega ].
        eapply H' with (s2 := m + n) in Hin; [| now ssromega ].
        inv Hin. eassumption.
      + inv Hs1.
  Qed.

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

  Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  Proof.
    constructor. move => s1 s2 Hleq a [H1 /semSizedSize H2].
    split; eauto. eapply semSizedSize.
    eapply H. eassumption.
    have [_ Ha] : (isSome :&: semGenSize (gen s2) s1) a.
    { eapply H0. eassumption. split; eauto. }
    eassumption.
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
      simpl. rewrite !semReturnSize. now apply subset_refl.
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

  Lemma suchThatMaybeAux_exists {A} (g : G (option A)) s p k n x :
    semGenSize (suchThatMaybeOptAux g p k n) s (Some x) ->
    exists s, s >= 2*k + n /\ s < 2*(k + n) /\ semGenSize g s (Some x) /\ p x.
  Proof.
    elim : n k => [| n IHn ] k /= H.
    - eapply semReturnSize in H; inv H.
    - eapply semBindSize in H. destruct H as [a [Hg Hf]].
      eapply semSizeResize with (g := g) in Hg. destruct a.
      + destruct (p a) eqn:heq.
        * eapply semReturnSize in Hf. inv Hf. eexists.
          split; [| split; [| split; [ eassumption | now eauto ] ]];
            by ssromega.
        * edestruct IHn as [s' [Hleq1 [Hleq2 [Hgen Hp]]]]. eassumption.
          eexists. 
          repeat split; try eassumption. ssromega. ssromega.
      + edestruct IHn as [s' [Hleq1 [Hleq2 [Hgen Hp]]]]. eassumption.
        eexists. 
        repeat split; try eassumption. ssromega. ssromega.
  Qed.

  Lemma suchThatMaybeAux_exists_strong {A} (g : G (option A)) s p k n x :
    semGenSize (suchThatMaybeOptAux g p k n) s (Some x) ->
    exists s, s >= 2*k + n /\ s < 2*(k + n) /\ semGenSize g s (Some x) /\ p x /\
         (forall s', 2*k + n <= s' < s -> (semGenSize g s' None \/ exists x, semGenSize g s' (Some x) /\ ~ p x)).
  Proof.
    elim : n k => [| n IHn ] k /= H.
    - eapply semReturnSize in H; inv H.
    - eapply semBindSize in H. destruct H as [a [Hg Hf]].
      eapply semSizeResize with (g := g) in Hg. destruct a.
      + destruct (p a) eqn:heq.
        * eapply semReturnSize in Hf. inv Hf. eexists.
          split; [| split; [| split; [ eassumption | split; [ now eauto |] ] ]];
          try intros; by ssromega.
        * edestruct IHn as [s' [Hleq1 [Hleq2 [Hgen [Hp Hstrong]]]]]. eassumption.
          eexists. 
          repeat split; try eassumption. ssromega. ssromega.
          move => m /andP [Hleq Hlt]. specialize (Hstrong m).
          destruct (Nat.eq_dec m (2 * k + n.+1)).
          { subst. right. eexists ; split; eauto. }
          { eapply Hstrong. ssromega. }
      + edestruct IHn as [s' [Hleq1 [Hleq2 [Hgen [Hp Hstrong]]]]]. eassumption.
        eexists.
        repeat split; try eassumption. ssromega. ssromega.
        move => m /andP [Hleq Hlt]. specialize (Hstrong m). 
        destruct (Nat.eq_dec m (2 * k + n.+1)).
        { subst. left. eassumption. } 
        { eapply Hstrong. ssromega. }
  Qed.

  Lemma semGenSizeInhabited {A} (g : G A) s :
    exists x, semGenSize g s x.
  Proof.
    destruct randomSeed_inhabited as [r].
    eexists (run g s r ). unfold semGenSize, codom.
    exists r. reflexivity.
  Qed.

  Lemma semSizeGenSuchThatMaybeOptAux_sound_alt {A} :
    forall g p k n (a : A) size seed,
      run (suchThatMaybeOptAux g p k n) size seed = Some a ->
      (exists s, s >= 2*k + n /\ (Some a) \in semGenSize g s :&: (Some @: p)).
  Proof.
    case=> g p k n; elim: n k =>  [//=| n IHn] k a size seed /=.
    case: (randomSplit seed) => r1 r2 Hrun.
    destruct (g (2 * k + n.+1) r1) as [a' |] eqn:Heq.
    - destruct (p a') eqn:Hpa.
      + inv Hrun.
        eexists (2 * k + n.+1). split. by ssromega.
        split.
        eexists. eassumption.
        eexists. split. eassumption. reflexivity.
      + edestruct IHn as [s [Hleq [Hg Hs]]]; [ eassumption |].
        exists s. split. by ssromega.
        split; eassumption. 
    - edestruct IHn as [s [Hleq [Hg Hs]]]; [ eassumption |].
      exists s. split. by ssromega.
      split; eassumption.
  Qed.
  
  Lemma semGenSizeSuchThatMaybeOptAux_complete {A} :
    forall g (p : A -> bool) k s n,
      n > 0 ->
      2*k + n >= s ->
      SizeMonotonicOpt g ->
      (semGenSize g s :&: ( Some @: p )) \subset semGenSize (suchThatMaybeOptAux g p k n) s.
  Proof.
    intros g p k s.
    intros n Hleq1 Hleq2 Hmon x [Hg [a [Hp Hs]]].
    destruct x as [x | ]; try discriminate. inv Hs.
    case : n k Hleq1 Hleq2 => [//= | n] k Hleq1 Hleq2.
    simpl. eapply semBindSize.
    exists (Some x). split. eapply semSizeResize.
    have [_ Ha] : (isSome :&: semGenSize g (2 * k + n.+1)) (Some x).
    { eapply Hmon; [| split; eauto ]. by ssromega. }
    eassumption.
    rewrite Hp.
    apply semReturnSize. reflexivity.
  Qed.


  Instance SuchThatMaybeAuxOptUnsized  {A} :
    forall (g : G (option A)) p k n,
      Unsized (suchThatMaybeOptAux g p k n).
  Proof.
   intros g p k n. elim : n k => [| n IHn ] k.
   - constructor. simpl. intros. rewrite !semReturnSize.
     now apply subset_refl.
   - constructor. intros s1 s2.
     simpl.
     rewrite !semBindSize. eapply eq_bigcup'.
     rewrite !semSizeResize. now apply subset_refl.
     intros x. destruct x.
     destruct (p a).
     rewrite !semReturnSize. now apply subset_refl.
     eapply IHn. eapply IHn.
  Qed.

  Lemma semSizeSuchThatMaybeOptAux_sound_alt {A} (g : G (option A)) s p n k :
    SizeMonotonicOpt g ->
    n > 0 ->
    isSome :&: semGenSize (suchThatMaybeOptAux g p k n) s \subset
    (\bigcup_(s in (fun s => s < 2*(k + n))) semGenSize g s) :&: (Some @: (fun x => p x = true)).
  Proof.
    intros Hopt.
    case : n k => [ //= | n ] k Hlt. 
    simpl. rewrite semBindSize semSizeResize.
    intros x [Hsome [y [Hg Hf]]]. destruct x as [a|]; try discriminate.
    destruct y as [a'|].
    + destruct (p a') eqn:Hp. 
      * eapply semReturnSize in Hf; inv Hf. split.
        eexists; split; [| eassumption ]. by ssromega.
        now eexists; split; eauto.
      * eapply suchThatMaybeAux_exists in Hf.
        destruct Hf as [s' [Hleq1 [Hleq2 [Hg' Hp']]]].
        split. exists s'. split; eauto.
        now eexists; split; eauto.
    + eapply suchThatMaybeAux_exists in Hf.
      destruct Hf as [s' [Hleq1 [Hleq2 [Hg' Hp']]]].
      split. exists s'. split; eauto.
      eexists; split; eauto. reflexivity.
  Qed.

  Lemma SuchThatMaybeAuxOptParamMonotonicOpt {A} :
    forall (g : G (option A)) p n1 n2 k s,
      SizeMonotonicOpt g ->
      n1 <= n2 ->
      isSome :&: semGenSize (suchThatMaybeOptAux g p k n1) s \subset
      isSome :&: semGenSize (suchThatMaybeOptAux g p k n2) s.
  Proof.
    intros g p n1. elim : n1 => [| n1 IHn1] n2 k s Hmon Hleq.
    - simpl. rewrite semReturnSize. rewrite setI_set0.
      eapply sub0set. intros [x|]; eauto. intros _ Hc; discriminate Hc.
    - destruct n2; try ssromega.
      simpl. rewrite !semBindSize !semSizeResize.
      intros x [Hs [a [Ha Hg]]]. destruct x as [x|]; try discriminate.
      split; eauto.
      destruct a as [a|].
      + destruct (p a) eqn:Hp.
        * eexists (Some a). split.
          have [_ Ha'] : (isSome :&: semGenSize g (2 * k + n2.+1)) (Some a).
          { eapply Hmon; [| split; eauto ]. ssromega. }
          eassumption. rewrite Hp. eapply semReturnSize in Hg. inv Hg.
          eapply semReturnSize. reflexivity.
        * have [_ Ha'] : (isSome :&: semGenSize g (2 * k + n2.+1)) (Some a).
          { eapply Hmon; [| split; eauto ]. ssromega. }
          eexists. split; eauto. simpl. rewrite Hp.
          eapply IHn1; eauto. split; eauto.
      + assert (Hg' := Hg). 
        eapply suchThatMaybeAux_exists_strong in Hg.
        destruct Hg as [s1 [Hleq1 [Hleq2 [Hin [Hp' Hstrong]]]]]. 
        destruct (s1 <= 2*k + n2.+1) eqn:Hleqs1.
        * eexists (Some x). split.
          have [_ Ha'] : (isSome :&: semGenSize g (2 * k + n2.+1)) (Some x).
          { eapply Hmon; [| split; eauto ]. ssromega. }
          eassumption. rewrite Hp'.
          eapply semReturnSize. reflexivity.
        * { destruct (Nat.eq_dec n1 n2).
            - subst. eexists None. split; eauto.
            - specialize (Hstrong (2 * k + n2.+1)).
              destruct Hstrong as [Hl | [y [Hr Hnp]]].
              + apply/andP; split; try ssromega.
              + eexists None. split; eauto.
                eapply IHn1; eauto. split; eauto.
              + eexists (Some y). split; eauto.
                destruct (p y); try contradiction.
                eapply IHn1; eauto. split; eauto. }
  Qed.
  
  Lemma SuchThatMaybeAuxParamMonotonicOpt {A} :
    forall (g : G A) p n1 n2 k s,
      SizeMonotonic g ->
      n1 <= n2 ->
      isSome :&: semGenSize (suchThatMaybeAux g p k n1) s \subset
      isSome :&: semGenSize (suchThatMaybeAux g p k n2) s.
  Proof.
    intros g p. elim  => [| n IHn ] n2 k s Hmon Heq.
    - intros x [H1 H2]. destruct x; try discriminate.
      eapply semReturnSize in H2. inv H2.
    - intros x [H1 H2]. split; eauto.
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

  Lemma semSuchThatMaybeOpt_sound' A (g : G (option A)) (f : A -> bool) :
    semGen (suchThatMaybeOpt g f) \subset None |: (semGen g :&: (Some @: f)).
  Proof.
    case=> [a [size [_ [x run_x]]] | ]; last by left.
    right. unfold suchThatMaybeOpt in run_x.
    simpl in run_x.
    destruct size;
      eapply semGenSuchThatMaybeOptAux_sound; eassumption.
  Qed. 

  Lemma lt_leq_trans n m u : n < m -> m <= u -> n < u.
  Proof.
    intros H1 H2. ssromega.
  Qed.

  Lemma semGenSizeSuchThatMaybeAux_complete {A} :
    forall g (p : A -> bool) k s n,
      n > 0 ->
      n >= s ->
      SizeMonotonic g ->
      Some @: (semGenSize g s :&: p) \subset semGenSize (suchThatMaybeAux g p k n) s.
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
  

  Lemma semSuchThatMaybeOpt_complete' A (g : G (option A)) (f : A -> bool) :
    SizeMonotonicOpt g -> 
    semGen g :&: (Some @: f) \subset semGen (suchThatMaybeOpt g f).
  Proof.
    intros Hmon.
    intros x [[s [HT Hg]] [a [Hs Hf]]]. inv Hf. exists s.
    split; eauto.
    eapply semGenSizeSuchThatMaybeOptAux_complete; try eassumption.
    eapply lt_leq_trans with (m := 1). by ssromega.
    apply/leP. by eapply Max.le_max_l. 
    apply/leP. by eapply Max.le_max_r. 
    split; eauto.  eexists; split; eauto.
  Qed.
  
  Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
      run g size (varySeed (f a) r1).
  Proof. 
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
  Qed.

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

  Definition GOpt A := G (option A).

  Global Instance Monad_GOpt : Monad GOpt := {
    ret A x := returnGen (Some x);
    bind A B := bindGenOpt;
  }.

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
