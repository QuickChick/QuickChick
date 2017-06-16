Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Random RoseTrees.
Require Import Sets Tactics.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Lemma randomSplit_codom : codom randomSplit <--> setT.
Proof.
by apply/subset_eqP; split=> // [[s1 s2]] _; apply: randomSplitAssumption.
Qed.

(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)
Module Type GenLowInterface.

  (** * Type of generators *)

  Parameter G : Type -> Type.

  (** * Primitive generator combinators *)

  Parameter returnGen  : forall {A : Type}, A -> G A.
  (* TODO: Add dependent combinator *)
  Parameter bindGen :  forall {A B : Type}, G A -> (A -> G B) -> G B.
  Parameter bindGenOpt : forall {A B : Type}, G (option A) -> (A -> G (option B)) -> G (option B).
  Parameter run  : forall {A : Type}, G A -> nat -> RandomSeed -> A.
  Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter sized : forall {A: Type}, (nat -> G A) -> G A.
  Parameter resize : forall {A: Type}, nat -> G A -> G A.
  Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A).
  Parameter suchThatMaybe : forall {A : Type}, G A -> (A -> bool) ->
                                          G (option A).
  Parameter suchThatMaybeOpt : forall {A : Type}, G (option A) -> (A -> bool) ->
                                             G (option A).
  Parameter choose : forall {A : Type} `{ChoosableFromInterval A}, (A * A) -> G A.
  Parameter sample : forall {A : Type}, G A -> list A.


  (* LL: The abstraction barrier is annoying :D *)
  Parameter variant : forall {A : Type}, SplitPath -> G A -> G A.
  Parameter reallyUnsafePromote : forall {r A:Type}, (r -> G A) -> G (r -> A).

  Parameter promoteVariant : forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size 
                               (r r1 r2 : RandomSeed),
                               randomSplit r = (r1,r2) ->                              
                               run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
                               run g size (varySeed (f a) r1).

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated below) *)
  Definition semGenSize {A : Type} (g : G A) (size : nat) : set A :=
    codom (run g size).
  Definition semGen {A : Type} (g : G A) : set A :=
    \bigcup_size semGenSize g size.

  Parameter bindGen' : forall {A B : Type} (g : G A), 
                       (forall (a : A), (a \in semGen g) -> G B) -> G B. 

  Arguments bindGen' [A] [B] _ _.

  (** * Properties of generators *)

  (** A generator is [Unsized] if its semantics does not depend on the runtime size *)
  (* begin Unsized *)
  Class Unsized {A} (g : G A) :=
    {
      unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2
    }.
  (* end Unsized *)
  
  (** Sized generators monotonic in the size parameter *)
  Class SizedMonotonic {A} (g : nat -> G A) :=
    {
      sizeMonotonic :
        forall s s1 s2,
          s1 <= s2 ->
          semGenSize (g s1) s \subset semGenSize (g s2) s
    }.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    {
      sizeMonotonicOpt :
        forall s s1 s2,
          s1 <= s2 ->
          isSome :&: semGenSize (g s1) s \subset isSome :&: semGenSize (g s2) s
    }.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    {
      monotonic :
        forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2
    }.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    {
      monotonic_opt :
        forall s1 s2, s1 <= s2 -> isSome :&: semGenSize g s1 \subset isSome :&: semGenSize g s2
    }.
  
  (* CH: Why does Unsized need a _ when A is marked as implict! *)
  Parameter unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.

  (* begin unsizedMonotonic *)
  Declare Instance unsizedMonotonic : forall {A} (g : G A), Unsized g -> SizeMonotonic g.
  (* end unsizedMonotonic *)
  

  (** *  Semantics of combinators *)
  
  Parameter semReturn :
    forall A (x : A), semGen (returnGen x) <--> [set x].
  Parameter semReturnSize :
    forall A (x : A) size, semGenSize (returnGen x) size <--> [set x].
  
  Declare Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Declare Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).

  Parameter semBindSize :
    forall A B (g : G A) (f : A -> G B) (size : nat),
      semGenSize (bindGen g f) size <-->
                 \bigcup_(a in semGenSize g size) semGenSize (f a) size.
  
  Parameter monad_leftid : 
    forall {A B : Type} (a: A) (f : A -> G B),
      semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Parameter monad_rightid : 
    forall {A : Type} (g : G A),
      semGen (bindGen g returnGen) <--> semGen g.
  Parameter monad_assoc: 
    forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
      semGen (bindGen (bindGen ga fb) fc) <--> 
             semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  
  (* I'm not sure how this universal quantifier will behave *)
  (* begin bindUnsized *)
  Declare Instance bindUnsized {A B} (g : G A) (f : A -> G B)
          `{Unsized _ g} `{forall x, Unsized (f x)} : Unsized (bindGen g f).
  (* end bindUnsized *)

  (* XXX these will always succeed together and they have the same priority *)
  Declare Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).

  Declare Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, semGen g x -> SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).
  
  Parameter semBindUnsized1 :
    forall A B (g : G A) (f : A -> G B) `{Unsized _ g},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B) `{forall a, Unsized (f a)},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindSizeMonotonic :
  forall {A B} (g : G A) (f : A -> G B)
         `{SizeMonotonic _ g} `{forall a, SizeMonotonic (f a)},
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

  Parameter semBindOptSizeMonotonicIncl_r :
    forall {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semGen g \subset (Some @: s1) :|: [set None] ->
      (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semGen (bindGenOpt g f) \subset Some @: (\bigcup_(a in s1) s2 a) :|: [set None].

  Parameter semBindSizeMonotonicIncl_r :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semGen g \subset s1 ->
      (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].

  Parameter semBindOptSizeMonotonicIncl_l :
    forall {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A)  (fs : A -> set B) 
      `{Hg : SizeMonotonicOpt _ g} {Hf : forall a, SizeMonotonicOpt (f a)},
      Some @: s1 \subset semGen g ->
      (forall x, Some @: (fs x) \subset semGen (f x)) ->
      (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGenOpt g f).


  Parameter semBindSizeMonotonicIncl_l :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (fs : A -> set B) 
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonicOpt (f a)},
    s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGen g f).

  Parameter semFmap :
    forall A B (f : A -> B) (g : G A),
      semGen (fmap f g) <--> f @: semGen g.

  Parameter semFmapSize :
    forall A B (f : A -> B) (g : G A) (size : nat),
      semGenSize (fmap f g) size <--> f @: semGenSize g size.

  Declare Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} : 
    Unsized (fmap f g).

  Declare Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).

  Parameter semChoose :
    forall A `{ChoosableFromInterval A} (a1 a2 : A),
      Random.leq a1 a2 ->
      (semGen (choose (a1,a2)) <--> [set a | Random.leq a1 a && Random.leq a a2]).

  Parameter semChooseSize :
    forall A `{ChoosableFromInterval A} (a1 a2 : A),
      Random.leq a1 a2 ->
      forall size, (semGenSize (choose (a1,a2)) size <-->
              [set a | Random.leq a1 a && Random.leq a a2]).

  Declare Instance chooseUnsized A `{ChoosableFromInterval A} (a1 a2 : A) : 
    Unsized (choose (a1, a2)).

  Parameter semSized :
    forall A (f : nat -> G A),
      semGen (sized f) <--> \bigcup_s semGenSize (f s) s.

  Parameter semSizedSize :
    forall A (f : nat -> G A) s,
      semGenSize (sized f) s <--> semGenSize (f s) s.

  (* TODO change name *)

  Parameter semSized_alt :
    forall A (f : nat -> G A) `{forall n, SizeMonotonic (f n)},
      (forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) ->
      semGen (sized f) <--> \bigcup_n (semGen (f n)).

  Parameter semSize_opt :
    forall A (f : nat -> G (option A)) (H : forall n, SizeMonotonic (f n))
      (H' : forall n m s, n <= m -> isSome :&: semGenSize (f n) s \subset isSome :&: semGenSize (f m) s),
    isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).

  Declare Instance sizedSizeMonotonic
          A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).
  
  Parameter semResize :
    forall A (n : nat) (g : G A),
      semGen (resize n g) <--> semGenSize g n.

  Declare Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).


  (* TODO: We need completeness as well - this is not exact *)
  Parameter semSuchThatMaybe_sound:
    forall A (g : G A) (f : A -> bool),
      semGen (suchThatMaybe g f) \subset None |: some @: (semGen g :&: f).

  (* This (very concrete) spec is needed to prove shrinking *)
  Parameter semPromote :
    forall A (m : Rose (G A)),
      semGen (promote m) <-->
      codom2 (fun size seed => fmapRose (fun g => run g size seed) m).

  Parameter semPromoteSize :
    forall (A : Type) (m : Rose (G A)) n,
      semGenSize (promote m) n <-->
      (fun t : Rose A =>
         exists (seed : RandomSeed),
           fmapRose (fun g : G A => run g n seed) m = t).

  (* Those are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete. *)

  Parameter runFmap :
    forall (A B : Type) (f : A -> B) (g : G A) seed size,
      run (fmap f g) seed size = f (run g seed size).
  
  Parameter runPromote :
    forall A (m : Rose (G A)) seed size,
      run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  
  Parameter semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).
  
End GenLowInterface.

Module GenLow : GenLowInterface.

  (** * Type of generators *)

  (* begin GenType *)
  Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> A) -> GenType A.
  (* end GenType *)
  
  Definition G := GenType.

  (** * Primitive generator combinators *)
  
  (* begin run *)
  Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
  (* end run *)
  
  Definition returnGen {A : Type} (x : A) : G A :=
    MkGen (fun _ _ => x).
  
  Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1)) n r2).

  Definition bindGenOpt {A B} (g : G (option A)) (f : A -> G (option B)) : G (option B) :=
    bindGen g (fun ma => 
                 match ma with
                   | None => returnGen None
                   | Some a => f a
                 end).
  
  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
    MkGen (fun n r => f (run g n r)).
  
  Definition sized {A : Type} (f : nat -> G A) : G A :=
    MkGen (fun n r => run (f n) n r).
  
  Definition resize {A : Type} (n : nat) (g : G A) : G A :=
    match g with
      | MkGen m => MkGen (fun _ => m n)
    end.
  
  Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun n r => fmapRose (fun g => run g n r) m).
  
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
    MkGen (fun _ r => fst (randomR range r)).
  
  Definition sample (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := mkRandomSeed 0 in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.
  
  (* LL : Things that need to be in GenLow because of MkGen *)
  
  Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.
  
  Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n g => (match g with MkGen f => f r n end)).
  
  Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).
  
  (* End Things *)

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated above) *)
  (* begin semGen *)
  Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := codom (run g s).
  Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.
  (* end semGen *)

  (* More things *)
  Definition bindGen_aux {A : Type} (g : G A) (n : nat) (r : RandomSeed) : semGen g (run g n r).
    unfold semGen, semGenSize, codom, bigcup.
    exists n; split => //=.
    exists r; auto.
  Qed.

  Definition bindGen' {A B : Type} (g : G A) (k : forall (a : A), (a \in semGen g) -> G B) : G B :=
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1) (bindGen_aux g n r1)) n r2).

  

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
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    {
      sizeMonotonicOpt :
        forall s s1 s2,
          s1 <= s2 ->
          isSome :&: semGenSize (g s1) s \subset isSome :&: semGenSize (g s2) s
    }.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    {
      monotonic :
        forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2
    }.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    {
      monotonic_opt :
        forall s1 s2, s1 <= s2 -> isSome :&: semGenSize g s1 \subset isSome :&: semGenSize g s2
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

  (* begin semReturn *)
  Lemma semReturn {A} (x : A) : semGen (returnGen x) <--> [set x].
  (* end semReturn *)
  Proof.
    rewrite /semGen /semGenSize /= bigcup_const ?codom_const //.
            exact: randomSeed_inhabited.
      by do 2! constructor.
  Qed.
  
  (* begin semReturnSize *)
  Lemma semReturnSize A (x : A) (s : nat) :
  semGenSize (returnGen x) s <--> [set x].
  (* end semReturnSize *)
  Proof.
      by rewrite /semGenSize /= codom_const //; apply: randomSeed_inhabited.
  Qed.
  
  Program Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Next Obligation.
      by rewrite ! semReturnSize; split; auto.
  Qed.
  
  Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Proof.
    firstorder.
  Qed.
  
  (* begin semBindSize *)
  Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
    \bigcup_(a in semGenSize g s) semGenSize (f a) s.
  (* end semBindSize *)
  Proof.
    rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
      by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
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

  Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
    semGenSize (fmap f g) size <--> f @: semGenSize g size.
  Proof.
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
    Random.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | Random.leq a1 a && Random.leq a a2].
  Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.
  
  Program Instance chooseUnsized {A} `{ChoosableFromInterval A} (a1 a2 : A) : 
    Unsized (choose (a1, a2)).
  Next Obligation. by []. Qed.
  
  Lemma semChoose A `{ChoosableFromInterval A} (a1 a2 : A) :
    Random.leq a1 a2 ->
    (semGen (choose (a1,a2)) <--> [set a | Random.leq a1 a && Random.leq a a2]).
  Proof. 
    move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
    move => m /=. rewrite (randomRCorrect m a1 a2) //.
  Qed.

  Lemma semSized A (f : nat -> G A) :
    semGen (sized f) <--> \bigcup_n semGenSize (f n) n.
  Proof. by []. Qed.

  Lemma semSizedSize A(f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
  Proof. by []. Qed.

  Lemma semSize_opt A (f : nat -> G (option A)) (H : forall n, SizeMonotonic (f n))
        (H' : forall n m s, n <= m -> isSome :&: semGenSize (f n) s \subset isSome :&: semGenSize (f m) s) :
    isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized. rewrite !setI_bigcup_assoc.
    move => x; split.
    - move => [n [HT [Hs1 Hs2]]].
      eexists. split; eauto. split; eauto. eexists; eauto.
    - move => [n [HT [Hs1 [m [HT' Hs2]]]]].
      eexists (m + n).
      split. now constructor. 
      split; [ eassumption | ]. eapply (H' n). ssromega.
      split; [ eassumption | ].
      eapply (H n); try eassumption. ssromega.
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
  
  Lemma semResize A n (g : G A) : semGen (resize n g) <--> semGenSize g n .
  Proof.
      by case: g => g; rewrite /semGen /semGenSize /= bigcup_const.
  Qed.
  
  Program Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).
  Next Obligation.
    rewrite /Unsized /resize /semGenSize.
    destruct g; split; auto.
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
  Lemma semSuchThatMaybe_sound A (g : G A) (f : A -> bool) :
    semGen (suchThatMaybe g f) \subset
           None |: some @: (semGen g :&: f).
  Proof.
    case=> [a [size [_ [x run_x]]] | ]; last by left.
    by right; exists a; split=> //; apply: (semGenSuchThatMaybeAux_sound run_x).
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
  
End GenLow.