Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat seq.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     RandomQC RoseTrees Sets Tactics Producer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> A) -> GenType A.
  
Definition G := GenType.

(** * Primitive generator combinators *)
  
Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
  
Definition returnGen {A : Type} (x : A) : G A :=
  MkGen (fun _ _ => x).

Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
  MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1)) n r2).

Instance MonadGen : Monad G :=
  { ret := @returnGen
  ; bind := @bindGen }.

Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => List.rev (cons O acc)
  | S n' => createRange n' (cons n acc)
  end.

Fixpoint rnds (s : RandomSeed) (n' : nat) : list RandomSeed :=
    match n' with
      | O => nil
      | S n'' =>
        let (s1, s2) := randomSplit s in
        cons s1 (rnds s2 n'')
    end.

Definition sampleGen (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.

Definition sizedGen {A : Type} (f : nat -> G A) : G A :=
  MkGen (fun n r => run (f n) n r).

Definition resizeGen {A : Type} (n : nat) (g : G A) : G A :=
    match g with
    | MkGen m => MkGen (fun _ => m n)
    end.

Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := codom (run g s).

Definition chooseGen {A : Type} `{ChoosableFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ r => fst (randomR range r)).

Program Instance ProducerGen : Producer G :=
  {
  super := MonadGen;

  sample := sampleGen;
  
  sized  := @sizedGen; 
  resize := @resizeGen;

  choose := @chooseGen;
  
  semProdSize := @semGenSize;

  (* Probably belongs in another class for modularity? *)
  bindPf :=
    fun {A B : Type} (g : G A)
        (k : forall (a : A),
            (fun (A : Type) (g : G A) =>
               \bigcup_(size in [set: nat]) semGenSize g size) A g a -> G B) =>
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1) _) n r2)}.
Next Obligation.
  unfold semGenSize, codom, bigcup.
  exists n; split => //=.
  exists r1; auto.
Defined.

(* Generator specific sample of a single input. *)
Definition sample1 (A : Type) (g : G A) : A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        m 10 rnd
    end.

(* Generator specific - shrinking support. *)
Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun n r => fmapRose (fun g => run g n r) m).

(* Generator specific - coarbitrary support. *)
Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.
  
Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n g => (match g with MkGen f => f r n end)).
  
Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).

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
    semProd (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
Proof. by rewrite /codom2 curry_codom2l. Qed.

Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semGenSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
Proof. by []. Qed.

Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
Proof. by []. Qed.


(* Generator specific - choose and its semantics. *)
Definition choose {A : Type} `{ChoosableFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ r => fst (randomR range r)).


Lemma semChooseSize A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.
  
Instance chooseUnsized {A} `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
Proof. by []. Qed.
  
Lemma semChoose A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
Proof.
  move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
  move => m /=. rewrite (randomRCorrect m a1 a2) //.
Qed.

  Definition thunkGen {A} (f : unit -> G A) : G A :=
    MkGen (fun n r => run (f tt) n r).

  Lemma semThunkGenSize {A} (f : unit -> G A) s :
    semProdSize (thunkGen f) s <--> semProdSize (f tt) s.
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Lemma semThunkGen {A} (f : unit -> G A) :
    semProd (thunkGen f) <--> semProd (f tt).
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Instance thunkGenUnsized {A} (f : unit -> G A)
          `{@Unsized _ _ ProducerGen (f tt)} : Unsized (thunkGen f).
  Proof.
    intros s1 s2.
    Set Printing All.
    do 2 rewrite semThunkGenSize.
    apply unsized.
  Qed.

  Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{@SizeMonotonic _ _ ProducerGen (f tt)} : SizeMonotonic (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonic.
  Qed.

  Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{@SizeMonotonicOpt _ _ ProducerGen (f tt)} : SizeMonotonicOpt (thunkGen f).
  Proof.
    intros s1 s2 Hs. unfold semProdSizeOpt.
    do 2 rewrite semThunkGenSize.
    by apply monotonicOpt.
  Qed.

  Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{@SizeAntiMonotonicNone _ _ ProducerGen (f tt)} : SizeAntiMonotonicNone (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonicNone.
  Qed.

Fixpoint pick {A : Type} (def : G A) (xs : list (nat * G A)) n : nat * G A :=
  match xs with
    | nil => (0, def)
    | (k, x) :: xs =>
      if (n < k) then (k, x)
      else pick def xs (n - k)
  end.

(* This should use urns! *)
Fixpoint pickDrop {A : Type} (xs : list (nat * G (option A))) n : nat * G (option A) * list (nat * G (option A)) :=
  match xs with
    | nil => (0, returnGen None, nil)
    | (k, x) :: xs =>
      if (n < k) then  (k, x, xs)
      else let '(k', x', xs') := pickDrop xs (n - k)
           in (k', x', (k,x)::xs')
  end. 

Definition sum_fst {A : Type} (gs : list (nat * A)) : nat :=
  foldl (fun t p => t + (fst p)) 0 gs.

Definition freq_ {A : Type} (def : G A) (gs : list (nat * G A))
: G A :=
  let tot := sum_fst gs in
  bindGen (choose (0, tot-1)) (fun n =>
  @snd _ _ (pick def gs n)).

(*
Definition frequency {A}:= 
  @deprecate (G A -> list (nat * G A) -> G A) "frequency" "freq_" freq_.
 *)

Fixpoint backtrackFuel {A : Type} (fuel : nat) (tot : nat) (gs : list (nat * G (option A))) : G (option A) :=
  match fuel with 
    | O => returnGen None
    | S fuel' => bindGen (choose (0, tot-1)) (fun n => 
                 let '(k, g, gs') := pickDrop gs n in
                 bindGen g (fun ma =>
                 match ma with 
                   | Some a => returnGen (Some a)
                   | None => backtrackFuel fuel' (tot - k) gs'
                 end ))
  end.

Definition backtrack {A : Type} (gs : list (nat * G (option A))) : G (option A) :=
  backtrackFuel (length gs) (sum_fst gs) gs.

Definition retryBody {A : Type}
           (retry : nat -> G (option A) -> G (option A))
           (n : nat) (g : G (option A)) : G (option A) :=
  bindGen g (fun x =>
               match x, n with
               | Some a, _ => returnGen (Some a)
               | None, O => returnGen None
               | None, S n' => retry n' g
               end).

(* Rerun a generator [g] until it returns a [Some], or stop after
     [n+1] tries. *)
Fixpoint retry {A : Type} (n : nat) (g : G (option A)) :
  G (option A) :=
  retryBody retry n g.

(* Filter the output of a generator [g], returning [None] when the
     predicate [p] is [false]. The generator is run once. *)
Definition suchThatMaybe1 {A : Type} (g : G A) (p : A -> bool) :
  G (option A) :=
  fmap (fun x => if p x then Some x else None) g.

(* Retry a generator [g : G A] until it returns a value satisfying
     the predicate, or stop after [size+1] times, where [size] is the
     current size value. *)
Definition suchThatMaybe {A : Type} (g : G A) (p : A -> bool) :
  G (option A) :=
  sized (fun n => retry n (suchThatMaybe1 g p)).

(* Retry a generator [g : G (option A)] until it returns a value
     satisfying the predicate, or stop after [size+1] times, where
     [size] is the current size value. *)
Definition suchThatMaybeOpt {A : Type} (g : G (option A))
           (p : A -> bool) : G (option A) :=
  sized (fun n => retry n (fmap (fun x =>
                                   match x with
                                   | None => None
                                   | Some a => if p a then Some a else None
                                   end) g)).

(* Retry a generator until it returns a value, or stop after
     [size+1] times. *)
Definition retrySized {A : Type} (g : G (option A)) : G (option A) :=
  sized (fun n => retry n g).




  
