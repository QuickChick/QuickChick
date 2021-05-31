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
     GenLowInterface RandomQC RoseTrees Sets Tactics Producer.

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

Program Instance ProducerGen : Producer G :=
  {
  super := MonadGen;

  sample := sampleGen;
  
  sized  := @sizedGen; 
  resize := @resizeGen;

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

