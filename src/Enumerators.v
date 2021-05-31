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
     Sets Tactics Producer LazyList.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Inductive EnumType (A:Type) : Type :=
  MkGen : (nat -> LazyList A) -> EnumType A.
  
Definition E := EnumType.

(** * Primitive generator combinators *)

Definition run {A : Type} (g : E A) :=
  match g with MkGen f => f end.

Definition returnEnum {A : Type} (x : A) : E A :=
  MkGen (fun _ => ret x).

  
Definition bindEnum {A B : Type} (g : E A) (k : A -> E B) : E B :=
  MkGen (fun n =>
           x <- run g n;;
           run (k x) n).

Instance MonadEnum : Monad E :=
  { ret := @returnEnum
  ; bind := @bindEnum }.

Definition sampleEnum (A : Type) (g : E A) : list A :=
  LazyList_to_list (run g 4).

Definition sizedEnum {A : Type} (f : nat -> E A) : E A :=
  MkGen (fun n => run (f n) n).

Definition resizeEnum {A : Type} (n : nat) (g : E A) : E A :=
    match g with
    | MkGen m => MkGen (fun _ => m n)
    end.

Definition semEnumSize {A : Type} (g : E A) (s : nat) : set A :=
  fun x => In_ll x (run g s).

Program Instance ProducerEnum : Producer E :=
  {
  super := MonadEnum;

  sample := sampleEnum;
  
  sized  := @sizedEnum; 
  resize := @resizeEnum;

  semProdSize := @semEnumSize;

  (* Probably belongs in another class for modularity? *)
  bindPf :=
    fun {A B : Type} (g : E A)
        (k : forall (a : A),
            (fun (A : Type) (g : E A) =>
               \bigcup_(size in [set: nat]) semEnumSize g size) A g a -> E B) =>
      MkGen (fun n => _)
  }.
Next Obligation.
  remember (run g n) as l.
  refine (bindLazyListPf l _) => x In.
  rewrite /semEnumSize /E in k.
  specialize (k x).
  assert ((\bigcup_(size in [set: nat]) In_ll^~ (run g size)) x).
  { 
    exists n; split; unfold setT; auto.
    rewrite -Heql; auto.
  }     
  specialize (k H).
  inversion k.
  apply (X n).
Defined.

Print ProducerEnum.
Print ProducerEnum_obligation_1.
