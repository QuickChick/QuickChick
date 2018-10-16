From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
From QuickChick Require Import RoseTrees.

Import MonadNotation.
Open Scope monad_scope.


(* A lazy list *)
Inductive LazyList (A : Type) : Type :=
| lnil : LazyList A
| lcons : A -> Lazy (LazyList A) -> LazyList A.


Fixpoint lazy_append {A : Type} (l1 : LazyList A) (l2 : LazyList A) : LazyList A :=
  match l1 with
  | lnil => l2
  | lcons x l1' => lcons _ x (lazy (lazy_append (force l1') l2))
  end.

(* Functor instace for LazyList *)
Fixpoint mapLazyList {A B : Type} (f : A -> B) (l : LazyList A) : LazyList B :=
  match l with
  | lnil => lnil _
  | lcons x l' => lcons _ (f x) (lazy (mapLazyList f (force l')))
  end.

Instance FunctorLazyList : Functor LazyList :=
  {
    fmap := @mapLazyList
  }.


(* Monad and applicative instances for LazyList *)
Definition retLazyList {A : Type} (a : A) : LazyList A :=
  lcons _ a (lazy (lnil _)).

Fixpoint concatLazyList {A : Type} (l : LazyList (LazyList A)) : LazyList A :=
  match l with
  | lnil => lnil _
  | lcons x l' => lazy_append x (concatLazyList (force l'))
  end.

Definition bindLazyList {A B : Type} (l : LazyList A) (f : A -> LazyList B) : LazyList B :=
  concatLazyList (mapLazyList f l).

Instance MonadLazyList : Monad LazyList :=
  {
    ret := @retLazyList;
    bind := @bindLazyList
  }.


Definition apLazyList {A B : Type} (lab : LazyList (A -> B)) (la : LazyList A) : LazyList B :=
  ab <- lab;;
  a <- la;;
  ret (ab a).


Instance ApplicativeLazyList : Applicative LazyList :=
  {
    pure := @retLazyList;
    ap := @apLazyList
  }.

Definition apComp {F: Type -> Type} `{Functor F} {A B C : Type} (f : B -> C) (fab : F (A -> B)) : F (A -> C) :=
  fmap (fun g => fun a => f (g a)) fab.


(* Guard definition, because ExtLib doesn't have Alternative *)
Definition guard (b : bool) : LazyList unit :=
  match b with
  | true => ret tt
  | false => lnil _
  end.


(* Lazy list in *)
Fixpoint In_ll {A : Type} (a : A) (l : LazyList A) : Prop :=
  match l with
  | lnil => False
  | lcons h ts => h = a \/ In_ll a (force ts)
  end.