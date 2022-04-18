From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Require Import List.
Import ListNotations.

From QuickChick Require Import Tactics.

Import MonadNotation.
Open Scope monad_scope.

Set Bullet Behavior "Strict Subproofs".

(* A lazy list *)
(* Laziness is implemented by just thunking the computation for the tail
   of a cons-cell. Since each such tail is used exactly once, there is no
   point in using ocaml's 'lazy' that memoizes computation and results in
   unnecessary overheads. 
 *)
Inductive LazyList (A : Type) : Type :=
| lnil : LazyList A
| lcons : A -> (unit -> (LazyList A)) -> LazyList A.

Arguments lnil {A}.
Arguments lcons {A} _ _.

Fixpoint lazy_append {A : Type} (l1 : LazyList A) (l2 : LazyList A) : LazyList A :=
  match l1 with
  | lnil => l2
  | lcons x l1' => lcons x (fun _ => (lazy_append (l1' tt) l2))
  end.

Fixpoint lazy_append' {A : Type} (l1 : LazyList A) (l2 : unit -> LazyList A) : LazyList A :=
  match l1 with
  | lnil => l2 tt

(*                     
    match l2 tt with
    | lnil => lsing x
    | l2' => lcons x (fun _ => l2')
    end
*)
  | lcons x l1' => lcons x (fun _ => (lazy_append' (l1' tt) l2))
  end.

Fixpoint lazy_take {A : Type} (n : nat) (l : LazyList A) : LazyList A :=
  match n with
  | 0 => lnil
  | S n' => match l with
            | lnil => lnil
            | lcons h ts => lcons h (fun _ => (lazy_take n' (ts tt)))
            end
  end.

(* Functor instace for LazyList *)
Fixpoint mapLazyList {A B : Type} (f : A -> B) (l : LazyList A) : LazyList B :=
  match l with
  | lnil => lnil
  | lcons x l' => lcons (f x) (fun _ => (mapLazyList f (l' tt)))
  end.

#[global] Instance FunctorLazyList : Functor LazyList :=
  {
    fmap := @mapLazyList
  }.


(* Monad and applicative instances for LazyList *)
(* Injecting into a monad must crucially use the singleton constructor. *)
Definition retLazyList {A : Type} (a : A) : LazyList A :=
  lcons a (fun _ => lnil).
(*   lcons _ a (fun _ => (lnil _)). *)

Fixpoint concatLazyList {A : Type} (l : LazyList (LazyList A)) : LazyList A :=
  match l with
  | lnil => lnil
  | lcons x l' => lazy_append x (concatLazyList (l' tt))
  end.

Definition bindLazyList {A B : Type} (l : LazyList A) (f : A -> LazyList B) : LazyList B :=
  concatLazyList (mapLazyList f l).

#[global] Instance MonadLazyList : Monad LazyList :=
  {
    ret := @retLazyList;
    bind := @bindLazyList
  }.


Definition apLazyList {A B : Type} (lab : LazyList (A -> B)) (la : LazyList A) : LazyList B :=
  ab <- lab;;
  a <- la;;
  ret (ab a).

#[global] Instance ApplicativeLazyList : Applicative LazyList :=
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
  | false => lnil
  end.


(* Lazy list in *)
Fixpoint In_ll {A : Type} (a : A) (l : LazyList A) : Prop :=
  match l with
  | lnil => False
  | lcons h ts => h = a \/ In_ll a (ts tt)
  end.

Fixpoint All_ll {A : Type} (P : A -> Prop) (l : LazyList A) : Prop :=
  match l with
  | lnil => True
  | lcons h ts => P h /\ All_ll P (ts tt)
  end.

From Coq Require Import ssreflect.
Lemma lazy_in_map_iff :
  forall (A B : Type) (f : A -> B) (l : LazyList A) (y : B),
  In_ll y (mapLazyList f l) <-> (exists x : A, f x = y /\ In_ll x l).
Proof.
  move => A B f l; induction l => y; split => [HIn | [x [Hfx HIn]]].
  - inversion HIn.
  - inversion HIn.
  - simpl in *.
    destruct HIn as [Hf | HIn].
    + exists a; split; auto.
    + apply H in HIn.
      destruct HIn as [x [Hf HIn]].
      exists x; split; auto.
  - destruct HIn as [Hf | HIn]; subst; simpl in *; auto.
    right; apply H.
    exists x; auto.
Qed.

    (*
Section Ind.

  Variable A : Type.
  Variable P : LazyList A -> Prop.
  Variable Hnil  : P (lnil).
  Variable Hsing : forall (a : A), P (lsing a).
  Variable Hcons : forall (a : A) (l : LazyList A), P l -> P (lcons a (fun _ => l)).

  Fixpoint better_ll_ind (l : LazyList A) : P l :=
    match l with
    | lnil => Hnil
    | lsing x => Hsing x
    | lcons a tl => @Hcons a (tl tt) (better_ll_ind (tl tt))
    end.
  
End Ind.
 *)

Lemma lazy_in_app_or :
  forall (A : Type) (l m : LazyList A) (a : A), In_ll a (lazy_append l m) -> In_ll a l \/ In_ll a m.
Proof.
  intros A l.
  induction l; intros m h Hyp; simpl in *; auto.
  - destruct Hyp; subst; simpl in *; auto.
    rewrite or_assoc.
    apply H in H0.
    destruct H0; auto.
Qed.

Lemma lazy_in_or_app :
  forall (A : Type) (l m : LazyList A) (a : A), In_ll a l \/ In_ll a m -> In_ll a (lazy_append l m).
Proof.
  intros A l.
  induction l; intros m h HIn; simpl in *.
  - destruct HIn as [Contra | HIn]; [ contradiction | auto ].
  - destruct HIn as [[HEq | HIn] | HIn]; subst; simpl in *; auto.
Qed.    

Fixpoint LazyList_to_list {A : Type} (l : LazyList A) : list A :=
  match l with
  | lnil => nil
  | lcons x x0 => x :: LazyList_to_list (x0 tt)
  end.

Fixpoint list_to_LazyList {A : Type} (l : list A) : LazyList A :=
  match l with
  | nil => lnil
  | cons x x0 => lcons x (fun _ => (list_to_LazyList x0))
  end.

Theorem nil_lazylist :
  forall A (l : LazyList A),
    [] = LazyList_to_list l -> l = lnil.
Proof.
  intros A l H.
  destruct l; simpl in *; auto; inversion H.
Qed.

Theorem lazy_in_map:
  forall (A B : Type) (f : A -> B) (l : LazyList A) (x : A), In_ll x l -> In_ll (f x) (fmap f l).
Proof.
  intros A B f l.
  induction l; intros x HIn.
  - inversion HIn.
  - destruct HIn as [Hax | Hin]; subst; auto.
    + left. auto.
    + right. auto.
Qed.

Lemma lazy_append_nil_r :
  forall {B : Type} (b : B) l,
    In_ll b l ->
    In_ll b (lazy_append l lnil).
Proof.
  intros B b l H.
  induction l.
  - inversion H.
  - simpl in *. firstorder.
Qed.

Lemma lazy_append_sing_r :
  forall {B : Type} (b x : B) l,
    In_ll b l ->
    In_ll b (lazy_append l (lcons x (fun _ => lnil))).
Proof.
  intros B b x l H.
  induction l.
  - inversion H.
  - simpl in *. firstorder.
Qed.

Lemma lazy_append_in_l :
  forall {B : Type} ll (b : B) l,
    In_ll b l ->
    In_ll b (lazy_append l ll).
Proof.
  intros B ll; induction ll; intros b l0 HIn.
  - auto using lazy_append_nil_r.
  - induction l0.
    + inversion HIn.
    + simpl in *. firstorder.
Qed.

Lemma lazy_append_in_r :
  forall {B : Type} (b : B) l ll,
    In_ll b ll ->
    In_ll b (lazy_append l ll).
Proof.
  intros B b l ll H.
  induction l; simpl; auto.
Qed.

Lemma lazy_concat_in :
  forall {B : Type} (b : B) l ll,
    In_ll b l ->
    In_ll l ll ->
    In_ll b (concatLazyList ll).
Proof.
  intros B b l ll Hb Hbll.
  induction ll; simpl in *; subst; auto.
  destruct Hbll as [Hal | Hinl]; subst;
    auto using lazy_append_in_l, lazy_append_in_r.
Qed.

Fixpoint join_list_lazy_list {A : Type} (l : list (LazyList A)) : LazyList A :=
  match l with
  | nil => lnil
  | cons h ts => lazy_append h (join_list_lazy_list ts)
  end.

Fixpoint joint_list_lazy_list_list {A : Type} (l : list (LazyList A)) : list A :=
  match l with
  | nil => nil
  | cons h ts => (LazyList_to_list h) ++ (joint_list_lazy_list_list ts)
  end.

Fixpoint lazy_seq {A : Type}
           (s : A -> A) (lo : A) (len : nat) :=
  match len with
  | O => lnil
  | S len' => lcons lo (fun tt => lazy_seq s (s lo) len')
  end.

Definition mapLazyListProof {A B : Type}
         (l : LazyList A)          
         (f : forall (x : A), In_ll x l -> B) :
  LazyList B.
Proof.
  induction l.
  - apply lnil.
  - apply lcons.
    + apply (f a).
      left; reflexivity.
    + specialize (X tt).
      refine (fun u => _).
      apply X.
      intros x In.
      apply (f x).
      right; auto.
Defined.

Definition bindLazyListPf {A B : Type}
           (l : LazyList A)
           (f : forall (x : A),
               In_ll x l -> LazyList B) : LazyList B :=
  (concatLazyList (mapLazyListProof l f)).
  
Fixpoint filter_LazyList {A} (p : A -> bool) (l : LazyList A) :=
  match l with
  | lnil => lnil
  | lcons h t => if p h then
                   lcons h (fun tt => filter_LazyList p (t tt))
                 else filter_LazyList p (t tt)
  end.

Require Import Coq.Logic.ClassicalFacts.

Axiom EM : excluded_middle.

Lemma In_ll_Dec {A : Type} (* {_ : Dec_Eq A} *) (x : A) l :
  (LazyList.In_ll x l) \/ (~ LazyList.In_ll x l ).
Proof.
  induction l.
  - right. intros Hc; inv Hc.
  - assert (Hem := EM (x = a)). destruct Hem.
    + left; eauto. left; eauto.
    + destruct (H tt).
      * left. right. eassumption.
      * right. intros Hc. inv Hc; eauto.
Qed.

Lemma lazy_concat_in' :
  forall {B : Type} (b : B) ll,
    LazyList.In_ll b (LazyList.concatLazyList ll) ->
    exists l, LazyList.In_ll b l /\ LazyList.In_ll l ll.
Proof.
  intros B b ll Hbll.
  induction ll; simpl in *; subst; auto.
  - exfalso; eauto.
  - eapply LazyList.lazy_in_app_or in Hbll. inv Hbll; eauto.
    eapply H in H0. destruct H0 as [l' [Hin1 Hin2]].
    eexists. split; eauto. 
Qed.

