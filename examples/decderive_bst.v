From Coq Require Import Init.Nat Lia.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssreflect.eqtype.
Import QcNotation. Import QcDefaultNotation.

Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.


From Ltac2 Require Import Ltac2.


(* Some small examples for checker proof derivation *)

Inductive wf_list : list nat -> Prop :=
| lnil : wf_list nil
| lcons :
    forall l,
      wf_list l -> wf_list l.

Derive DecOpt for (wf_list l).

Inductive wf_list2 : list nat -> Prop :=
| lcons2 :
    forall l,
      wf_list2 l -> wf_list2 l.

Derive DecOpt for (wf_list2 l).

(* For each DecOpt instance we should be able to derive the following *) 

Instance DecOptwf_listSizeMonotonic l : DecOptSizeMonotonic (wf_list l).
Proof. derive_mon (). Qed. 

Instance DecOptwf_list_sound l : DecOptSoundPos (wf_list l).
Proof. derive_sound (). Qed.

Instance DecOptwf_list_complete l : DecOptCompletePos (wf_list l).
Proof. derive_complete (). Qed.


(* Counter-example for completess *) 
Goal (forall l, ~ wf_list2 l).
Proof.
  intros l Hwf. induction Hwf; eauto.
Qed. 

Inductive list_len : nat -> list nat -> Prop :=
| nil_len : list_len 0 nil
| cons_len :
    forall n x l,
      list_len n l ->
      wf_list l -> (* silly; just to test proofs *) 
      list_len (S n) (x :: l). 

Derive DecOpt for (list_len n l).


Instance DecOptlist_lenSizeMonotonic n l : DecOptSizeMonotonic (list_len n l).
Proof. derive_mon (). Qed. 

Instance DecOptlist_len_sound n l : DecOptSoundPos (list_len n l).
Proof. derive_sound (). Qed.

Instance DecOptlist_len_complete n l : DecOptCompletePos (list_len n l).
Proof. derive_complete (). Qed.


Inductive tree :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.
Derive Show for tree.
Derive Arbitrary for tree.

Derive ArbitrarySizedSuchThat for (fun n => le n n').
Derive ArbitrarySizedSuchThat for (fun n' => le n n').

Inductive bst : nat -> nat -> tree -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node n t1 t2).

Derive DecOpt for (le n m).
Derive DecOpt for (bst min max t).

(* For each DecOpt instance we should be able to derive the following *) 
Instance decOptbstSizeMonotonic m n t : DecOptSizeMonotonic (bst m n t).
Proof. derive_mon (). Qed.
                       
Instance DecOptbst_sound m n t : DecOptSoundPos (bst m n t).
Proof. derive_sound (). Qed.

Instance DecOptbst_complete m n t : DecOptCompletePos (bst m n t).
Proof. derive_complete (). Qed.

Derive ArbitrarySizedSuchThat for (fun b => bst min max b).


Conjecture expand_range : forall t,
    bst 0 30 t ->
    bst 0 40 t.
QuickChick expand_range.
Conjecture contract_range : forall t,
    bst 0 30 t ->
    bst 0 1 t.
QuickChick expand_range.
(* this shouldn't work *)

Fixpoint insert t x :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node a l r =>
    if a <= x ? then
      Node x (insert l x) r
    else
      Node x r (insert r x)
  end.


Inductive inrange : nat -> nat -> tree -> nat -> Prop :=
| InRange : forall t n max x,
    le n max ->
    bst 0 max t ->
    le x max ->
    inrange n max t x.
Derive DecOpt for (inrange n m t x).
Derive ArbitrarySizedSuchThat for (fun n => inrange n m t x).


(* Testing here doesn't work *)
(* Conjecture insert_invariant : *)
(*   forall t, *)
(*     inrange 30 30 t 30 -> *)
(*     bst 0 30 t. *)
(* QuickChick insert_invariant. *)


