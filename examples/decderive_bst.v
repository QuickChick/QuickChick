From Coq Require Import Init.Nat.
From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.
Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.

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
Derive DecOpt for (bst min max t).
Derive ArbitrarySizedSuchThat for (fun b => bst min max b).

Compute (sample (@arbitrarySizeST _ (fun t => bst 0 30 t) _ 10)).

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
