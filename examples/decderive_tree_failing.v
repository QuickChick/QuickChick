From Coq Require Import Init.Nat.
Open Scope nat_scope.
From QuickChick Require Import QuickChick.

Inductive Tree : Type :=
| Leaf
| Node : nat -> Tree -> Tree -> Tree.
Derive Show for Tree.


Inductive ltx : nat -> Tree -> Prop :=
| lt_leaf : forall n, ltx n Leaf
| lt_node : forall n x l r,
                n < x ->
                ltx n l ->
                ltx n r ->
                ltx n (Node x l r).
Derive DecOpt for (ltx n t).

