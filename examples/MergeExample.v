From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Inductive bal : nat -> Tree -> Prop :=
| bal_leaf0 : bal 0 Leaf
| bal_leaf1 : bal 1 Leaf
| bal_node : forall n t1 t2 m,
    bal n t1 -> bal n t2 -> bal (S n) (Node m t1 t2).

QuickChickDebug Debug On.
Merge (fun t => bst lo hi t) With (fun t => bal n t)
      As bstbalmerged.

Inductive bstbal : nat -> nat -> nat -> Tree -> Prop :=
| leafleaf0 : forall lo hi, bstbal lo hi 0 Leaf
| leafleaf1 : forall lo hi, bstbal lo hi 1 Leaf
| nodenode : forall lo hi n x l r,
    le (S lo) x -> le (S x) hi ->
    bstbal lo hi n l -> bstbal x hi n r -> bstbal lo hi (S n) (Node x l r).

Derive ArbitrarySizedSuchThat for (fun t => bal n t).
Derive DecOpt for (bal n t).
Derive EnumSizedSuchThat for (fun n => bal n t).

Definition Empty {A} (e : E A) (n : nat) : bool :=
  match (Enumerators.run e n) with
  | LazyList.lnil => false
  | LazyList.lcons _ _ => true
  end.

Derive DecOpt for (le x y).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive ArbitrarySizedSuchThat for (fun t => bstbal a b c t).

Sample (@arbitrarySizeST _ (fun t => bst 0 10 t) _ 5).

Print GenSizedSuchThatbst.

Sample (genST (fun t => bst 0 10 t)).

Derive DecOpt for (bst lo hi t).

Check @decOpt.
Check GenSizedSuchThatbst.
 
Compute (@decOpt (bal 0 Leaf) _ 5).

Definition balBst_any_test :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 10 t) _ 5)
              (fun t => if Empty (@enumSizeST _ (fun n => bal n t) _ 10) 10
              then (checker true) else (checker tt)).

QuickChick balBst_any_test.

Definition balBst_merged :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bstbal 0 10 2 t) _ 5)
              (fun t => checker true).

QuickChick balBst_merged.

(*An issue is that these two aren't really comparing the same thing.
Ideally, we should generate trees for which all three parameters can be
anything.*)
