From QuickChick Require Import QuickChick.

Inductive Tree (A : Type) :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Derive (Arbitrary, Show) for Tree.

Inductive GoodTree {A} : Tree A -> Prop :=
| GoodLeaf : GoodTree Leaf
| GoodNode : forall x l r,
    GoodTree l -> GoodTree r -> GoodTree (Node x l r).

Require Import List. Import ListNotations.
Import MonadNotation.
Import BindOptNotation.

Fixpoint genGoodTree (s : nat) {A} `{GenSized A}
  : G (option (Tree A)) :=
  match s with
  | O => ret (Some Leaf)
  | S s' =>
      backtrack [ (1, ret (Some Leaf))
                ; (1, x <- arbitrarySized s';;
                      l <-- genGoodTree s';;
                      r <-- genGoodTree s';;
                      ret (Some (Node x l r)))]
  end.
          
