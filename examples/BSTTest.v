From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree.

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x -> le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive DecOpt for (bst lo hi t).

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo < x /\ x < hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

Definition bst_checker_prop :=
  forAll (genST (fun t => bst 2 7 t))
         (fun mt =>
            match mt with
            | Some t => 
              (@decOpt (bst 2 7 t) _ 40 = Some (is_bst 2 7 t))?
            | _ => false
            end).

(*! QuickChick bst_checker_prop. *)



