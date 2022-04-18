From QuickChick Require Import QuickChick.
Import QcNotation.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

From ExtLib Require Import Monad.
Import MonadNotation.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree.

Inductive between : nat -> nat -> nat -> Prop :=
| between_n : forall n m, le n m -> between n (S n) (S (S m))
| between_S : forall n m o, between n m o -> between n (S m) (S o).

Derive DecOpt for (le x y).
Derive ArbitrarySizedSuchThat for (fun x => le y x).

QuickChickWeights [(between_n, 1); (between_S, 7)].
Derive ArbitrarySizedSuchThat for (fun x => between lo x hi).
Derive DecOpt for (between lo x hi).

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    between lo x hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).
Derive DecOpt for (bst lo hi t).

Fixpoint gen_bst (s : nat) (lo hi : nat) : G Tree :=
  match s with
  | O => ret Leaf
  | S s' => freq [(1, ret Leaf)
                 ;(if hi - lo < 2? then 0 else s,
                    x <- choose (lo+1, hi-1);;
                    l <- gen_bst s' lo x;;
                    r <- gen_bst s' x hi;;
                    ret (Node x l r))]
  end.

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo < x /\ x < hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

Fixpoint insert (x : nat) (t : Tree) :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node y l r =>
    (*! *)
      if x < y ? then
    (*!! IF-LE-L *)
    (*! if x <= y ? then *)
        Node y (insert x l) r
    (*! *)             
      else if x > y ? then
    (*!! IF-LE-R *)
    (*! else if x >= y ? then *)
        Node y l (insert x r)
      else t
  end.


Extract Constant defNumTests => "100000".

(*! Section base *)

Definition insert_bst :=
  forAll (gen_bst 5 0 10) (fun t =>
  forAll (choose (1, 9)) (fun x => 
  is_bst 0 10 (insert x t))).

(*! QuickChick insert_bst. *)

(*! Section derived-dec *)

Definition insert_bst_derived_checker :=
  forAll (gen_bst 5 0 10) (fun t =>
  forAll (choose (1, 9)) (fun x => 
  bst 0 10 (insert x t) ?? 10)).

(*! QuickChick insert_bst_derived_checker. *)

(*! Section derived-gen *)

Definition insert_bst_derived_gen :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 10 t) _ 5) (fun t =>
  forAll (choose (1, 9)) (fun x => 
  is_bst 0 10 (insert x t))).

(*! QuickChick insert_bst_derived_gen. *)




