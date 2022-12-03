From QuickChick Require Import QuickChick.
Import MonadNotation.
Require Import Arith.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

#[local] Instance MutateNat : Mutate nat :=
  {| mutate n := choose (n - 5, n + 5) |}.

#[local] Instance FuzzyNat : Fuzzy nat :=
  {| fuzz n := choose (n - 5, n + 5) |}.

Derive (Arbitrary, Show, Sized, Mutate) for Tree.

QuickChickDebug Debug On.
Derive Fuzzy for Tree.

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive DecOpt for (le x y).

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

Fixpoint insert (x : nat) (t : Tree) :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node y l r =>
    if x < y ? then
      Node y (insert x l) r
    else if x > y ? then
      Node y l (insert x r)
    else t
  end.

Fixpoint mem (x : nat) (t : Tree) :=
  match t with
  | Leaf => false
  | Node y l r =>
      orb (x =? y) (mem x l)
  end.

(*
Definition bst_checker_prop :=
  forAllMaybe (genST (fun t => bst 0 17 t)) (fun t => 
  forAll (choose (1, 16)) (fun x => 
  bst 0 17 (insert x t) ?? 10)). (* *)
(*  is_bst 0 17 (insert x t))). *)

Extract Constant defNumTests => "20000".
QuickChick bst_checker_prop. 
*)

Definition prop (t : Tree) :=
  Some (mem 4 (insert 4 t)).

(*
Definition test_prop (n : nat) := Some (n <=? 10).

Definition gen : G nat := choose (0,5).

Definition fuzz (n : nat) : G nat :=
  x <- choose (1,3);;
  ret (n + x).
 *)

(* QuickChick prop. *)

ManualExtract Tree.
QuickChickDebug Debug On.

Definition fuzzer :=
  fun (u : unit) => fuzzLoop arbitrary mutate show prop.
FuzzChick prop (fuzzer tt).

(* Definition fuzz_fuzzer :=
  fun (u : unit) => fuzzLoop arbitrary fuzz show prop.
FuzzChick prop (fuzz_fuzzer tt). *)
