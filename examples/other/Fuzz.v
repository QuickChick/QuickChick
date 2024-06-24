From QuickChick Require Import QuickChick.
Import MonadNotation.
Require Import Arith.
Require Import List. Import ListNotations.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

#[local] Instance FuzzyNat : Fuzzy nat :=
  {| fuzz n := choose (n - 5, n + 5) |}.

Instance FuzzyPair {A B} `{Fuzzy A} `{Fuzzy B} : Fuzzy (A * B) :=
  {| fuzz p :=
      let '(a,b) := p in
      oneOf_ (ret p) [ thunkGen (fun _ => a' <- fuzz a;; ret (a',b))
                     ; thunkGen (fun _ => b' <- fuzz b;; ret (a,b'))
                     ]
  |}.


Derive (Arbitrary, Show, Sized) for Tree.
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

Definition insert_prop (xt : nat * Tree) :=
  let '(x,t) := xt in 
  is_bst 0 17 t -=> 0 <? x -=> x <? 17 -=> is_bst 0 17 (insert x t).

Definition bst_checker_prop :=
  forAllMaybe (genST (fun t => bst 0 17 t)) (fun t => 
  forAll (choose (1, 16)) (fun x => 
  bst 0 17 (insert x t) ?? 10)). 

QuickChick bst_checker_prop.

QuickChick insert_prop.

ManualExtract Tree.
Definition fuzzer :=
  fun (u : unit) => fuzzLoop arbitrary fuzz show insert_prop.

FuzzChick insert_prop (fuzzer tt).
