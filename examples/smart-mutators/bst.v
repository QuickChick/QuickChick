From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Sized, Show) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive DecOpt for (le x y).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun x => le x y).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive DecOpt for (bst lo hi t).

Definition genBetween lo hi: G (option nat) :=
  if (lo <= hi)?
    then
      bindGenOpt (genST (fun x => le x (hi - lo))) (fun x => 
      ret (Some (x + lo)))
    else ret None.

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo <= x /\ x <= hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

Fixpoint maxNode x t: nat :=
  match t with 
  | Leaf => x
  | Node y l r => maxNode y r
  end.

Fixpoint minNode x t: nat :=
  match t with 
  | Leaf => x
  | Node y l r => minNode y l
  end.

(* How much to weight branches, as a function of their size *)
Definition mut_bst_branch_weighting (n: nat): nat := 2 * n.

Fixpoint mut_bst (lo hi: nat) (t: Tree) : G (option Tree) :=
  let n := size t in 
  (* preserves size *)
  let mut_here: G (option Tree) :=
        @arbitrarySizeST _ (fun t => bst lo hi t) _ n in
  match t return G (option Tree) with
  | Leaf => mut_here 
  | Node x l r =>
    backtrack
      [ (* here *)
        ( 1 , mut_here )
      ; (* x *)
        ( 1
        (* specialized *)
        (* , bindGenOpt (genBetween (maxNode lo l) (minNode hi r)) (fun x' => *)
        (* generalized *)
        , bindGenOpt
            (backtrack [
              ( 1
              , bindGenOpt (genST (fun x => lo <= x)) (fun x' =>
                  if
                    (andb ((x' <= hi)?)
                    (andb (is_bst lo x' l)
                          (is_bst x' hi r)))
                  then ret (Some x)
                  else ret None)
              )
            ])
            (fun x' => ret (Some (Node x' l r)))
        )
      ; (* l *)
        ( mut_bst_branch_weighting (size l)
        , bindGenOpt (mut_bst lo x l) (fun l' => 
          ret (Some (Node x l' r)))
        )
      ; (* r *)
        ( mut_bst_branch_weighting (size r)
        , bindGenOpt (mut_bst x hi r) (fun r' => 
          ret (Some (Node x l r')))
        )
      ]
  end.    

Definition mut_preserves_bst :=
  forAll (arbitrary: G nat) (fun hi =>
  forAllMaybe (genST (fun lo => lo <= hi)) (fun lo =>
  forAllMaybe (@arbitraryST _ (fun t => bst lo hi t) _) (fun t =>
  forAllMaybe (mut_bst lo hi t) (fun t' =>
  ret (is_bst lo hi t')
  )))).

QuickChick mut_preserves_bst.

Sample (mut_bst 0 100 (Node 50 (Node 25 Leaf Leaf) (Node 75 Leaf Leaf))).