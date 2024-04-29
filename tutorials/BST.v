Require Import Arith Bool List ZArith. Import ListNotations.
From QuickChick Require Import QuickChick. Import QcNotation.

(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

(* ================================================================= *)
(** ** Another Precondition: Binary Search Trees *)

(* Let's revisit once again our favorite datatype, binary trees: *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Derive (Arbitrary, Show) for Tree.
(* ==> 
GenSizedTree is defined
ShrinkTree is defined 
ShowTree is defined 
*)


(** Let's look at another precondition: _binary search trees_.

    The [isBST] predicate characterizes trees with elements between
    [low] and [high]. *)

Fixpoint isBST (low high: nat) (t : Tree nat) := 
  match t with 
  | Leaf => true
  | Node x l r =>
      (low <? x) && (x <? high)
      && (isBST low x l) && (isBST x high r)
  end.

(** Here is a (faulty?) insertion function for binary search trees. *)

Fixpoint insertBST (x : nat) (t : Tree nat) :=
  match t with 
  | Leaf => Node x Leaf Leaf
  | Node x' l r =>
      if x <? x' then Node x' (insertBST x l) r
      else Node x' l (insertBST x r)
  end.

(** We would expect that if we insert an element that is within 
    the bounds [low] and [high] into a binary search tree, then
    the result is also a binary search tree. *)

Check implication.
(* 
     ===> implication : bool -> Checker -> Checker
*)

(**
   The _implication_ function takes a boolean (the precondition) and a
   Checker (the conclusion of the property); if the boolean is true,
   it tests the Checker, otherwise, it rejects the current test. The _==>_ notation is in _Checker_scope_. 

 *)
Open Scope Checker_scope.

Definition insertBST_spec (low high : nat) (x : nat) (t : Tree nat) :=
  (low <? x) ==> 
  (x <? high) ==> 
  (isBST low high t) ==> 
  isBST low high (insertBST x t).                         
(*
QuickChick insertBST_spec.

    

    ===> 
      QuickChecking insertBST_spec
      0
      5
      4
      Node (4) (Leaf) (Leaf)
      *** Failed after 85 tests and 1 shrinks. (1274 discards) 
*)

(** We can see that a bug exists when inserting an element into a
    [Node] with the same payload: if the element already exists in the
    binary search tree, we should not change it. *)
  
(** However we are wasting too much testing effort.  Indeed, if we fix the
    bug ... *)

Fixpoint insertBST' (x : nat) (t : Tree nat) :=
  match t with 
  | Leaf => Node x Leaf Leaf
  | Node x' l r => if x <? x' then Node x' (insertBST' x l) r
                   else if x' <? x then Node x' l (insertBST' x r)
                   else t
  end.

Definition insertBST_spec' (low high : nat) (x : nat) (t : Tree nat) :=
  (low <? x) ==> (x <? high) ==> (isBST low high t) ==> 
  isBST low high (insertBST' x t).                         

(** ... and try again... *)
(*
QuickChick insertBST_spec'.

     ===> 
     QuickChecking insertBST_spec'
     *** Gave up! Passed only 1281 tests
     Discarded: 20000 
*)
(** ... we see that 90%% of tests are being discarded. *)

(** **** Exercise: 4 stars, standard (gen_bst)

    Write a generator that produces binary search trees directly, so
    that you run 10000 tests with 0 discards. *)

Fixpoint genBST (low high size : nat) := 
  match size with 
  | O => ret Leaf
  | S size' => 
    if high - 1 <? low + 1 then ret Leaf
    else freq [ (1, ret Leaf)
              ; (size, x <- choose (low+1, high-1);;
                       l <- genBST low x size';;
                       r <- genBST x high size';;
                       ret (Node x l r)) ]
  end.

Definition bst_checker := 
  forAllShrink arbitrary shrink (fun low =>
  forAll (choose (low+5, low + 10)) (fun high => 
  forAll (choose (low+1, high-1)) (fun x => 
  forAll (genBST low high 5) (fun t => 
  isBST low high (insertBST' x t))))).                                
(*
QuickChick bst_checker.

    [] *)

(* Could we do the same using automation? Sure! 
   Just write a BST inductive! *)

Inductive lt : nat -> nat -> Prop :=
| lt_0 : forall n, lt O (S n)
| lt_S : forall n m, lt n m -> lt (S n) (S m).

Inductive bst : nat -> nat -> Tree nat -> Prop :=
| BST_leaf : forall lo hi, bst lo hi Leaf
| BST_node : forall lo hi x l r,
    lt lo x -> lt x hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

(* And let's try to derive a constrained generator! *)
Fail Derive GenSizedSuchThat for (fun t => bst lo hi t).

(* "Uncaught exception Failure("No Checkers or Producers for relation: lt")." *)

(* Why does it fail? Because to generate a tree that satisfies bst, we
need to do something about the lt relationship that appears inside it. 

Let's derive a checker and try again! *)

Derive DecOpt for (lt n m).
Derive GenSizedSuchThat for (fun t => bst lo hi t).

(* Let's write a convenient shorthand to call it, 
   and test our property! *)
Definition g lo hi n :=
  @arbitrarySizeST _ (fun t => bst lo hi t) _ n.

Definition bst_checker_derived g := 
  forAllShrink arbitrary shrink (fun low =>
  forAll (choose (low+5, low + 10)) (fun high => 
  forAll (choose (low+1, high-1)) (fun x => 
  forAllMaybe (g low high 5) (fun t => 
  isBST low high (insertBST' x t))))).                 

QuickChick (bst_checker_derived g).
(* ===> 
+++ Passed 10000 tests (0 discards)
 *)

(* Perfect! Are we done? Well, let's sample it... *)
Sample (g 0 10 5).
(* ===> 
   [ Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ; Some Leaf
   ]. 

   Something seems to be going wrong... 
   Let's look at the generator - what's the problem?
*)





(* Let's try providing a generator for lt: *)
#[global] Remove Hints GenSizedSuchThatbst : typeclass_instances.

Fail Definition g lo hi n :=
  @arbitrarySizeST _ (fun t => bst lo hi t) _ n.

Derive GenSizedSuchThat for (fun x => lt n x).
Derive GenSizedSuchThat for (fun t => bst lo hi t).

Definition g' lo hi n :=
  @arbitrarySizeST _ (fun t => bst lo hi t) _ n.

Sample (g' 0 10 5).

(* Better, but still, not generating large trees... 
   But how do we quantify that? *)
Fixpoint size (t : Tree nat) : nat :=
  match t with
  | Leaf => 0
  | Node _ l r => 1 + max (size l) (size r)
  end.

Definition bst_checker_collect g := 
  forAllShrink arbitrary shrink (fun low =>
  forAll (choose (low+5, low + 10)) (fun high => 
  forAll (choose (low+1, high-1)) (fun x => 
  forAllMaybe (g low high 5) (fun t => 
  collect (size t)
          (isBST low high (insertBST' x t)))))).

QuickChick (bst_checker_collect g).
QuickChick (bst_checker_collect g').


(* Still not great - it checks whether 'lt x hi' holds! *)
Inductive between : nat -> nat -> nat -> Prop :=
| between_0 : forall n, between O (S n) (S (S n))
| between_S : forall n m o,
    between n m o -> between n m (S o)
| between_SS : forall n m o,
    between n m o -> between (S n) (S m) (S o).

Inductive bst' : nat -> nat -> Tree nat -> Prop :=
| BST_leaf' : forall lo hi, bst' lo hi Leaf
| BST_node' : forall lo hi x l r,
    between lo x hi ->
    bst' lo x l -> bst' x hi r ->
    bst' lo hi (Node x l r).

Derive GenSizedSuchThat for (fun x => between lo x hi).
Derive GenSizedSuchThat for (fun t => bst' lo hi t).

Definition g'' lo hi n :=
  @arbitrarySizeST _ (fun t => bst' lo hi t) _ n.

QuickChick (bst_checker_collect g'').

(* Getting even better! But is it as good as the original? *)

Definition gg lo hi n := liftGen Some (genBST lo hi n).
QuickChick (bst_checker_collect gg).

(* The distributions are still different! *)

#[local] Instance gen_between lo hi :
  GenSizedSuchThat nat (fun x => between lo x hi) :=
  { arbitrarySizeST sz :=
    if lo + 1 >= hi? then
      ret None
    else liftGen Some (choose (lo + 1, hi - 1))
  }. 
#[global] Remove Hints GenSizedSuchThatbetween : typeclass_instances.
QuickChickWeights [(BST_leaf', 1); (BST_node', size)].
Derive GenSizedSuchThat for (fun t => bst' lo hi t).

Definition g3 lo hi n :=
  @arbitrarySizeST _ (fun t => bst' lo hi t) _ n.

QuickChick (bst_checker_collect g3).

