(** * Automation Tutorial for QuickChick *)

(** This tutorial explores the automation capabilities of 
    QuickChick, leveraging typeclasses and plugin magic. *)

From QuickChick Require Import QuickChick.

(* Let's revisit our favorite datatype, binary trees: *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(* Instead of writing a generator, shrinker, and printer for trees, we
   could simply derive them using the `Derive` command. 

   This command takes two parameters:
   - the name (or names) of the typeclass to be derived 
   - the datatype to derive it for
 *)

Derive (Arbitrary, Show) for Tree.
(* ==> 
GenSizedTree is defined
ShrinkTree is defined 
ShowTree is defined 
*)

(* To decide propositions, QuickChick provides the convenient
   `Dec` typeclass. This is a thin wrapper around ssreflects
   decidable definition, which in itself is just a 
   proof that P holds or does not hold.
*)

From mathcomp Require Import ssrbool.
Check decidable.
(* ==> 
fun P : Prop => {P} + {~ P}
*)

Module DecPlayground.
  (* The Dec class provides the dec method which gives
     a decidability witness for P *)
  Class Dec (P : Prop) : Type := { dec : decidable P }.

  (* The DecOpt class encodes partial decidability: 
     - It takes a nat argument as fuel
     - It returns None, if it can't decide.
     - It returns Some true/Some false if it can.
     - These are supposed to be monotonic, in the 
       sense that if they ever return Some b for 
       some fuel, they will also do so for higher 
       fuel values.
   *)
  Class DecOpt (P : Prop) := { decOpt : nat -> option bool }.

  (* Every Dec instance naturally gives rise to an 
     instance of DecOpt *)

  (* QuickChick also provides convenient notation 
     for accessing these instances: *)

  Notation "P '?'" := (match (@dec P _) with
                       | left _ => true
                       | right _ => false
                     end) (at level 100).
  
  Notation "P '??' n" := (@decOpt P _ n) (at level 100).

  (* The most common use of the Dec class is boolean equality
     testing. That is the purpose of the Dec_Eq typeclass.  *)
  
  Class Dec_Eq (A : Type) := { dec_eq : forall (x y : A), decidable (x =
     y) }.
  
End DecPlayground.

(* For the Dec_Eq class in particular, QuickChick provides a useful
tactic for using the Coq-provided `decide equality` tactic in
conjunction with existing Dec_Eq instances, to automate its
construction. For example, for our Tree example we can invoke `dec_eq`, assuming our type A is also testable for equality --- note the "Defined" to close the proof.
 *)
Instance Dec_Eq_Tree {A} `{Dec_Eq A} : Dec_Eq (Tree A).
Proof. dec_eq. Defined.


(* Armed with all these instances, we can now automatically test
   properties of trees. For example, in the BasicUsage tutorial we saw
   a `mirror` function: *)

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
  | Leaf => Leaf
  | Node x l r => Node x (mirror r) (mirror l)
  end.

(* Along with a faulty mirror property, specialized 
to nat for simpler testing: *)
Definition faulty_mirrorP (t : Tree nat) :=
  mirror t = t?.

QuickChick faulty_mirrorP.

(* Preconditions + Automation *)
(* ========================== *)

(* Another very common occurrence in Coq is to have 
   complex inductive definitions that both constrain
   the inputs of theorems, and are used in the conclusion. 
   
   For a complete example, we refer the user to the 
   stlc tutorial. For here, let's consider the simpler
   case of balanced trees of height `n`, where every path 
   through the tree has length either `n` or `n-1`.
 *)

Inductive balanced {A} : nat -> Tree A -> Prop :=
| B0 : balanced 0 Leaf
| B1 : balanced 1 Leaf
| BS : forall n x l r,
    balanced n l -> balanced n r ->
    balanced (S n) (Node x l r).

(* When implementing a data structure such as AVL trees, we would
   ensure that a balanced tree remains balanced after inserting an
   element with intricate rebalancing operations. 

   Here, let's encode a very naive insertion function that always inserts elements on the
   leftmost path, and see how QuickChick can figure out when things go wrong:
 *)

Fixpoint insert {A} (x : A) (t : Tree A) : Tree A :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node y l r => Node y (insert x l) r
  end.

(* To check if a tree t is balanced, we need a _computable_ way of 
   deciding whether there exists a height n for which `balanced n t` 
   holds. Inductives in Coq don't provide that capability, and most
   often users resort to writing a separate piece of code that 
   performs this computation, usually along with a proof that 
   it does so correctly. 

   However, QuickChick provides a derivation mechanism that allows for 
   extracting such computational content from an inductive relation
   over simply-typed first-order data, levering the typeclass 
   infrastructure we've seen! *)

Derive DecOpt for (balanced n t).
(* ==> DecOptbalanced is defined *)

(* This Derive command produces an instance of the DecOpt typeclass for 
   the proposition `Balanced n t` for arbitrary parameters n and t. *)

Check DecOptbalanced.
(* ==>
  DecOptbalanced
     : forall (n_ : nat) (t_ : Tree ?A), DecOpt (balanced n_ t_)
*)

(* We can use this to check whether a given tree is balanced at a given height *)
Eval compute in (balanced 1 (Node 42 Leaf Leaf) ?? 10).
(* ==> Some true *)
Eval compute in (balanced 2 Leaf ?? 10).
(* ==> Some false *)
Eval compute in (balanced 3 (Node 42 (Node 10 Leaf Leaf) (Node 10 Leaf Leaf)) ?? 1).
(* ==> None *)

(* For QuickChick-derived instances of DecOpt, you can assume that `decOpt` functions are:
   - Monotonic: If they return a `Some` for some fuel value, they will also return
     the same result for all larger fuel values.
   - Sound: If they return `Some true`, then the inductive relation holds. If they 
     return `Some false`, then the inductive relation doesn't hold.
   - Partially complete: If the inductive relation holds, then there exists a fuel
     value for which they return `Some true`. Unfortunately, the decision procedures 
     are incomplete in the case where the inductive relation doesn't hold, as it 
     might encode nonterminating computations. 

   Proofs of these laws can also be obtained automatically for derived instances!
   For more information, check out the PLDI paper: "Computing Correctly with Inductive
   Relations". *)

(* In the first case, a single node tree is balanced at height 1. In the second, 
   a Leaf is balanced but not at height 2. In the third case, we didn't provide 
   enough fuel for the checker to decide conclusively one way or another. *)

(* So let's try to check our first (obviously false) property using derived 
   checkers: all trees (of natural numbers) are balanced. *)

Definition all_trees_are_balanced (n : nat) (t : Tree nat) := 
  balanced n t ?? 10.

QuickChick all_trees_are_balanced.
(* ==> 
   0
   (Node 0 Leaf Leaf)
   Failed after 5 tests and 11 shrinks.
*)
(* Sure enough, not all trees are balanced. But how would we go about generating 
   balanced trees for testing purposes? Another `Derive` command to the rescue! *)

Derive GenSizedSuchThat for (fun t => balanced n t).
(* ==> GenSizedSuchThatbalanced is defined *)

(* This Derive command produces an instance of the GenSizedSuchThat typeclass,
   which produces trees t such that t is balanced---for a given input argument
   n. That is, the anonymous function arguments set what the argument to generate
   for is, and the rest of the names are assumed to be universally quantified. *)

Check GenSizedSuchThatbalanced.
(* ==> 
   GenSizedSuchThatbalanced
     : forall n_ : nat,
       GenSizedSuchThat (Tree ?A) (fun t_ : Tree ?A => balanced n_ t_)
 *)

(* But what is GenSizedSuchThat? *)
Print GenSizedSuchThat.
(* ==> 
  Record GenSizedSuchThat (A : Type) (P : A -> Prop) : Type := Build_GenSizedSuchThat
     { arbitrarySizeST : nat -> G (option A) }.
 *)

(* It's a typeclass with a single method, given an (inductive) predicate P over some 
   type A, it (maybe) produces instances of A given some fuel. For the QuickChick-derived
   instances you can once again assume:
   - Monotonicity on fuel
   - Soundness (will only produce As satisfying P) 
   - Completeness (all As satisfying P can be produced)

   Proofs of these can again be obtained automatically.

   Finally, QuickChick provides a convenient notation, `genSizedST` to invoke 
   arbitrarySizeST, and `genST` to invoke it with the QuickChick-managed 
   size parameter.
 *)
Sample (genST (fun t => balanced 1 t)).
(*==> 
  QuickChecking (genST (fun t => balanced 1 t))
  [ Some Leaf
  ; Some Leaf
  ; Some Node 5 Leaf Leaf
  ; Some Node 4 Leaf Leaf
  ; Some Node 1 Leaf Leaf
  ; Some Node 5 Leaf Leaf
  ; Some Node 2 Leaf Leaf
  ; Some Leaf
  ; Some Node 0 Leaf Leaf
  ; Some Node 0 Leaf Leaf
  ; Some Leaf]

  You'll note that the generator produced both Leafs and single-Node trees,
  as both are balanced at height 1 according to our inductive definition. *)

(* Now we can use this generator and the checker above, to sanity check that 
   QuickChick has done the right thing: *)

Definition prop_gen_balanced_is_balanced :=
  let fuel := 10 in
  (* Generate an arbitrary n *)
  forAll (choose (0,5)) (fun (n : nat) =>
  (* Generate an arbitrary balanced tree of height n *)
  forAllMaybe (genSizedST (fun t => balanced n t) fuel) (fun (t : Tree nat) => 
  (* Check the resulting tree is balanced. *)
  balanced n t ?? fuel)).

QuickChick prop_gen_balanced_is_balanced.
(* ==>
   QuickChecking gen_balanced_is_balanced
   +++ Passed 10000 tests (0 discards)
*)

(* Perfect! Now let's try to write - and test - the property that insertion 
   preserves balanced. We will use the '==>?' combinator which combines two
   option bools, treating failures in the precondition as a `None` - a 
   discarded test.
*)
Definition balanced_preserves_balanced (fuel n x : nat) (t : Tree nat) :=
  (balanced n t ?? fuel) ==>? (balanced n (insert x t) ?? fuel).

(* We could try to test this property with the type based generators, for some height e.g. 5:
*)
QuickChick (balanced_preserves_balanced 10 5).

(* ==>
  QuickChecking (balanced_preserves_balanced 10 5)
  *** Gave up! Passed only 0 tests
  Discarded: 20000
*)

(* Naturally, no balanced trees of height 5 could even be generated!

   However, we could use the derived constrained generators instead: *)

Definition prop_balanced_preserves_balanced (n : nat) :=
  let fuel := 10 in
  (* Generate an arbitrary balanced tree of height n *)
  forAllMaybe (genSizedST (fun t => balanced n t) fuel) (fun (t : Tree nat) =>
  (* Generate an arbitrary integer x to insert *)
  forAll (choose (0,10)) (fun x =>                  
  balanced_preserves_balanced fuel n x t)).                                                       
QuickChick (prop_balanced_preserves_balanced 5).
(* ==>
QuickChecking prop_balanced_preserves_balanced
Node 4 (Node 0 (Node 5 (Node 3 (Node 4 Leaf Leaf) (Node 0 Leaf Leaf)) (Node 1 Leaf Leaf)) (Node 0 (Node 5 (Node 5 Leaf Leaf) Leaf) (Node 2 Leaf Leaf))) (Node 0 (Node 2 (Node 1 Leaf Leaf) (Node 0 Leaf (Node 0 Leaf Leaf))) (Node 0 (Node 3 Leaf (Node 5 Leaf Leaf)) (Node 1 (Node 4 Leaf Leaf) (Node 2 Leaf Leaf))))
7
*** Failed after 6 tests and 0 shrinks. (0 discards)
*)

(* We immediately get a balanced tree of height 5 that invalidates the property! *)

