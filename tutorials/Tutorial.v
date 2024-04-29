(** * Tutorial/Demo for QuickChick *)

(** QuickChick started out as a clone of Haskell's QuickCheck, 
    and is being fed steroids ever since. This tutorial 
    explores basic aspects of random property-based testing
    and details the majority of features of QuickChick. *)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.

(** ** Introduction *)
     
(** It is not uncommon during a verification effort to spend many
    hours attempting to prove a slightly false theorem, only to result
    in frustration when the mistake is realized and one needs to start
    over. Other theorem provers have testing tools to quickly raise
    one's confidence before embarking on the body of the proof;
    Isabelle has its own QuickCheck clone, as well as Nitpick,
    Sledgehammer and a variety of other tools; ACL2 has gone a step
    further using random testing to facilitate its
    automation. QuickChick is meant to fill this void for Coq.


    Consider the following short function [remove] that takes a
    natural number [x] and a list of nats [l] and proceeds to remove
    [x] from the list. While one might be tempted to pose the question
    "Is there a bug in this definition?", such a question has little
    meaning without an explicit specification. Here, [removeP]
    requires that after removing [x] from [l], the resulting list does
    not contain any occurences of [x]. *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if Nat.eqb h x then t else h :: remove x t
  end.

Definition removeP (x : nat) (l : list nat) : bool := 
  negb (existsb (fun y => x =? y) (remove x l)).

(** For this simple example, it is not hard to "spot" the bug by
    inspection. We will use QuickChick to find out what is wrong.

    QuickChick provides a toplevel command [QuickChick] that receives
    as input an executable property and attempts to falsify it. *)

QuickChick removeP.

(** Internally, the code is extracted to OCaml, compiled, and run.  The
    following output is presented in your terminal, CoqIDE [Messages] 
    pane, or Visual Studio Code [Info] pulldown menu tab:
<<
    0

    [0; 0]

    Failed! After 17 tests and 12 shrinks
>>
    The output signifies that if we use an input where [x] is [0] and
    [l] is the two element list containing two zeros, then our
    property fails. Indeed, we can now identify that the [then] branch
    of [remove] fails to make a recursive call, which means that only
    one occurence of each element will be deleted. The last line of
    the output states that it took 17 tests to identify some fault
    inducing input and 12 shrinks to reduce it to a minimal
    counterexample.

    Before we begin to explain exactly how QuickChick magically comes
    up with this result, it is important to point out the first (and
    arguably most important) limitation of this tool: it requires an
    *executable* specification. QuickChick needs to be able to "run" a
    property and decide whether it is true or not; a definition like
    [remove_spec] can't be QuickChecked! *)

Definition remove_spec :=
  forall x l, ~ In x (remove x l).

(** QuickChick requires either a functional spec (like [removeP]) or a
    decidability procedure for an inductive spec. *)

(** ** Property Based Random Testing Ingredients 

    There are four basic ingredients in property based random testing:

    - An executable property, as discussed above
    - A printer, to report counterexamples found
    - A generator, to produce random inputs 
    - A shrinker, to reduce counterexamples.

*)

(** *** Printing 

    For printing, QuickChick uses a [Show] typeclass, like Haskell. *)

Print Show.

(**  ==> Record Show (A : Type) : Type 
            := Build_Show { show : A -> String.string }   *)

(** The [Show] typeclass contains a single function [show] from some
    type [A] to Coq's [string]. QuickChick provides default instances
    for [string]s (the identity function), [nat], [bool], [Z],
    etc. (via extraction to appropriate OCaml functions for
    efficiency), as well as some common compound datatypes: lists,
    pairs and options.

    Writing your own show instance is easy! Let's define a simple
    [Color] datatype. *)

Inductive Color := Red | Green | Blue | Yellow.

(** After ensuring we have opened the [string] scope, we can declare
    an instance of [Show Color] by encoding [show] as a simple pattern
    matching on colors. *)

Require Import String. Open Scope string.
#[global]
Instance show_color : Show Color :=
  {| show c :=
       match c with
         | Red    => "Red"
         | Green  => "Green"
         | Blue   => "Blue"
         | Yellow => "Yellow"
       end
  |}.

(** You can safely ignore the "#[global]" annotation for now, it 
    signifies that this instance should be exported along with this 
    module. *)

Eval compute in (show Green).
(** ==> "Green" : string *)

(** While writing show instances is relatively straightforward, it can
    get tedious.  The QuickChick provides a lot of automation, in the 
    form of automatically derived typeclass instances: *)

Derive Show for Color.
(** => ShowColor is defined *)
Print ShowColor.

(** *** Generators *)

(** **** The [G] Monad *)

(** The heart of property based random testing is the random
    generation of inputs.  In QuickChick, a generator for elements of
    some type [A] is a monadic object with type [G A]. The monad [G]
    serves as an abstraction over random seed plumbing. Consider
    writing a program that given a random seed generates many
    integers: one needs to use the given seed to produce an integer
    while at the same time obtain a new, altered seed to use for
    future draws. This [State]-monad like behavior is hidden behind
    [G].

    Standard monadic functions have the [Gen] suffix. *)

Check bindGen.
(** ==> bindGen : G ?A -> (?A -> G ?B) -> G ?B *) 

Check returnGen.
(** ==> returnGen : ?A -> G ?A *)

(** For those familiar with Haskell's monadic interface, QuickChick
    also provides variants of [liftM] (as [liftGen]) with arities 1 to
    5, [sequence] (as [sequenceGen]) and [foldM] (as [foldGen]). *)

(** Using this abstraction and a few primitives for sampling numbers
    in a given range, QuickChick users can write their own custom
    generator to generate any datatype. However, that can become _very_
    tedious quickly. So QuickChick provides automatic derivation for
    that as well.
 *)

Print GenSized.
(** ==> 
Record GenSized (A : Type): Type := 
  Build_GenSized { arbitrarySized : nat -> G A }.
*) 

(** The GenSized typeclass characterizes types that admit a fuel-based
  generator (to allow for generation of recursive types). *)

Derive GenSized for Color.
(** ==> GenSizedColor is defined *)

Print GenSizedColor.

(* For a more compelling example, let's turn to our favorite datatype,
binary trees: *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(* Instead of writing a generator, shrinker, and printer 
   for trees, we
   could simply derive them using the `Derive` command. 

   This command takes two parameters:
   - the name (or names) of the typeclass to be derived 
   - the datatype to derive it for
 *)

Derive (GenSized, Show) for Tree.
(* ==> 
GenSizedTree is defined
ShowTree is defined 
*)
Print ShowTree.
Print GenSizedTree.


(** To showcase this generator, we will use the notion of mirroring a
    tree: swapping its left and right subtrees recursively. *)
   
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror r) (mirror l)
  end.

(** We also need a simple structural equality on trees *)
Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      Nat.eqb x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.

(** One expects that [mirror] should be unipotent; mirroring a tree
    twice yields the original tree.  *)

Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.

(** To test this assumption, we can use the [forAll] property
    combinator that receives a generator [g] for elements of type [A]
    and an executable property with argument [A] and tests the
    property on random inputs of [g]. *)

QuickChick (forAll (arbitrarySized 5) mirrorP).

(** QuickChick quickly responds that this property passed 10000 tests,
    so we gain some confidence in its truth. But what would happend if
    we had the *wrong* property? *)

Definition faultyMirrorP (t : Tree nat) := eq_tree (mirror t) t.

QuickChick (forAll (arbitrarySized 5) faultyMirrorP).
(** ==> Node (3) (Node (0) (Leaf) (Node (0) (Node (1) (Leaf) (Leaf)) (Leaf)))
(Node (5) (Node (0) (Node (1) (Leaf) (Node (4) (Leaf) (Leaf))) (Node (4) (Leaf)
(Node (0) (Leaf) (Leaf)))) (Node (5) (Node (4) (Node (0) (Leaf) (Leaf)) (Leaf))
(Node (3) (Leaf) (Leaf))))

*** Failed! After 1 tests and 0 shrinks
*)

(** The bug is found immediately and reported. However, is this 
    counterexample really helpful? What is the important part of it? 
    The reported bug is too big and noisy to identify the root cause
    of the problem. That is where _shrinking_ comes in. *)

(** **** Shrinking *)

(** Shrinking, also known as delta debugging, is a greedy process by
    which we can find a smaller counterexample given a relatively
    large one. Given a shrinking function [s] of type [A -> list A]
    and a counterexample [x] of type [A] that is known to falsify some
    property [p], QuickChick (lazily) tries [p] on all members of [s
    x] until it finds another counterexample; then it repeats this
    process.

    This greedy algorithm can only work if all elements of [s x] are
    strictly "smaller" that [x] for all [x]. Most of the time, a
    shrinking function for some type only returns elements that are
    "one step" smaller. For example, consider the default shrinking
    function for lists provided by QuickChick. 

    Just like with printing and generation, QuickChick provides a 
    Shrink typeclass and derivation mechanism:
*)

Print Shrink.
(** ==>
Record Shrink (A : Type) : Type := 
  Build_Shrink { shrink : A -> list A }.
*)

Derive Shrink for Tree.
(** ==> ShrinkTree is defined. *)

Print ShrinkTree.
(** While this is hard to read, it's equivalent to something like 
the following: *)

Open Scope list.
Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : list (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node x' l r) (s x) ++
                    map (fun l' => Node x l' r) (shrinkTree s l) ++
                    map (fun r' => Node x l r') (shrinkTree s r)
  end.

(** That is, we don't shrink [Leaf]s (they're already minimal)
    while for [Node]s we can return the left
    or right subtrees, shrink the payload or one of the subtrees.*)

(** Armed with the shrinker we can revisit the property under test: *)

QuickChick (forAllShrink (arbitrarySized 5) shrink faultyMirrorP).

(** ==> Node (0) (Leaf) (Node (0) (Leaf) (Leaf))

*** Failed! After 1 tests and 8 shrinks *)

(** We now got a much simpler counterexample (in fact, this is one of
    the two minimal ones) and can tell that the real problem occurs
    when the subtrees of a [Node] are different. *)

(** Writing the property above is quite formulaic. In fact, QuickChick
    can use typeclasses to automate that as well! *)

QuickChick faultyMirrorP.

(** But what about propositions? *)

(* To decide propositions, QuickChick provides the convenient
   `Dec` typeclass. This is a thin wrapper around ssreflects
   decidable definition, which in itself is just a 
   proof that P holds or does not hold.
*)

(* Importing ssreflect yields a bunch of "notation overridden" warnings,
   which we can suppress with the following line. *)
Set Warnings "-notation-overridden,-parsing".
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
  
  Class Dec_Eq (A : Type) :=
    { dec_eq : forall (x y : A), decidable (x = y) }.
  
End DecPlayground.

(* For the Dec_Eq class in particular, QuickChick provides a useful
tactic for using the Coq-provided `decide equality` tactic in
conjunction with existing Dec_Eq instances, to automate its
construction. For example, for our Tree example we can invoke `dec_eq`, assuming our type A is also testable for equality --- note the "Defined" to close the proof.
 *)
#[global] Instance Dec_Eq_Tree {A} `{Dec_Eq A} : Dec_Eq (Tree A).
Proof. dec_eq. Defined.


(* Armed with all these instances, we can now automatically test
   properties of trees. For example, in the BasicUsage tutorial we saw
   a `mirror` function: *)

(* Along with a faulty mirror property, specialized 
to nat for simpler testing: *)
Definition faulty_mirrorP (t : Tree nat) :=
  (mirror t = t)?.

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

Derive Checker for (balanced n t).
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

Derive Generator for (fun t => balanced n t).
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

