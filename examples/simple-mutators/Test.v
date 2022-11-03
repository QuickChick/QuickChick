From QuickChick Require Import QuickChick.
Import MonadNotation.
Require Import List.
Import ListNotations.

(* QuickChickDebug Debug On. *)

(* bool *)

Derive (Show, Sized, Arbitrary) for bool.
Derive Mutate for bool.

Sample (mutate true).

(* nat *)

Derive (Show, Sized, Arbitrary) for nat.
Derive Mutate for nat.

Sample (mutate 100).

(* List Nat *)

(* Inductive L : Set :=
  | Nil : L
  | Cons : nat -> L -> L.

Derive (Show, Sized, Arbitrary) for L.
Derive Mutate for L.

Sample (mutate Nil).
Sample (mutate (Cons 1 (Cons 2 Nil))). *)

(* Tree Nat *)

(* Inductive T : Set :=
  | Leaf : T
  | Node : nat -> T -> T -> T.

Derive (Show, Sized, Arbitrary, Mutate) for T.

Sample (mutate Leaf).
Sample (mutate (Node 100 (Node 200 Leaf Leaf) (Node 300 Leaf Leaf))). *)

(* from RedBlackTree/Impl.v *)

Require Import ZArith.

Derive (Arbitrary, Sized, Show, Mutate) for positive.
Derive (Arbitrary, Sized, Show, Mutate) for Z.

Inductive Color := R | B.
Derive (Arbitrary, Sized, Show, Mutate) for Color.

Inductive Tree :=
    | E : Tree
    | T : Color -> Tree -> Z -> Z -> Tree -> Tree.

Derive (Arbitrary, Sized, Show, Mutate) for Tree.

(* Option *)

Derive (Show, Arbitrary, Sized, Mutate) for option.

Sample (mutate (None : option nat)).
Sample (mutate (Some 100: option nat)).

(* list *)

Derive (Show, Arbitrary, Sized, Mutate) for list.

Sample (mutate [100]).
Sample (mutate [100; 200; 300; 400]).

(* tree *)

Print list.

Inductive tree (A : Type) : Type :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A}.

(* TODO: all of these derives give this error
The constructor leaf (in type tree) is expected to be applied to 1 argument 
while it is actually applied to no arguments.

Something wierd is wrong at bottom of deriving... special to QC2? This wasn't 
broken before for sure.
*)
(* Derive (Show, Arbitrary, Sized, Mutate) for tree. *)
(* Derive Show for tree. *)
(* Derive Arbitrary for tree. *)
(* Derive Sized for tree. *)
(* Derive Mutate for tree. *)