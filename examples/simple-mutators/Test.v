From QuickChick Require Import QuickChick.
Import MonadNotation.

(* List *)

Inductive L : Set :=
  | Nil : L
  | Cons : nat -> L -> L.

Derive Mutate for nat.

Derive (Show, Arbitrary) for L.
(* QuickChickDebug Debug On. *)
Derive Mutate for L.

Sample (mutate Nil).
Sample (mutate (Cons 1 (Cons 2 Nil))).

(* Tree *)

Inductive T : Set :=
  | Leaf : T
  | Node : nat -> T -> T -> T.

Derive (Show, Arbitrary, Mutate) for T.

Sample (mutate Leaf).
Sample (mutate (Node 1 (Node 2 Leaf Leaf) (Node 3 Leaf Leaf))).

(* Option *)

Derive (Show, Arbitrary, Mutate) for option.

Sample (mutate (None : option nat)).
Sample (mutate (Some 1: option nat)).