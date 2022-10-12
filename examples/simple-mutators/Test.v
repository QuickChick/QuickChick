From QuickChick Require Import QuickChick.
Import MonadNotation.

Inductive L : Set :=
  | Nil : L
  | Cons : nat -> L -> L.

QuickChickDebug Debug On.
Derive Arbitrary for L.
(* Derive Fuzzy for L. *)
Derive Mutate for L.
