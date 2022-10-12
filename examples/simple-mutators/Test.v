From QuickChick Require Import QuickChick.
Import MonadNotation.

Inductive L : Set :=
  | Nil : L
  | Cons : nat -> L -> L.

Derive (Show, Arbitrary) for L.
QuickChickDebug Debug On.
Derive Mutate for L.

Check @mutate.
Sample (mutate Nil).
 