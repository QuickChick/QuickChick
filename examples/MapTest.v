From QuickChick Require Import QuickChick FMapWeakListInstances.

Require Import Coq.Structures.DecidableTypeEx.

Module Map := Make(Nat_as_DT).

Definition prop (m : Map.t nat) (n : nat) : Checker :=
  checker (Map.cardinal m = Map.cardinal (Map.remove n m)?).

QuickChick prop.