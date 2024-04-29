From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.
Set Warnings "-extraction".

Definition my_prop :=
  (fun (x : nat) =>
     tyche "my_prop" (show x) (Nat.leb x 5)).

QuickChick my_prop.

