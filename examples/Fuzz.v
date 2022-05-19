From QuickChick Require Import QuickChick.
Import MonadNotation.
Require Import Arith.

Definition test_prop (n : nat) := Some (n <=? 10).

Definition gen : G nat := choose (0,5).

Definition fuzz (n : nat) : G nat :=
  x <- choose (1,3);;
  ret (n + x).

Definition fuzzer := fuzzLoop gen fuzz show test_prop.

QuickChickDebug Debug On.
FuzzChick test_prop fuzzer.
