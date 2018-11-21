From QuickChick Require Import QuickChick EnumerationQC.

From ExtLib Require Import Monads. Import MonadNotation.

Definition gMixed : G (list nat) :=
  x <- enumR (0, 10);;
  vectorOf x (choose (0,10)).

Definition gRand : G (list nat) :=
  n <- choose (0, 10);;
    vectorOf n (choose (0,10)).

Definition token_prop (x : list nat) := collect (length x) true.

QuickChick (forAll gRand token_prop).
QuickChick (forAll gMixed token_prop).
(* Note: Enumeration counts for total number of tests. *)



