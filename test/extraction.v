From QuickChick Require Import QuickChick.
From Coq Require Import Arith.

Extract Constant defNumTests    => "1".

(* Make sure max extracts correctly *)
QuickChick (Nat.eqb (Nat.max 0 1) 1).
