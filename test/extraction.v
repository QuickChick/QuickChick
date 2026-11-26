From QuickChick Require Import QuickChick.
From Coq Require Import Arith ZArith.

Extract Constant defNumTests    => "1".

(* Make sure max extracts correctly *)
QuickChick (Nat.eqb (Nat.max 0 1) 1).

(* Test extraction of Hexadecimal.int and Number.int (#443) *)
QuickChick (Z.eqb (Z.of_hex_int (Z.to_hex_int 1)) 1).
QuickChick (Z.eqb (Z.of_num_int (Z.to_num_int 1)) 1).

(* Test extraction of Nat.sub (#442) *)
QuickChick (Nat.eqb (Nat.sub 0 1) 0).

(* Test extraction of randomR with large ranges *)
QuickChick (
  forAll (choose (0%N, N.pow 2 120)) (fun _ =>
  forAll (choose (0%Z, Z.pow 2 120)) (fun _ => true))).
