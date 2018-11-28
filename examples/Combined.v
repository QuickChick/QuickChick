From QuickChick Require Import QuickChick EnumerationQC.

From ExtLib Require Import Monads. Import MonadNotation.


(* QuickChick supports an enumeration testing variant in addition to
   random testing. Thus, it is possible to enumerate all of the test
   cases you might want to consider.

   However, it's even better than that! QuickChick allows you to mix
   and match enumeration testing and random testing, which can make it
   easier to achieve the distributions you want to test.

   This file will go through some basic examples of how to mix
   enumeration testing.
*)



(** Basic Mixed **)

(* gMixed and gRand are both generators for lists of natural numbers.

   gMixed enumerates the length of the list, and randomly chooses the
   elements, giving you equal numbers of test cases with each length
   of list. gRand chooses both the length and elements randomly.
 *)
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


(** Buckets **)

(* When testing you might want to guarantee that you generate values
   in certain buckets. For instance, when randomly generating numbers
   from 0 to 999, you might want to make sure you get a number in
   every group of 10, but you don't care what that number is.
*)
Definition gBuckets : G nat :=
  x <- enumR (0, 900);;
  r <- choose (0, 9);;
  ret (x * 10 + r).

Definition gNoBuckets : G nat :=
  choose(0, 999).

Definition bucket_prop (x : nat) := collect (Nat.div x 10) true.

QuickChick (forAll gBuckets bucket_prop).

(* Get a much less even distributin into buckets, also may need to
   tweek the generator for nats to make large numbers more
   likely. With enumeration it's much more obvious how large your
   numbers can get.
*)
QuickChick (forAll gNoBuckets bucket_prop).
