From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

QuickChickDebug Debug On.

(* Derive (Arbitrary, Sized, Fuzzy, Mutate) for nat. *)

(* !TMP base case 0 so i can see how far down mutate recursions go *)
#[global] Instance GenNat : Gen nat := 
    {| arbitrary := choose (0, 10) |}.
Derive (Sized, Fuzzy, Mutate) for nat.

(* Sample (mutate 10). *)
