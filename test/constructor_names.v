From QuickChick Require Import QuickChick.

(* Derived code names a constructor by its shortest name, so that a later
   global with the same base name, here a definition Bool, does not capture
   it. Show still prints the constructor's own name. *)
Module Z.
  Inductive base := Int | Bool | Unit.
End Z.
Import Z.
Definition Bool := 3.

QuickChick Derive (Arbitrary, Show) for base.

Example shows : (show Z.Bool, show Int) = ("Bool"%string, "Int"%string).
Proof. reflexivity. Qed.
