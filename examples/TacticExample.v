Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.

Definition to_be_generated :=
  forAll arbitrary (fun x =>
  forAll arbitrary (fun y =>                      
  if (x = y)? then checker ((x = 0)?)
  else checker tt)).

Theorem foo : forall (x y: nat) , x = y -> x = 0.
Proof.
  quickchick.
