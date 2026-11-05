From QuickChick Require Import QuickChick.

(* The commands apply sampleGen, show and quickCheck explicitly, so they
   keep working when users change those constants' implicit arguments
   (issue #351). *)
Definition a : G nat := ret 1.

Arguments QuickChick.Generators.sampleGen : clear implicits.
Arguments QuickChick.Show.show : clear implicits.
Arguments QuickChick.Test.quickCheck : clear implicits.

Sample (liftM Some a).
QuickChick (forAll a (fun n => Nat.eqb n 1)).
