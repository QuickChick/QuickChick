(* An equality check compiles to a Dec_Eq instance, so without one the check
   is unavailable: the checker for same cannot be derived, and no theorem
   schedule checks same x y. Every remaining schedule runs; before, the best
   one checked same and failed to compile. *)
From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".
Inductive opaque := Opaque : nat -> opaque.
QuickChick Derive (Arbitrary, Show) for opaque.
Inductive wrapped : opaque -> Prop := Wrapped : forall n, wrapped (Opaque n).
Inductive same : opaque -> opaque -> Prop := Same : forall x, same x x.
Definition unwrap (o : opaque) := match o with Opaque n => n end.
Fail QuickChick Derive Checker for (same x y).
Goal forall x y, wrapped x -> wrapped y -> same x y -> unwrap x = unwrap y.
  quickchick_schedules.
  quickchick 2 0.
  quickchick 2 1.
  quickchick 2 2.
  Fail quickchick 2 3.
Abort.
