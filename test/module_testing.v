From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".
Module Outer.
  Module quickchick.
    Inductive flag := On | Off.
    QuickChick Derive (Arbitrary, Show) for flag.
    Sample (arbitrary : G flag).
    QuickChick (fun x : flag => match x with On | Off => true end).
    Goal forall n : nat, n = n.
      quickchick 2.
      pose (saved := theorem).
      QuickChick (saved 3).
      QuickChickWith (updMaxSuccess stdArgs 2) (saved 4).
      intros; reflexivity.
    Qed.
    Fail Check theorem.
  End quickchick.
  QuickCheck true.
End Outer.
Module Type Input.
  Parameter n : nat.
End Input.
Module Deferred (X : Input).
  Definition property := Nat.eqb X.n X.n.
  Fail QuickChick property.
End Deferred.
QuickChick true.

Module Concrete <: Input.
  Definition n := 3.
End Concrete.
Module Applied := Deferred Concrete.
QuickChick Applied.property.
