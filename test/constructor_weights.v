From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* QuickChickWeights sets a constructor's weight in derived generators, as
   it does for the legacy engine. The weight 13 occurs in no other part of
   the generated helpers, so finding it shows the weight was used. *)

Inductive two : nat -> Prop :=
| TwoZero : two 0
| TwoOne : two 1.

QuickChickWeights [(TwoZero, 1); (TwoOne, 13)].

Theorem two_small : forall n, two n -> n <= 1.
Proof.
  quickchick 3.
  match goal with
  | h := ?body |- _ => lazymatch body with context [13] => idtac end
  | _ => fail "the derived generator does not use the registered weight"
  end.
Abort.
