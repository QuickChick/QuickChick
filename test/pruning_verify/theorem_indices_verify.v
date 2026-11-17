(* In verification mode, quickchick n i also ranks every theorem candidate
   and fails if skipping changed the i+1 best. *)
From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".
Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive plus' : nat -> nat -> nat -> Prop :=
| plus_O n : plus' 0 n n
| plus_S n m p : plus' n m p -> plus' (S n) m (S p).
Goal forall a b c d s, le' a b -> le' b c -> plus' a c s -> le' c d -> le' a d.
  quickchick 3 0.
  quickchick 3 2.
  quickchick 3 5.
  quickchick 3 9.
Abort.
