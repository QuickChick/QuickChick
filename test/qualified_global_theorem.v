From QuickChick Require Import QuickChick.

Definition twice (n : nat) := n + n.

Theorem add_comm_test : forall n m : nat, n + m = m + n.
Proof. quickchick. Admitted.

Theorem twice_test : forall n : nat, twice n = n + n.
Proof. quickchick. Admitted.
