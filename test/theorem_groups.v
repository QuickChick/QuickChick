From QuickChick Require Import QuickChick.

(* The hypotheses share no variables, so theorem testing searches them as
   separate groups and keeps only the combinations that can reach the best
   score. Schedule indices range over those combinations. *)
Theorem bounded_sum : forall x y : nat, x <= 3 -> y <= 3 -> x + y <= 6.
Proof.
  quickchick.
  (* Both orders of the two generators score equally; only one is kept. *)
  Fail quickchick 10 1.
Admitted.
