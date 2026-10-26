From QuickChick Require Import QuickChick.

(* A premise that is a quantified statement has no producer or checker to
   schedule; deriving reports it as a user error instead of an anomaly. *)

Inductive all_below : nat -> Prop :=
| AllBelow n : (forall m, m <= n) -> all_below n.

Fail QCDerive Generator for (fun n => all_below n).
