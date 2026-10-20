From QuickChick Require Import QuickChick.
QuickChickDebug Debug On.

Inductive asym_a : nat -> Prop :=
| AsymA0 : asym_a 0
| AsymAS : forall n, asym_b n -> asym_a (S n)
with asym_b : nat -> Prop :=
| AsymBFromA : forall n, asym_a n -> asym_b n.

Derive Inductive Schedule asym_b 0 derive "Gen" opt "true".
