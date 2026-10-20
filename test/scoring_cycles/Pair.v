From QuickChick Require Import QuickChick.
QuickChickDebug Debug On.

Inductive asym_a : nat -> Prop :=
| AsymA0 : asym_a 0
| AsymAS : forall n, asym_b n -> asym_a (S n)
with asym_b : nat -> Prop :=
| AsymBFromA : forall n, asym_a n -> asym_b n.

Inductive asym_pair : nat -> nat -> Prop :=
| AsymPair : forall m z, asym_a m -> asym_b z -> asym_pair m z.

Derive Inductive Schedule asym_pair 0 1 derive "Gen" opt "true".
