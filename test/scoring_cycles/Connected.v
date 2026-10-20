From QuickChick Require Import QuickChick.
QuickChickDebug Debug On.

Inductive asym_a : nat -> Prop :=
| AsymA0 : asym_a 0
| AsymAS : forall n, asym_b n -> asym_a (S n)
with asym_b : nat -> Prop :=
| AsymBFromA : forall n, asym_a n -> asym_b n.

Inductive asym_c : nat -> nat -> Prop :=
| AsymC : forall z a n, asym_b n -> asym_c z a.

Inductive asym_root : nat -> nat -> nat -> Prop :=
| AsymRoot : forall a m z,
    asym_a m -> asym_b z -> asym_c z a -> asym_root a m z.

Derive Inductive Schedule asym_root 0 1 2 derive "Gen" opt "true".
