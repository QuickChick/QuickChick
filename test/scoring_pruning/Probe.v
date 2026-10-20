From QuickChick Require Import QuickChick.

Inductive probe_a : nat -> Prop := ProbeA : forall x, probe_a x.
Inductive probe_b : nat -> nat -> Prop := ProbeB : forall x y, probe_b x y.
Inductive probe_c : nat -> nat -> Prop := ProbeC : forall y z, probe_c y z.

Inductive probe_root : nat -> nat -> nat -> Prop :=
| ProbeRoot : forall x y z,
    probe_a x -> probe_b x y -> probe_c y z -> probe_root x y z.

Derive Inductive Schedule probe_root 0 1 2 derive "Gen" opt "true".
