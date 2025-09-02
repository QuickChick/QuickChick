From QuickChick Require Import QuickChick Classes.

Inductive a :=
  | A1 : a
  | A2 : b -> a
with b :=
  | B1 : b
  | B2 : a -> b.

Derive Instance GenSized for a.
Derive Instance EnumSized for a.
Derive Instance Shrink for a.
Derive Instance Arbitrary for a.
Derive Instance Show for a.
