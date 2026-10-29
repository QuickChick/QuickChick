From QuickChick Require Import QuickChick Classes.

Inductive a :=
  | A1 : a
  | A2 : b -> a
with b :=
  | B1 : b
  | B2 : a -> b.

QuickChick Derive GenSized for a.
QuickChick Derive EnumSized for a.
QuickChick Derive Shrink for a.
QuickChick Derive Arbitrary for a.
QuickChick Derive Show for a.
