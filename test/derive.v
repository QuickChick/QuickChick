From QuickChick Require Import QuickChick Classes.

Inductive a :=
  | A1 : a
  | A2 : b -> a
with b :=
  | B1 : b
  | B2 : a -> b.

Derive GenSized for a.
Derive EnumSized for a.
Derive Shrink for a.
Derive Arbitrary for a.
Derive Show for a.
