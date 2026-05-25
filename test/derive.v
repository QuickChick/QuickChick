From QuickChick Require Import QuickChick Classes.

Inductive a :=
  | A1 : a
  | A2 : b -> a
with b :=
  | B1 : b
  | B2 : a -> b.

QCDerive GenSized for a.
QCDerive EnumSized for a.
QCDerive Shrink for a.
QCDerive Arbitrary for a.
QCDerive Show for a.
