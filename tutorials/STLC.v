From QuickChick Require Import QuickChick.

Inductive type :=
| Base  : type
| Arrow : type -> type -> type.
