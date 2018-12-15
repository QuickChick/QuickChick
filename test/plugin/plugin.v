From QuickChick Require Import QuickChick.

Inductive foo (A : Type) :=
| bar : A -> foo A -> foo A
| baz : foo A
.

Derive Show for foo.
