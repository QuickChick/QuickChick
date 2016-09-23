From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.

Inductive Foo :=
| Foo1 : Foo
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

DeriveShow Foo as "showFoo".
Print showFoo.

DeriveArbitrary Foo as "arbFoo".
Print arbFoo.

Inductive Bar A :=
| Bar1 : Bar A
| Bar2 : Bar A -> Bar A
| Bar3 : A -> A -> Bar A -> Bar A.

DeriveShow Bar as "showBar".
Print showBar.

DeriveArbitrary Bar as "arbBar".
Print arbBar.

Definition testGen : G (Bar nat) := arbitrary.

Sample testGen.