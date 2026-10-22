From QuickChick Require Import QuickChick.

Inductive box (A : Type) := Box : A -> box A.
QCDerive (GenSized, EnumSized) for box.

Inductive related {A B : Type} : A -> B -> Prop :=
| Related : forall x y, related x y.
QCDerive Checker for (@related A B x y).
QCDerive Generator for (fun (y : B) => @related A B x y).

From QuickChick Require Import LegacyDerive.
Inductive legacy_box (A : Type) := LegacyBox : A -> legacy_box A.
Derive GenSized for legacy_box.

Extract Constant defNumTests => "3".

Module ModuleDemo.
  Inductive light := On | Off.
  QCDerive (GenSized, Shrink, Show) for light.
  QuickChick (fun x : light => match x with On | Off => true end).
End ModuleDemo.

Goal forall n : nat, n = n.
  quickchick 2.
  QuickChick (theorem 4).
  intros; reflexivity.
Qed.
