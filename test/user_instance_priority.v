From QuickChick Require Import QuickChick.

(* Derived instances are registered at priority 42, as the legacy engine
   does, so a user instance with a better priority wins resolution even when
   it is declared after the derivation. *)

Inductive name := Named : nat -> list nat -> name.

QuickChick Derive (GenSized, EnumSized) for name.

Definition canonical_gen : G name := returnGen (Named 0 nil).
Definition canonical_enum : E name := returnEnum (Named 0 nil).

#[global] Instance canonical_gen_sized : GenSized name | 1 :=
  {| arbitrarySized := fun _ => canonical_gen |}.
#[global] Instance canonical_enum_sized : EnumSized name | 1 :=
  {| enumSized := fun _ => canonical_enum |}.

Goal @arbitrarySized name _ = fun _ => canonical_gen.
Proof. reflexivity. Qed.

Goal @enumSized name _ = fun _ => canonical_enum.
Proof. reflexivity. Qed.

Inductive small : nat -> Prop := Small : small 0.

QuickChick Derive DecOpt for (small n).

#[global] Instance always_small n : DecOpt (small n) | 1 :=
  {| decOpt := fun _ => Some true |}.

Goal forall n, @decOpt (small n) _ = fun _ => Some true.
Proof. reflexivity. Qed.

(* A plain-type generator registers at the same priority. *)
Inductive old_name := OldNamed : nat -> old_name.

QuickChick Derive GenSized for old_name.

#[global] Instance canonical_old : GenSized old_name | 1 :=
  {| arbitrarySized := fun _ => returnGen (OldNamed 0) |}.

Goal @arbitrarySized old_name _ = fun _ => returnGen (OldNamed 0).
Proof. reflexivity. Qed.
