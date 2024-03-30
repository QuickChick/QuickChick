From QuickChick Require Import QuickChick Tactics.
From Coq Require Import Arith Lia List String.
Import ListNotations.
Import QcDefaultNotation.
Open Scope string.
Open Scope qc_scope.

Inductive ty : nat -> Type :=
| pi : forall n i , i <= n -> ty n.

Program Definition gen_ty (p : nat) :  G (ty p) :=
  bindPf (choose (0, p)) (fun m H =>
  returnGen (pi p m  _) ).
Next Obligation.
  apply semChooseGen in H; lia.
Defined.
