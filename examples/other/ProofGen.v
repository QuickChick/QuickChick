From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Inductive ty : nat -> Type :=
| pi : forall n i , i <= n -> ty n.

Program Definition gen_ty (p : nat) :  G (ty p) :=
  bindPf (choose (0, p)) (fun m H =>
  returnGen (pi p m  _) ).
Next Obligation.
  apply semChoose in H; auto.
Defined.
