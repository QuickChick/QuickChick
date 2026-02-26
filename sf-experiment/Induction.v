(** * Induction: Proof by Induction *)

Require Export Basics.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Require Import List ZArith.
Import ListNotations.
(*
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq ssrnat eqtype.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
*)

Definition plus_n_O (n:nat) :=
  n =? n + 0.

(*! QuickChick plus_n_O. *)
