Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(* These should be moved to /src *)
Lemma max_lub_l_ssr n m p:
  max n m < p -> n < p.
Proof.
  move /ltP/PeanoNat.Nat.max_lub_lt_iff => [/ltP H1 _].
  assumption.
Qed.

Lemma max_lub_r_ssr n m p:
  max n m < p -> m < p.
Proof.
  move /ltP/PeanoNat.Nat.max_lub_lt_iff => [_ /ltP H1].
  assumption.
Qed.

Lemma max_lub_ssr n m p :
  n < p -> m < p -> max n m < p.
Proof.
  move => /ltP H1 /ltP H2.
  apply/ltP/PeanoNat.Nat.max_lub_lt; eassumption.
Qed.

(* TODO do implicits for the rest of the file *)

Set Implicit Arguments.
Unset Strict Implicit.


Lemma lt0_False :
  forall n, ~ n < 0.
Proof.
  firstorder.
Qed.

Lemma leq_ltS n m :
  n <= m -> n < m.+1.
Proof.
  eauto.
Qed.

Lemma ltS_leq n m :
  n <= m -> n < m.+1.
Proof.
  eauto.
Qed.
