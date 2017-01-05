From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

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

Lemma setU_set0_neut_eq {A} (s s1 : set A) :
  s1 <--> set0 ->
  s <--> s :|: s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_symm {A} (s1 s2 : set A) :
  s1 <--> s2 -> s2 <--> s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_refl {A} (s : set A) :
  s <--> s.
Proof.
  firstorder.
Qed.

Lemma bigcup_set0_r (T U : Type) (s : set T) (F : T -> set U) :
  (forall x, F x <--> set0) ->
  \bigcup_(x in s) F x <--> set0.
Proof.
  firstorder.
Qed.

Lemma bigcup_set0_l_eq (T U : Type) (s : set T) (F : T -> set U) :
  s <--> set0 ->
  \bigcup_(x in s) F x <--> set0.
Proof.
  firstorder.
Qed.

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

Lemma setU_set0_l {A} (s1 s2 s3 : set A) :
  s1 <--> set0 ->
  s2 <--> s3 ->
  (s1 :|: s2) <--> s3. 
Proof.
  firstorder.
Qed.

Lemma setU_set0_r {A} (s1 s2 s3 : set A) :
  s1 <--> set0 ->
  s3 <--> s2 ->
  s3 <--> (s1 :|: s2). 
Proof.
  firstorder.
Qed.

Lemma eq_bigcup' :
  forall (T U : Type) (A B : set T) (F G : T -> set U),
    A <--> B ->
    (forall x, F x <--> G x) ->
    \bigcup_(x in A) F x <--> \bigcup_(x in B) G x.
Proof.
  intros.
  eapply eq_bigcup; eauto.
Qed.
