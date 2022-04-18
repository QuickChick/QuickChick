From Coq Require Import Init.Nat Lia List.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssreflect.eqtype.

Import ListNotations.

Inductive Sorted : list nat -> Prop :=
  Sorted_nil : Sorted []
| Sorted_singl x : Sorted [x]
| Sorted_cons x y l :
    x <= y -> Sorted (y :: l) -> Sorted (x :: y :: l).


Derive DecOpt for (Sorted l).

Instance DecOptsorted_sound  l : DecOptSoundPos (Sorted l).
Proof. derive_sound. Qed.

Lemma sorted_2000 : Sorted (repeat 1 5000).
Proof.
  time (repeat (first [ eapply Sorted_cons; [ apply le_n | ]
                      | eapply Sorted_singl ])). 
Time Qed.

(* Tactic call ran for 11.202 secs (11.171u,0.019s) (success) *)
(* Finished transaction in 16.283 secs (16.23u,0.03s) (successful) *)

(* Tactic call ran for 79.948 secs (78.952u,0.851s) (success) *)
(* Finished transaction in 326.736 secs (240.418u,1.744s) (successful) *)

Lemma sorted_2000' : Sorted (repeat 1 2000).
Proof.
  time (eapply sound with (s := 2000); compute; reflexivity).
Time Qed.
(* Tactic call ran for 0.05 secs (0.05u,0.s) (success) *)
(* Finished transaction in 0.059 secs (0.058u,0.s) (successful) *)


Lemma sorted_5000' : Sorted (repeat 1 5000).
Proof.
  time (eapply sound with (s := 5000); compute; reflexivity).
Time Qed.
