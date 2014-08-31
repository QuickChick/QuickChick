Require Import ZArith.
Require Import EquivDec.
Require Import List.

Require Import ssreflect ssrbool eqtype seq.

Require Import Utils.

Class JoinSemiLattice (Lab : Type) :=
{ bot : Lab
; join : Lab -> Lab -> Lab
; flows : Lab -> Lab -> bool
; meet : Lab -> Lab -> Lab
; bot_flows : forall l, flows bot l = true
; flows_refl : forall l, flows l l = true
; flows_trans : forall l1 l2 l3, flows l1 l2 = true ->
                                 flows l2 l3 = true ->
                                 flows l1 l3 = true
; flows_antisymm : forall l1 l2, flows l1 l2 = true ->
                                 flows l2 l1 = true -> l1 = l2
; flows_join_right : forall l1 l2, flows l1 (join l1 l2) = true
; flows_join_left : forall l1 l2, flows l2 (join l1 l2) = true
; join_minimal : forall l1 l2 l, flows l1 l = true ->
                                 flows l2 l = true ->
                                 flows (join l1 l2) l = true
}.

Notation "l1 \_/ l2" := (join l1 l2) (at level 40) : type_scope.
Notation "l1 <: l2" := (flows l1 l2 = true)
  (at level 50, no associativity) : type_scope.
Notation "⊥" := bot.

Hint Resolve
  @flows_refl
  @flows_trans
  @flows_join_left
  @flows_join_right
  @flows_antisymm
  @join_minimal : lat.

Definition flows_to {Lab : Type} `{JoinSemiLattice Lab} (l1 l2 : Lab) : Z :=
  if flows l1 l2 then 1%Z else 0%Z.

(** Immediate properties from the semi-lattice structure. *)
Section JoinSemiLattice_properties.

Context {T: Type}.

Lemma flows_join {L : JoinSemiLattice T} : forall l1 l2,
  l1 <: l2 <-> l1 \_/ l2 = l2.
Proof.
  intros.
  split.
  - intros H.
    apply flows_antisymm.
    + apply join_minimal; auto with lat.
    + apply flows_join_left.
  - intros H.
    rewrite <- H.
    auto with lat.
Qed.

Lemma join_1_rev {L : JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l -> l1 <: l.
Proof. eauto with lat. Qed.

Lemma join_2_rev {L : JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l -> l2 <: l.
Proof. eauto with lat. Qed.

Lemma join_1 {L : JoinSemiLattice T} : forall l l1 l2,
  l <: l1 -> l <: l1 \_/ l2.
Proof. eauto with lat. Qed.

Lemma join_2 {L : JoinSemiLattice T} : forall l l1 l2,
  l <: l2 -> l <: l1 \_/ l2.
Proof. eauto with lat. Qed.

Lemma join_bot_right {L : JoinSemiLattice T} : forall l,
  l \_/ bot = l.
Proof.
  eauto using bot_flows with lat.
Qed.

Lemma join_bot_left {L:  JoinSemiLattice T} : forall l,
  bot \_/ l = l.
Proof. eauto using bot_flows with lat.
Qed.

Lemma not_flows_not_join_flows_left {L : JoinSemiLattice T} : forall l l1 l2,
  flows l1 l = false ->
  flows (l1 \_/ l2) l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_1_rev; eauto.
  auto.
Qed.

Lemma not_flows_not_join_flows_right {L : JoinSemiLattice T} : forall l l1 l2,
  flows l2 l = false ->
  flows (l1 \_/ l2) l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_2_rev; eauto.
  auto.
Qed.

Definition label_eqb {L : JoinSemiLattice T} l1 l2 :=
  flows l1 l2 && flows l2 l1.

Lemma label_eqP (L : JoinSemiLattice T) : Equality.axiom label_eqb.
Proof.
move => l1 l2.
rewrite /label_eqb.
apply/(iffP idP).
- move/andP => [H1 H2].
  by apply flows_antisymm.
- move => -> .
  by rewrite !flows_refl.
Qed.

Definition label_eqMixin (L : JoinSemiLattice T) := EqMixin (@label_eqP L).

End JoinSemiLattice_properties.

Hint Resolve
  @join_1
  @join_2
  @bot_flows
  @not_flows_not_join_flows_right
  @not_flows_not_join_flows_left : lat.

Definition label_dec {T : Type} {Lat : JoinSemiLattice T}
  : forall l1 l2 : T, {l1 = l2} + {l1 <> l2}.
Proof.
  intros x y.
  destruct (flows x y) eqn:xy;
  destruct (flows y x) eqn:yx; try (right; congruence).
  - left. eauto with lat.
  - generalize (flows_refl x). intros.
    right. congruence.
Defined.

Instance LatEqDec (T : Type) {Lat : JoinSemiLattice T} : EqDec T eq.
  intros x y.
  destruct (flows x y) eqn:xy;
  destruct (flows y x) eqn:yx; try (right; congruence).
  - left. compute. eauto with lat.
  - generalize (flows_refl x). intros.
    right. congruence.
Defined.

Class Lattice (Lab: Type) :=
{ jslat :> JoinSemiLattice Lab
; top : Lab
; flows_top : forall l, l <: top
}.

Class FiniteLattice (Lab : Type) :=
{
  lat :> Lattice Lab
; elems : list Lab
; all_elems : forall l : Lab, In l elems
}.

Definition allThingsBelow {L : Type} `{FiniteLattice L} (l : L) : list L :=
  filter (fun l' => flows l' l) elems.

Module LabelEqType.

Canonical label_eqType T {L : JoinSemiLattice T} := Eval hnf in EqType _ (label_eqMixin L).

End LabelEqType.
