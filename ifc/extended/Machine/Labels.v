Require Import ZArith.
Require Import EquivDec.

Require Import Utils.

Open Scope bool_scope.

(** Labels form a join-semi-lattice. *)

(** * Definition *)

Class JoinSemiLattice (Lab: Type) :=
{ bot : Lab
; join : Lab -> Lab -> Lab
; flows : Lab -> Lab -> bool
; meet : Lab -> Lab -> Lab
; bot_flows : forall l, flows bot l = true
; flows_refl : forall l, flows l l = true
; flows_trans : forall l1 l2 l3, flows l1 l2 = true -> flows l2 l3 = true -> flows l1 l3 = true
; flows_antisymm : forall l1 l2, flows l1 l2 = true -> flows l2 l1 = true -> l1 = l2
; flows_join_right : forall l1 l2, flows l1 (join l1 l2) = true
; flows_join_left : forall l1 l2, flows l2 (join l1 l2) = true
; join_minimal : forall l1 l2 l, flows l1 l = true -> flows l2 l = true -> flows (join l1 l2) l = true
}.

Notation "l1 \_/ l2" := (join l1 l2) (at level 40) : type_scope.
Notation "l1 <: l2" := (flows l1 l2) (at level 50, no associativity) : type_scope.
Notation "⊥" := bot.

(* Might be used at some point as the default for clearance
Parameter top : Lab.
Hypothesis flows_top : forall l, l <: top. *)

Hint Resolve
  @flows_refl
  @flows_trans
  @flows_join_left
  @flows_join_right
  @flows_antisymm
  @join_minimal: lat.

Definition flows_to {Lab:Type} `{JoinSemiLattice Lab} (l1 l2:Lab) : Z :=
  if flows l1 l2 then 1%Z else 0%Z.

(** Immediate properties from the semi-lattice structure. *)
Section JoinSemiLattice_properties.

Context {T: Type}.

(* AAA: used to be assumption, not used *)
Lemma flows_join {L:JoinSemiLattice T} : forall l1 l2, l1 <: l2 = true <-> l1 \_/ l2 = l2.
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

Lemma join_1_rev {L: JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l = true -> l1 <: l = true.
Proof. eauto with lat. Qed.

Lemma join_2_rev {L: JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l  = true -> l2 <: l  = true.
Proof. eauto with lat. Qed.

Lemma join_1 {L: JoinSemiLattice T} : forall l l1 l2,
  l <: l1  = true -> l <: l1 \_/ l2  = true.
Proof. eauto with lat. Qed.

Lemma join_2 {L: JoinSemiLattice T}: forall l l1 l2,
  l <: l2 = true -> l <: l1 \_/ l2 = true.
Proof. eauto with lat. Qed.

Lemma join_bot_right {L: JoinSemiLattice T} : forall l,
  l \_/ bot = l.
Proof.
  eauto using bot_flows with lat.
Qed.

Lemma join_bot_left {L: JoinSemiLattice T} : forall l,
  bot \_/ l = l.
Proof. eauto using bot_flows with lat.
Qed.

Lemma not_flows_not_join_flows_left {L: JoinSemiLattice T}: forall l l1 l2,
  l1 <: l = false ->
  (l1 \_/ l2) <: l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_1_rev; eauto.
  auto.
Qed.

Lemma not_flows_not_join_flows_right {L: JoinSemiLattice T}: forall l l1 l2,
  l2 <: l = false ->
  (l1 \_/ l2) <: l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_2_rev; eauto.
  auto.
Qed.

End JoinSemiLattice_properties.

Hint Resolve
  @join_1
  @join_2
  @bot_flows
  @not_flows_not_join_flows_right
  @not_flows_not_join_flows_left : lat.

(*
(** The two point lattice *)
Inductive Lab2 : Set :=
  | L : Lab2
  | H : Lab2.

Instance HL : JoinSemiLattice Lab :=
{  bot := L
;  join l1 l2 :=
     match l1, l2 with
       | H, _ => H
       | _, H => H
       | L, L => L
     end
; flows l1 l2 :=
    match l1, l2 with
      | L, _ => true
      | _, H => true
      | _, _ => false
    end
}.
Proof.
auto.
intros l; destruct l; auto.
intros l1 l2 l3; destruct l1, l2, l3; auto.
intros l1 l2; destruct l1, l2; auto.
intuition.
intuition.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.
*)

Instance LatEqDec (T : Type) {Lat : JoinSemiLattice T} : EqDec T eq.
  intros x y.
  destruct (x <: y) eqn:xy;
  destruct (y <: x) eqn:yx; try (right; congruence).
  - left. compute. eauto with lat.
  - generalize (flows_refl x). intros.
    right. congruence.
Defined.
