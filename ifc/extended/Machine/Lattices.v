Require Import EquivDec.
Require Export RelationClasses.
Require Export SetoidClass.
Require Import ZArith.
Require Import ListSet.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.

Require Export Utils.

Open Scope bool_scope.

(** Assumptions: labels form a join-semi-lattice. *)

(** * Definition *)

Class JoinSemiLattice (Lab: Type) :=
{ bot : Lab
; join : Lab -> Lab -> Lab
; flows : Lab -> Lab -> bool
; meet : Lab -> Lab -> Lab
; bot_flows : forall l, flows bot l  = true
; flows_refl : forall l, flows l l  = true
; flows_trans : forall l1 l2 l3,  flows l1 l2  = true -> flows l2 l3  = true -> flows l1 l3  = true
; flows_antisymm : forall l1 l2,  flows l1 l2  = true -> flows l2 l1 = true -> l1 = l2
; flows_join_right : forall l1 l2, flows l1 (join l1 l2) = true
; flows_join_left : forall l1 l2, flows l2 (join l1 l2) = true
; join_minimal : forall l1 l2 l, flows l1 l  = true -> flows l2 l  = true -> flows (join l1 l2) l = true
}.

Notation "l1 \_/ l2" := (join l1 l2) (at level 40) : type_scope.
Notation "l1 <: l2" := (flows l1 l2) (at level 50, no associativity) : type_scope.

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

Module Type ZFSET.

  Parameter t : Type.
  Parameter elements : t -> list Z.
  Definition In (z:Z) (s:t) := In z (elements s).

  Parameter empty : t.
  Parameter elements_empty : elements empty = nil.

  Parameter add : Z -> t -> t.
  Parameter In_add : forall z s x,
     In x (add z s) <-> x=z \/ In x s.

  Parameter union : t -> t -> t.
  Parameter In_union : forall s1 s2 x,
     In x (union s1 s2) <-> In x s1 \/ In x s2.

  Parameter inter : t -> t -> t.
  Parameter In_inter : forall s1 s2 x,
     In x (inter s1 s2) <-> In x s1 /\ In x s2.

  Parameter incl : t -> t -> bool.
  Parameter incl_spec : forall s1 s2,
    incl s1 s2 = true <-> List.incl (elements s1) (elements s2).

  Parameter antisym : forall s1 s2,
  incl s1 s2 = true ->
  incl s2 s1 = true ->
  s1 = s2.

End ZFSET.

Module Zset : ZFSET.

  Definition mem := set_mem Z.eq_dec.

  Fixpoint sorted (l:list Z) : bool :=
    match l with
      | nil => true
      | x :: q1 =>
        match q1 with
          | nil => true
          | y :: q =>
            Z.ltb x y && sorted q1
        end
    end.

  Record t_ := ZS { elements:> list Z; sorted_elements: sorted elements = true }.
  Definition t := t_.
  Hint Resolve sorted_elements.

  Definition In (z:Z) (s:t) := In z (elements s).

  Program Definition empty : t := ZS nil _.

  Definition elements_empty : elements empty = nil.
  Proof.
    simpl; auto.
  Qed.

  Lemma mem_elements : forall s z,
    mem z s = true <-> List.In z s.
  Proof.
    unfold mem; split; intros.
    - apply (set_mem_correct1 Z.eq_dec); auto.
    - apply (set_mem_correct2 Z.eq_dec); auto.
  Qed.

  Fixpoint insert (a:Z) (l:list Z) : list Z :=
    match l with
        nil => a::nil
      | x::q => if Z_lt_dec a x then a::l else
                  if Z_eq_dec a x then x::q
                  else x::(insert a q)
    end.

(* Zlt_is_lt_bool: forall n m : Z, (n < m)%Z <-> (n <? m)%Z = true *)

  Lemma sorted_insert : forall l z,
    sorted l = true -> sorted (insert z l) = true.
  Proof.
    induction l; simpl; auto; intros.
    destruct l; auto.
    - destruct Z_lt_dec; simpl.
      + rewrite (Zlt_is_lt_bool z a) in l.
        rewrite l; auto.
      + destruct Z.eq_dec; simpl; auto.
        rewrite andb_true_iff; split; auto.
        rewrite <- Zlt_is_lt_bool.
        omega.
    - rewrite andb_true_iff in H; destruct H.
      destruct Z_lt_dec.
      + simpl.
        rewrite Zlt_is_lt_bool in l0.
        rewrite l0; rewrite H.
        simpl in H0; rewrite H0.
        auto.
      + destruct Z.eq_dec; simpl.
        * rewrite H.
          simpl in H0; rewrite H0.
          auto.
        * {
            destruct Z_lt_dec; simpl.
            - rewrite Zlt_is_lt_bool in l0.
              rewrite l0.
              assert (a < z)%Z by omega.
              rewrite Zlt_is_lt_bool in H1.
              rewrite H1.
              simpl in H0; rewrite H0; auto.
            - destruct Z.eq_dec.
              + rewrite H; auto.
              + rewrite H.
                generalize (IHl z); simpl.
                destruct Z_lt_dec; try omega.
                destruct Z.eq_dec; try omega.
                auto.
          }
  Qed.

  Lemma In_insert : forall x l z,
     List.In x (insert z l) <-> x=z \/ List.In x l.
  Proof.
    split.
    - generalize dependent z; induction l.
      + simpl; intuition.
      + simpl; intros z.
        destruct Z_lt_dec; simpl; auto.
        * intuition.
        * destruct Z.eq_dec.
          simpl; intuition.
          simpl; intuition.
          apply IHl in H0; intuition.
    - generalize dependent z; induction l.
      + simpl; intuition.
      + intro z; simpl.
        destruct Z_lt_dec; simpl; auto.
        * intuition.
        * destruct Z.eq_dec.
          simpl; intuition.
          simpl; intuition.
  Qed.

  Program Definition add (z:Z) (s: t) : t :=
    ZS (insert z s) _.
  Next Obligation.
    destruct s; simpl.
    apply sorted_insert; auto.
  Qed.

  Lemma In_add : forall z s x,
     In x (add z s) <-> x=z \/ In x s.
  Proof.
    unfold add, In; destruct s as [l Hl]; simpl.
    intros; apply In_insert.
  Qed.

  Fixpoint union_list (l1 l2:list Z) : list Z :=
    match l1 with
      | nil => l2
      | x::q => union_list q (insert x l2)
    end.

  Lemma sorted_union : forall l1 l2,
    sorted l2 = true -> sorted (union_list l1 l2) = true.
  Proof.
    induction l1; simpl; auto.
    eauto using sorted_insert.
  Qed.

  Lemma In_union_list : forall l1 l2 x,
     List.In x (union_list l1 l2) <-> List.In x l1 \/ List.In x l2.
  Proof.
    induction l1; simpl; intuition.
    - rewrite IHl1 in H; intuition.
      rewrite In_insert in H0; intuition.
    - rewrite IHl1.
      rewrite In_insert; intuition.
    - rewrite IHl1; auto.
    - rewrite IHl1.
      rewrite In_insert; intuition.
  Qed.

  Program Definition union (s1 s2: t) : t :=
    ZS (union_list s1 s2) _.
  Next Obligation.
    destruct s1 as [l1 H1].
    destruct s2 as [l2 H2].
    simpl.
    apply sorted_union; auto.
  Qed.

  Lemma In_union : forall s1 s2 x,
     In x (union s1 s2) <-> In x s1 \/ In x s2.
  Proof.
    unfold union, In; destruct s1; destruct s2; simpl.
    apply In_union_list.
  Qed.

  (* Naive version for now *)
  Fixpoint inter_list (l1 l2:list Z) : list Z :=
    match l1 with
      | nil => nil
      | x::q => (if existsb (Z.eqb x) l2 then (fun l => x::l) else (fun l => l))
                  (inter_list q l2)
    end.

  Lemma sorted_drop : forall l a, sorted (a :: l) = true -> sorted l = true.
    intros. simpl in H.
    destruct l; auto.
    rewrite andb_true_iff in H.
    inversion_clear H.
    auto.
  Qed.

  Lemma sorted_min : forall l1 a, sorted (a :: l1) = true ->
                       forall x, List.In x l1 -> (a <? x)%Z = true.
    induction l1.
    - simpl; auto.
    - intros.
      pose proof H.
      apply sorted_drop in H.
      pose proof (IHl1 a H x).
      assert ((a0 <? a)%Z = true).
      simpl in H1; rewrite andb_true_iff in H1; inversion_clear H1; auto.
      inversion H0.
      * subst; auto.
      * apply H2 in H4.
      rewrite <- Zlt_is_lt_bool in *.
      eapply Z.lt_trans; eauto.
  Qed.

  Lemma in_inter : forall l1 l2 x, List.In x (inter_list l1 l2) -> List.In x l1.
    induction l1; simpl; auto.
    intros.
    destruct (existsb (Z.eqb a) l2) eqn:Mem.
    - inversion_clear H; [left; auto | right; eapply IHl1; eauto].
    - right. eapply IHl1; eauto.
  Qed.

  Lemma sorted_min_head : forall l a, sorted l = true ->
                            (forall x, List.In x l -> (a <? x)%Z = true) ->
                            sorted (a :: l) = true.
    intros.
    simpl.
    intros.
    destruct l; auto.
    pose proof (H0 z).
    assert (List.In z (z :: l)) by (simpl; left; auto).
    apply H1 in H2.
    apply andb_true_iff. auto.
  Qed.

  Lemma sorted_inter : forall l1 l2,
    sorted l1 = true -> sorted (inter_list l1 l2) = true.
  Proof.
    induction l1.
    - simpl; auto.
    - intros; simpl.
      destruct (existsb (Z.eqb a) l2) eqn:Mem.
      * pose proof H.
        apply sorted_drop in H.
        apply sorted_min_head.
        + apply IHl1; auto.
        + intros.
          apply in_inter in H1.
          eapply sorted_min; eauto.
      * apply IHl1. apply sorted_drop in H. auto.
  Qed.

  Program Definition inter (s1 s2: t) : t :=
    ZS (inter_list s1 s2) _.
  Next Obligation.
    destruct s1 as [l1 H1].
    destruct s2 as [l2 H2].
    simpl.
    apply sorted_inter; auto.
  Qed.

  Lemma In_inter_list : forall l1 l2 x,
     List.In x (inter_list l1 l2) <-> List.In x l1 /\ List.In x l2.
  Proof.
    induction l1; simpl; intuition.
    - destruct (existsb (Z.eqb a) l2) eqn:Mem.
      * inversion_clear H; [left; auto | right; eapply in_inter; eauto].
      * right ; eapply in_inter; eauto.
    - destruct (existsb (Z.eqb a) l2) eqn:Mem.
      * inversion_clear H; subst.
        apply List.existsb_exists in Mem.
        inversion_clear Mem. inversion_clear H.
        + rewrite Z.eqb_eq in H1; subst; auto.
        + pose proof (IHl1 l2 x).
          inversion_clear H.
          apply H1 in H0.
          inversion_clear H0.
          auto.
      * pose proof (IHl1 l2 x).
        inversion_clear H0.
        apply H1 in H.
        inversion_clear H.
        auto.
    - destruct (existsb (Z.eqb a) l2) eqn:Mem.
      * inversion_clear H; subst.
        apply List.existsb_exists in Mem.
        inversion_clear Mem. inversion_clear H.
        simpl; left; auto.
      * pose proof (List.existsb_exists (Z.eqb a) l2).
        inversion_clear H0.
        assert (exists x, List.In x l2 /\ (a =? x)%Z = true).
          exists x; split; subst; try rewrite Z.eqb_eq; auto.
        apply H3 in H0.
        rewrite Mem in H0.
        inversion H0.
    - destruct (existsb (Z.eqb a) l2) eqn:Mem.
      * simpl; right; apply IHl1; split; auto.
      * apply IHl1; split; auto.
  Qed.

  Lemma In_inter : forall s1 s2 x,
     In x (inter s1 s2) <-> In x s1 /\ In x s2.
  Proof.
    unfold inter, In; destruct s1; destruct s2; simpl.
    apply In_inter_list.
  Qed.

  Fixpoint set_incl (l1 l2 : list Z) : bool :=
    match l1 with
      | nil => true
      | x::q => mem x l2 && set_incl q l2
    end.

  Lemma set_incl_spec : forall l1 l2,
    set_incl l1 l2 = true <-> List.incl l1 l2.
  Proof.
    unfold incl.
    induction l1; simpl; intuition.
    - rewrite andb_true_iff in H; destruct H; subst.
      unfold mem in *.
      apply set_mem_correct1 in H; auto.
    - rewrite andb_true_iff in H; destruct H; subst.
      rewrite IHl1 in H0; auto.
    - rewrite andb_true_iff; split.
      + apply set_mem_correct2; auto.
        apply H; auto.
      + rewrite IHl1.
        intros; auto.
  Qed.

  Definition incl (s1 s2:t) : bool :=
    let (l1, _) := s1 in
    let (l2, _) := s2 in
    set_incl l1 l2.

  Lemma incl_spec : forall s1 s2,
    incl s1 s2 = true <-> List.incl (elements s1) (elements s2).
  Proof.
    destruct s1; destruct s2; simpl.
    apply set_incl_spec.
  Qed.

  Lemma inv_sorted_cons1: forall a l,
    sorted (a :: l) = true -> sorted l = true.
  Proof.
    simpl; destruct l; auto.
    rewrite andb_true_iff; intuition.
  Qed.

  Lemma inv_sorted_cons_2_aux: forall l,
    sorted l = true ->
    match l with
      | nil => True
      | a::l =>
        forall x, List.In x l -> (a < x)%Z
    end.
  Proof.
    simpl; induction l; intuition.
    destruct l; intuition.
    simpl in H.
    rewrite andb_true_iff in H; intuition.
    simpl in H0; destruct H0.
    - subst.
      rewrite <- Zlt_is_lt_bool in H1; auto.
    - generalize (H _ H0).
      rewrite <- Zlt_is_lt_bool in H1; omega.
  Qed.

  Lemma inv_sorted_cons_2: forall a l,
    sorted (a :: l) = true ->
    forall x, List.In x l -> (a < x)%Z.
  Proof.
    destruct l; intuition.
    generalize (inv_sorted_cons_2_aux _ H).
    auto.
  Qed.

  Lemma inv_sorted_cons_3: forall a l,
    sorted (a :: l) = true ->
    ~ List.In a l.
  Proof.
    red; intros.
    assert (a<a)%Z.
    eapply inv_sorted_cons_2; eauto.
    omega.
  Qed.

  Lemma set_antisym : forall l1 l2,
    List.incl l1 l2 ->
    List.incl l2 l1 ->
    sorted l1 = true -> sorted l2 = true ->
    l1 = l2.
  Proof.
    unfold List.incl.
    induction l1; destruct l2; intros; auto.
    - elim H0 with z; simpl; auto.
    - elim H with a; simpl; auto.
    - assert (a=z).
        destruct (H a); simpl; auto.
        destruct (H0 z); simpl; auto.
        exploit inv_sorted_cons_2; eauto.
        clear H2.
        exploit inv_sorted_cons_2; eauto.
        omega.
      subst.
      f_equal.
      apply IHl1.
      + intros x T; destruct (H x); simpl; auto.
        subst.
        apply inv_sorted_cons_3 in H1; intuition.
      + intros x T; destruct (H0 x); simpl; auto.
        subst.
        apply inv_sorted_cons_3 in H2; intuition.
      + eapply inv_sorted_cons1; eauto.
      + eapply inv_sorted_cons1; eauto.
  Qed.

  Lemma antisym : forall s1 s2,
    incl s1 s2 = true ->
    incl s2 s1 = true ->
    s1 = s2.
  Proof.
    destruct s1 as [l1 H1]; destruct s2 as [l2 H2]; simpl; intros.
    assert (l1=l2).
      eapply set_antisym; eauto.
      rewrite set_incl_spec in H; auto.
      rewrite set_incl_spec in H0; auto.
    subst.
    assert (H1=H2).
    apply eq_proofs_unicity.
    destruct x; destruct y; intuition congruence.
    f_equal.
    assumption.
  Qed.

(* Program Lemma elements__label_of_list:  *)
(*   forall lst,  *)
(*     elements (fold_left (fun a b => add b a) lst empty) = lst. *)
(* Proof. *)
(*   intros lst. induction lst; [reflexivity |]. *)
(*   simpl. rewrite add.    *)
(*   => [| x xs IHxs].  *)




End Zset.

Lemma Zset_add_incl : forall x s, Zset.incl s (Zset.add x s) = true.
Proof.
  intros; rewrite Zset.incl_spec.
  intros a H.
  generalize (Zset.In_add x s a); unfold Zset.In.
  intro T; rewrite T; auto.
Qed.

Instance ZsetLat : JoinSemiLattice Zset.t :=
{  bot := Zset.empty
;  join := Zset.union
;  flows := Zset.incl
;  meet := Zset.inter
}.
Proof.
  - intros s; rewrite Zset.incl_spec; intros x.
    rewrite Zset.elements_empty; simpl; intuition.
  - intros s; rewrite Zset.incl_spec; intros x; auto.
  - intros s1 s2 s3; repeat rewrite Zset.incl_spec.
    unfold incl; eauto.
  - intros; eapply Zset.antisym; eauto.
  - intros s1 s2; rewrite Zset.incl_spec; intros x; auto.
    intros; apply Zset.In_union; auto.
  - intros s1 s2; rewrite Zset.incl_spec; intros x; auto.
    intros; apply Zset.In_union; auto.
  - intros s1 s2 s3; repeat rewrite Zset.incl_spec.
    unfold incl; intros.
    rewrite (Zset.In_union s1 s2 a) in H1.
    intuition.
Defined.

Definition Label := Zset.t.
Notation "⊥" := bot.
Definition flows_to (l1 l2:Label) : Z :=
  if flows l1 l2 then 1%Z else 0%Z.
Definition label_of_list (l : list Z) :=
  fold_left (fun a b => Zset.add b a) l Zset.empty.