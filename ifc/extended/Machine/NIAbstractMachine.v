Require Import ZArith.
Require Import List.

Require Setoid.
Require RelationClasses.
Require Import Relations.
Require Import EquivDec.

Require Import Utils.
Require Import Lattices.
Require Import Machine.

Set Implicit Arguments.

Section ObsEquiv.

Definition low_pc (o: Label) (s: State) : Prop :=
  pc_lab (st_pc s) <: o = true.

Lemma low_pc_dec: forall o s, {low_pc o s}+{~ low_pc o s}.
Proof.
  intros. unfold low_pc.
  destruct (flows (pc_lab (st_pc s)) o) eqn:?; auto.
Qed.

SearchAbout Value.

Inductive low_equiv_val (o : Label) : relation Value :=
| le_v_int : forall i, low_equiv_val o (Vint i) (Vint i)
| le_v_lab : forall l, low_equiv_val o (Vlab l) (Vlab l)
| le_v_ptr : forall mf i, low_equiv_val o (Vptr (Ptr mf i)) (Vptr (Ptr mf i))
| le_v_cptr : forall i, low_equiv_val o (Vcptr i) (Vcptr i).

(** * Low equivalence relations *)
Inductive low_equiv_atom (o: Label) : relation Atom :=
| le_a_low : forall l v, l <: o = true -> low_equiv_atom o (v@l) (v@l)
| le_a_high: forall l1 l2 v1 v2,
  l1 = l2 ->
  l1 <: o = false ->
  l2 <: o = false ->
  low_equiv_atom o (v1@l1) (v2@l2).
Hint Constructors low_equiv_atom.

Lemma low_equiv_atom_equal:
  forall (a b: Value) (k l:Label) (o:Label), k <: o = true ->
    low_equiv_atom o (a@k) (b@l) -> a = b.
Proof.
  intros a b k l o h; inversion 1; auto.
  rewrite H4 in h. congruence.
Qed.

Instance low_pair (o: Label) : @Equivalence Atom (low_equiv_atom o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x;
  destruct (flows l o) eqn:?; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; auto.
  (* transitive *) intros x y z Hxy Hyz.
  inv Hxy; auto. inv Hyz ; auto.
Qed.

Global Instance low_atom (o: Label) : @Equivalence Atom (low_equiv_atom o) :=
  low_pair o.

(*
Global Instance low_pcatom (o: Label) : @Equivalence PcAtom Label) (low_equiv_atom o) :=
  low_pair Z o.
*)
Hint Extern 1 =>
  match goal with
    | |- low_equiv_atom _ _ _ => reflexivity
  end.


Lemma low_equiv_atom_join_value:
  forall o (v1 v0 v v2:Value) vl vl0  vl2 vl1,
    low_equiv_atom o (v1@vl) (v@ vl0) ->
    low_equiv_atom o (v2@ vl2) (v0@ vl1) ->
    low_equiv_atom o (v1@ vl \_/ vl2) (v@ vl0 \_/ vl1).
Proof.
  intros.
  inv H; inv H0; eauto with lat.
Qed.

Lemma low_equiv_atom_binop_value:
  forall o (f:Value->Value->option Value) (v1 v2 v1' v2' v v':Value) vl1 vl2  vl1' vl2',
    low_equiv_atom o (v1@vl1) (v1'@vl1') ->
    low_equiv_atom o (v2@vl2) (v2'@vl2') ->
    f v1 v2 = Some v ->
    f v1' v2' = Some v' ->
    low_equiv_atom o (v@vl1 \_/ vl2) (v'@vl1' \_/ vl2').
Proof.
  intros.
  inv H; inv H0;
  try (assert (v'=v) by congruence; subst); econstructor; auto with lat.
Qed.

(* TODO : Stacks
Inductive low_equiv_stkelt (o: Label) : StkElmt Label Label -> StkElmt Label Label -> Prop :=
| le_data : forall a1 a2
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (AData a1) (AData a2)
| le_aret : forall a1 a2 b
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (ARet a1 b) (ARet a2 b).
Hint Constructors low_equiv_stkelt.

Global Instance low_stkelt (o: Label) : @Equivalence (StkElmt Label Label) (low_equiv_stkelt o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; constructor ; symmetry; auto.
  (* transitive *) intros x y z Hxy Hyz.
  inv Hxy; inv Hyz; constructor; etransitivity; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_stkelt _ _ _ => reflexivity
  end.
*)
(* TODO: Rename and move *)
Lemma Forall2_app_left (A: Type) (low_equiv_a: A -> A -> Prop) :
  forall l1 l1' l2 l2',
    Forall2 low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    Forall2 low_equiv_a l1 l1'.
Proof.
  induction l1; intros; simpl in *.
  destruct l1'; [ eauto | inv H0].
  destruct l1'; [inv H0 | eauto].
  simpl in *; inv H; auto.
  constructor ; eauto.
Qed.

(* TODO: Rename and move *)
Lemma Forall2_app_right (A: Type) (low_equiv_a: A -> A -> Prop) :
  forall l1 l1' l2 l2',
    Forall2 low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    Forall2 low_equiv_a l2 l2'.
Proof.
  induction l1; intros; simpl in *.
  destruct l1' ; [simpl in * ; auto | inv H0].
  destruct l1'; [ inv H0 | simpl in * ].
  inv H; auto.
  eapply IHl1 ; eauto.
Qed.

(* TODO: Move and rename *)
Lemma index_list_low_eq (A: Type) (low_equiv: A -> A -> Prop) :
  forall n l1 l2 v1 v2,
    Forall2 low_equiv l1 l2 ->
    index_list n l1 = Some v1 ->
    index_list n l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  induction n ; intros.
  inv H; (simpl in * ; congruence).
  destruct l1, l2; (simpl in * ; try congruence).
  inv H.
  eapply IHn ; eauto.
Qed.

(* TODO: Move and rename *)
Lemma index_list_Z_low_eq (A: Type) (low_equiv: A -> A -> Prop) :
  forall i l1 l2 v1 v2,
    Forall2 low_equiv l1 l2 ->
    index_list_Z i l1 = Some v1 ->
    index_list_Z i l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  intros. eapply index_list_low_eq; eauto.
  eapply index_list_Z_nat; eauto.
  eapply index_list_Z_nat; eauto.
Qed.

Lemma update_list_high: forall o m1 m2,
  Forall2 (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Heq : l1 = l2)
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false),
    index_list a m1 = Some (o1@l1) ->
    update_list a (v@l2) m1 = Some m1' ->
    Forall2 (low_equiv_atom o) m1' m2.
Proof.
  induction 1; intros.
  destruct a; simpl in *; allinv.

  destruct a; simpl in *; allinv.
  constructor ; auto. inv H ; auto.


  case_eq (update_list a (v@l2) l) ; intros;
  rewrite H3 in *; allinv.
  constructor; auto.
  eapply (IHForall2 a l0 o1 v l2 l2) ; eauto.
Qed.

Lemma update_list_Z_high: forall o m1 m2,
  Forall2 (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Heq : l1 = l2)
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false),
    index_list_Z a m1 = Some (o1@l1) ->
    update_list_Z a (v@l2) m1 = Some m1' ->
    Forall2 (low_equiv_atom o) m1' m2.
Proof.
  intros.
  eapply update_list_high with (l1 := l1) (l2 := l2); eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.


Global Instance low_list
          (A: Type)
          (R: relation A)
          (EqR: Equivalence R) : @Equivalence (list A) (@Forall2 A A R).
Proof.
  constructor.
  (* reflexive *) unfold Reflexive. induction x; intros; constructor; auto. reflexivity.
  (* symmetric *)
  unfold Symmetric.
  induction x ; intros; (inv H ; constructor ; auto). symmetry; auto.
  (* transitive *)
  unfold Transitive.
  induction x; intros.
  inv H. auto. inv H. inv H0.
  constructor. etransitivity; eauto.
  eapply IHx ; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- Forall2 _ _ _ => reflexivity
  end.

Lemma update_list_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list a m = Some (o@l) ->
  update_list a (v@l) m = Some m' ->
  Forall2 (low_equiv_atom obs) m m'.
Proof.
  induction a; intros.
  destruct m ; simpl in *; allinv.
  constructor; auto.

  destruct m ; simpl in *; allinv.
  case_eq (update_list a (v@l) m) ; intros; rewrite H1 in *; allinv.
  constructor; eauto.
Qed.

Lemma update_list_Z_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list_Z a m = Some (o@l) ->
  update_list_Z a (v@l) m = Some m' ->
  Forall2 (low_equiv_atom obs) m m'.
Proof.
  intros. eapply update_list_low_equiv; eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.

(* TODO: Refactor and move *)
Lemma update_list_low_gen :
  forall T (R : T -> T -> Prop) n
         (x1 x2 : T)
         (l1 l1' l2 l2' : list T)
         (ELTS : R x1 x2)
         (LISTS : Forall2 R l1 l2)
         (UPD1 : update_list n x1 l1 = Some l1')
         (UPD2 : update_list n x2 l2 = Some l2'),
    Forall2 R l1' l2'.
Proof.
  induction n; intros.
  - inv LISTS; simpl in *; allinv.
    constructor; auto.

  - inv LISTS.
    simpl in *; allinv.
    simpl in *.
    repeat match goal with
             | H : (match ?b with _ => _ end) = Some _ |- _ =>
               destruct b eqn:?; simpl in *; try congruence
           end;
    allinv.
    constructor; eauto.
Qed.

(* TODO: Refactor and move *)
Lemma update_list_low : forall o n m1 m2 a1 a2 m1' m2',
  Forall2 (@low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list n a1 m1 = Some m1' ->
  update_list n a2 m2 = Some m2' ->
  Forall2 (low_equiv_atom o) m1' m2'.
Proof.
  induction n ; intros.
  inv H; simpl in *; allinv.
  constructor ; auto.

  inv H.
  simpl in *; allinv.
  simpl in H2, H1.
  case_eq (update_list n a2 l') ; case_eq (update_list n a1 l) ; intros;
    rewrite H in * ; rewrite H5 in * ; allinv.
  constructor ; eauto.
Qed.

(* TODO: Refactor and move *)
Lemma update_list_Z_low : forall o n m1 m2 a1 a2 m1' m2',
  Forall2 (@low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list_Z n a1 m1 = Some m1' ->
  update_list_Z n a2 m2 = Some m2' ->
  Forall2 (low_equiv_atom o) m1' m2'.
Proof.
  intros. eapply update_list_low; eauto.
  eapply update_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.

Lemma Forall2_update_Z: forall o a1 a2 a1l a2l o1 o1l o2 o2l m1 m2 m1' m2' v1 v1l v2 v2l,
    low_equiv_atom o (Vint a1@a1l) (Vint a2@a2l) ->
    Forall2 (low_equiv_atom o) m1 m2 ->
    index_list_Z a1 m1 = Some (o1@o1l) ->
    index_list_Z a2 m2 = Some (o2@o2l) ->
     a1l <: o1l = true ->
     a2l <: o2l = true ->
    low_equiv_atom o (v1@v1l) (v2@v2l) ->
    update_list_Z a1 (v1@join a1l v1l) m1 = Some m1' ->
    update_list_Z a2 (v2@join a2l v2l) m2 = Some m2' ->
    Forall2 (low_equiv_atom o) m1' m2'.
Proof.
Admitted.
(*  intros.
  inv H; inv H5.

  eapply (@update_list_Z_low o) ; eauto.

  eapply update_list_Z_low with (3:= H6) (4:= H7) ; eauto.
  econstructor 2; eauto with lat.

  assert (Forall2 (low_equiv_atom o) m1' m1).
  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  eapply update_list_Z_high with (5:= H1); eauto.
  destruct (flows o1l o) eqn:?; auto.
  assert (flows a2l o = true); eauto with lat.

  assert (Forall2 (low_equiv_atom o) m1' m2).
  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  exploit (@update_list_Z_spec Atom (v2 @ a1l \_/ v2l)) ; eauto. intros HH.
  assert (Forall2 (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto.
  destruct (flows o2l o) eqn:?; auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; auto.

  assert (a1l \_/ v1l <: o = false) by eauto with lat.
  assert (Forall2 (low_equiv_atom o) m1' m1).
  eapply update_list_Z_high with (4:= H1); eauto.
  destruct (flows o1l o) eqn:?; auto.
  assert (flows a1l o = true); eauto with lat.

  exploit (@update_list_Z_spec Atom (v1@a1l \_/ v1l)) ; eauto. intros HH.
  assert (Forall2 (low_equiv_atom o) m1' m2).
  etransitivity ; eauto.

  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  assert (Forall2 (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto.
  destruct (flows o2l o) eqn:?; auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; eauto.
Qed.
*)
(*
Lemma update_high_low_equiv: forall o addr m v l l' v' m',
  index_list addr m = Some (v@l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list addr (v'@l') m = Some m' ->
  Forall2 (@low_equiv_atom o) m m'.
Proof.
  induction addr; intros.
  destruct m ; simpl in *; allinv.
  constructor ; eauto.
  constructor 2; auto with lat.
  destruct (flows l' o) eqn:?; auto.
  assert (flows l o = true); eauto with lat.

  destruct m ; simpl in *; allinv.
  remember (update_list addr (v'@l') m) as up.
  destruct up; allinv.
  constructor; eauto.
Qed.

Lemma update_Z_high_low_equiv: forall o addr m v l l' v' m',
  index_list_Z addr m = Some (v@l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list_Z addr (v'@l') m = Some m' ->
  Forall2 (@low_equiv_atom o) m m'.
Proof.
  intros. eapply update_high_low_equiv; eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.
*)
(* TODO: Stacks.. *
Fixpoint below_lret (o: Label) (stk: list (StkElmt Label Label)) : list (StkElmt Label Label) :=
  match stk with
    | nil => nil
    | (ARet (_,l) _)::stk' =>
      match flows l o with
        | true => stk
        | false => below_lret o stk'
      end
    | _::stk' => below_lret o stk'
  end.

Lemma below_lret_low_equiv : forall o l1 l2,
  Forall2 (low_equiv_stkelt o) l1 l2 ->
  Forall2 (low_equiv_stkelt o) (below_lret o l1) (below_lret o l2).
Proof.
  induction 1; intros.
  simpl ; auto.
  inv H; (simpl; auto).
  inv LEa; (rewrite H in *; auto).
  rewrite H1 ; auto.
Qed.

Lemma below_lret_adata : forall o l l',
  (forall d, In d l -> exists a : Atom _ _, d = AData a) ->
  below_lret o (l ++ l') = below_lret o l'.
Proof.
  induction l; intros.
  simpl; auto.
  destruct a. simpl ; auto. eapply IHl ; eauto.
  intros. eapply H ; eauto. constructor 2 ; auto.

  eelim (H (ARet p b)); intros.
  congruence.
  constructor ; auto.
Qed.
*)
Global Instance declare_equiv_option {A} (R:relation A) `{Equivalence A R} : @Equivalence (option A) (match_options R).
Proof.
  constructor.
  - intros [x|]; repeat constructor.
    reflexivity.
  - intros [x|] [y|]; intros H1 ; inv H1; constructor.
    symmetry; auto.
  - intros [x|] [y|] [z|]; intros H1 H2; inv H1; inv H2; constructor.
    transitivity y; auto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- match_options _ _ _ => reflexivity
  end.

Definition low_equiv_frame (o : Label) : relation frame :=
  fun f1 f2 =>
    match f1, f2 with
      | Fr st1 lab1 d1, Fr st2 lab2 d2 =>

        Forall2 (low_equiv_atom o))
                    (Mem.get_frame m1 b) (Mem.get_frame m2 b) )

        Forall2

(* Low-equivalent memories:
   (1) low-equivalence of frames pointed to by low blocks
   (2) allocating a low frame in them results in the same block
     DD -> DP : I understand this as "low allocation history is the same"
*)
Definition equiv_mem (o:Label) : relation memory :=
  fun m1 m2 =>
    (forall b,
      Mem.stamp b <: o = true ->
       (match_frames (low_equiv_atom o)
                    (Mem.get_frame m1 b) (Mem.get_frame m2 b)) /\
      (forall lbl fr,
         lbl <: o = true ->
                fst (Mem.alloc Local m1 lbl fr) = fst (Mem.alloc Local m2 lbl fr))).

Global Instance declare_equiv_mem (o:Label): @Equivalence (memory Label Label) (equiv_mem o).
Proof.
  constructor.
  - intros m; split; reflexivity.
  - intros m1 m2 [H H']; split.
    + intros b Hb; symmetry; auto.
    + intros; symmetry; auto.
  - intros m1 m2 m3 H1 H2.
    destruct H1; destruct H2; split; intros.
    + transitivity (Mem.get_frame m2 b); auto.
    + rewrite H0; auto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- equiv_mem _ _ _ => reflexivity
  end.


Lemma load_equiv_mem:
  forall o p m1 m2 v1 v2,
    equiv_mem o m1 m2 ->
    Mem.stamp (fst p) <: o = true ->
    load p m1 = Some v1 ->
    load p m2 = Some v2 ->
    low_equiv_atom o v1 v2.
Proof.
  intros o [b ofs] m1 m2 v1 v2 [H _] Hs H0 H1.
  unfold load in *. simpl in *.
  assert (T:=H b Hs); inv T.
  - rewrite <- H3 in *; congruence.
  - rewrite <- H2 in *.
    rewrite <- H3 in *.
    eapply index_list_Z_low_eq; eauto.
Qed.

Lemma store_equiv_mem:
  forall o m1 m2 p1 p2 pcl l1 l2 v1 v2 ll1 ll2 o1 o2 lll1 lll2 m1' m2',
  equiv_mem o m1 m2 ->
  Mem.stamp (fst p1) <: l1 = true ->
  Mem.stamp (fst p2) <: l2 = true ->
  low_equiv_atom o (Vptr p1, l1) (Vptr p2, l2) ->
  load p1 m1 = Some (o1,ll1) ->
  load p2 m2 = Some (o2,ll2) ->
  pcl <: o = true ->
  l1 <: ll1 = true ->
  l2 <: ll2 = true ->
  low_equiv_atom o (v1, lll1) (v2, lll2) ->
  store p1 (v1, join l1 lll1) m1 = Some m1' ->
  store p2 (v2, join l2 lll2) m2 = Some m2' ->
  equiv_mem o m1' m2'.
Proof.
  intros o m1 m2 [b1 ofs1] [b2 ofs2] pcl l1 l2 v1 v2 ll1 ll2 o1 o2 lll1 lll2 m1' m2'.
  intros [H H'] Hs1 Hs2 H0 H1 H2 Hlow H3 H4 H5 H6 H7. simpl in *.
  split.
  + { intros b Hb.
      unfold load, store in *. simpl in *.
      inv H0.
      - assert (Hs2': Mem.stamp b2 <: o = true) by (eauto with lat).
        generalize (H b2 Hs2'); intros T; inv T.
        * rewrite <- H8 in *; rewrite <- H10 in *; try congruence.
        * unfold Atom in *.
          repeat rewrite <- H8 in *; repeat rewrite <- H0 in *.
          repeat match goal with
                   | id: match ?o with | Some _ => _ | None => None end = Some _ |- _ =>
                     destruct o eqn:?E;[idtac|congruence]
                 end.
          rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H7).
          rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H6).
          destruct (equiv_dec b2 b) as [Eb|Eb].
          + constructor.
            eapply Forall2_update_Z with (8:= E) (9:= E0); eauto.
          + auto.
      - unfold Atom in *.
        destruct (Mem.get_frame (A:=val _*Label) m1 b1) eqn:E1; try congruence.
        destruct (Mem.get_frame (A:=val _*Label) m2 b2) eqn:E2; try congruence.
        repeat match goal with
                 | id: match ?o with | Some _ => _ | None => None end = Some _ |- _ =>
                   destruct o eqn:?E;[idtac|congruence]
               end.
        rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H6).
        rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H7).
        destruct (equiv_dec b1 b);
          destruct (equiv_dec b2 b); subst.
        + constructor.
          eapply Forall2_update_Z with (8:= E0) (9:= E); eauto.
          inv e; inv e0.
          generalize (H b Hb); unfold Atom; rewrite E2; rewrite E1.
          intros T; inv T; auto.
        + inv e.
          transitivity (Mem.get_frame m1 b); auto.
          unfold Atom; rewrite E1.
          constructor.
          eapply update_list_Z_high with (4:=H1) (5:=E0); auto with lat.
          case_eq (ll1 <: o); auto.
          intros; assert (l1 <: o = true) by (eauto with lat).
          congruence.
        + inv e.
          transitivity (Mem.get_frame m2 b); auto.
          unfold Atom; rewrite E2.
          constructor.
          symmetry.
          eapply update_list_Z_high with (4:=H2) (5:=E); auto with lat.
          case_eq (ll2 <: o); auto.
          intros; assert (l2 <: o = true) by (eauto with lat).
          congruence. (* TODO : make a lattice lemma *)
        + auto.
    }
  + intros.
    unfold store in *.
    repeat match goal with
             | id: match ?o with | Some _ => _ | None => None end = Some _ |- _ =>
               destruct o eqn:?E;[idtac|congruence]
           end.
    erewrite (Mem.alloc_upd _ _ _ Local m1); eauto.
    symmetry.
    erewrite (Mem.alloc_upd _ _ _ Local m2); eauto.
    symmetry.
    apply H'; auto.
Qed.

Lemma store_high_equiv_mem: forall o m1 m2 l1 l2 o1 v p,
  l1 <: o = false ->
  l2 <: o = false ->
  load p m1 = Some (o1, l1) ->
  store p (v, l2) m1 = Some m2 ->
  equiv_mem o m1 m2.
Proof.
  unfold load, store; intros. destruct p as [b ofs]. simpl in *.
  destruct (Mem.get_frame m1 b) eqn:E1; try congruence.
  unfold Atom in *.
  destruct (update_list_Z ofs (v,l2) l) eqn:E2; try congruence.
  split.
  + intros b0 Hb.
    rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H2).
    destruct (equiv_dec b).
    - inv e.
      unfold Atom; rewrite E1; constructor.
      symmetry.
      eapply update_list_Z_high with (4:=H1) (5:=E2); eauto.
    - auto.
  + intros lbl fr Hl.
    symmetry.
    eapply (Mem.alloc_upd _ _ _ Local m1); eauto.
Qed.

Inductive low_equiv_full_state (o: Label) : @a_state Label -> @a_state Label -> Prop :=
| low_equiv_high:
  forall l1 l2 m1 m2 i stk1 stk2 pcv1 pcv2
    (Flowl1: l1 <: o = false)
    (Flowl2: l2 <: o = false)
    (LEm : equiv_mem o m1 m2)
    (LEsH : Forall2 (low_equiv_stkelt o) (below_lret o stk1) (below_lret o stk2)),
    low_equiv_full_state o
      (AState m1 i stk1 (pcv1,l1))
      (AState m2 i stk2 (pcv2,l2))
| low_equiv_low:
  forall l m1 m2 i stk1 stk2 pcv
    (Flowl: l <: o = true)
    (LEm : equiv_mem o m1 m2)
    (LEs : Forall2 (low_equiv_stkelt o) stk1 stk2),
    low_equiv_full_state o
      (AState m1 i stk1 (pcv,l))
      (AState m2 i stk2 (pcv,l)).
Hint Constructors low_equiv_full_state.

Global Instance low_state (o: Label) : @Equivalence (@a_state Label) (@low_equiv_full_state o).
Proof.
  constructor.
  (* reflexive *) intros x. destruct x. destruct apc.
  destruct (flows l o) eqn:?; auto.
  intros s s' Hss'.  inv Hss'.
  (constructor; eauto); symmetry ; eauto.
  (constructor 2; eauto) ; symmetry; eauto.
  (* transitive *)
  intros s s' s'' Hss' Hs's''.
  inv Hss' ; inv Hs's''.
  (constructor ; eauto); etransitivity; eauto.
  (constructor ; eauto); etransitivity; eauto.
  apply below_lret_low_equiv; auto.
  (constructor ; eauto); etransitivity; eauto.
  apply below_lret_low_equiv in LEs; auto.
  etransitivity; eauto.
  (constructor 2 ; eauto); etransitivity; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_full_state _ _ _ => reflexivity
  end.

Lemma pc_labels1 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s1 ->
  low_pc o s2.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma pc_labels2 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  low_pc o s1.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma index_list_low_equiv_some: forall (A: Type) (R: relation A) n e l l',
  Forall2 R l l' ->
  index_list n l = None ->
  index_list n l' = Some e ->
  False.
Proof.
  induction n ; intros.
  destruct l' ; inv H ; simpl in *; try congruence.
  destruct l' ; inv H ; simpl in * ; try congruence.
  eapply IHn ; eauto.
Qed.

Lemma index_list_Z_low_equiv_some: forall (A: Type) (R: relation A) n e l l',
  Forall2 R l l' ->
  index_list_Z n l = None ->
  index_list_Z n l' = Some e ->
  False.
Proof.
  unfold index_list_Z. intros.
  destruct (n <? 0)%Z. congruence.
  eapply index_list_low_equiv_some; eauto.
Qed.


Inductive visible_event (o : Label) : @Event Label -> Prop :=
| ve_low : forall i l, l <: o = true -> visible_event o (EInt (i, l)).
Hint Constructors visible_event.

Lemma visible_event_dec : forall o e, {visible_event o e} + {~ visible_event o e}.
Proof.
  intros o [[x l]].
  destruct (l <: o) eqn: Hl; auto.
  right. intros H. inv H. congruence.
Defined.

End ObsEquiv.

Hint Resolve low_state.

Hint Constructors
  low_equiv_atom
  low_equiv_stkelt
  Forall2
  low_equiv_full_state.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_atom _ _ _ => reflexivity
    | |- low_equiv_stkelt _ _ _ => reflexivity
    | |- Forall2 _ _ _ => reflexivity
    | |- equiv_mem _ _ _ => reflexivity
    | |- low_equiv_full_state _ _ _ => reflexivity
  end.

(** * Non-interference property *)

(** Instantiating the generic lockstep non-interference property for
    our particular abstract machine *)

Section ParamMachine.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

Variable atable : ASysTable T.

Ltac exploit_low :=
    repeat match goal with
        | [H: Forall2 _ (_::_) (_::_) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (AData _) (AData _) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (ARet _ _) (ARet _ _) |- _ ] => inv H
    end.

Ltac spec_pop_return :=
  (exploit @pop_to_return_spec; eauto);
  let stk := fresh "stk" in
  let Hstk := fresh "Hstk" in
  (intros [? [? [? [? [Hstk ?]]]]]);
  match type of Hstk with
    | ?aastk = _ =>
      match goal with
        | [HH: pop_to_return aastk _ |- _ ] => (subst ; move_to_top HH)
      end
  end.

Inductive abstract_i_equiv (o : T) : relation (abstract_init_data T) :=
  | ai_equiv : forall p d1 d2 b
                      (STK : Forall2 (low_equiv_atom o) d1 d2),
                 abstract_i_equiv o (p,d1,b) (p,d2,b).

Global Program Instance AMObservation : TINI.Observation (abstract_machine atable) (Event T) := {
  out e := e;
  e_low := visible_event;
  e_low_dec := visible_event_dec;
  i_equiv := abstract_i_equiv
}.

Lemma low_equiv_step_pop_to_return: forall o  stk1 stk2,
  Forall2 (low_equiv_stkelt o) stk1 stk2 ->
  forall  rstk1 rstk2 ,
    pop_to_return stk1 rstk1 ->
    pop_to_return stk2 rstk2 ->
    Forall2 (low_equiv_stkelt o) rstk1 rstk2.
Proof.
  induction 1; intros.
  - invh @pop_to_return.
  - invh @pop_to_return.
    + invh @pop_to_return; eauto.
      invh low_equiv_stkelt.
    + invh (pop_to_return (x::l)); eauto.
      invh low_equiv_stkelt.
Qed.

Section fix_observer.
Variable o : T.
Notation "'<<' m i s pc '>>'" := (AState m i s pc).
Notation "m1 '~~m' m2" := (equiv_mem o m1 m2) (at level 20).
Notation "s1 '~~l' s2" := (Forall2 (low_equiv_stkelt o) s1 s2) (at level 20).
Notation "a1 '~~a' a2" := (low_equiv_atom o a1 a2) (at level 20).

Arguments low_pc {Label Latt} o s /.

Definition syscall_lowstep (SysTable:ASysTable T) := forall id sys_info,
  SysTable id = Some sys_info ->
  forall args1 args2 res1 res2,
    map AData args1 ~~l map AData args2 ->
    asi_sem sys_info args1 = Some res1 ->
    asi_sem sys_info args2 = Some res2 ->
    res1 ~~a res2.

Variable hyp_syscall_lowstep : syscall_lowstep atable.

Local Ltac go :=
  try congruence;
  try omega;
  auto using below_lret_low_equiv with lat;
  try apply below_lret_low_equiv;
  constructor (go).

Local Ltac inv_equiv_atom :=
 match goal with
   | h: (_,_) ~~a (_,_) |- _ => inv h; simpl in *
  end.

Lemma a_alloc_high_step: forall size1 l1 a1 m1 b1 m1',
  a_alloc size1 l1 a1 m1 = Some (b1, m1') ->
  l1 <: o = false ->
  m1 ~~m m1'.
Proof.
  unfold a_alloc, alloc; intros size1 l1 a1 m1 b1 m1' H H0.
  destruct (zreplicate size1 a1) eqn:Ez1; try congruence; inv H.
  split.
  - intros b Hb.
    rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H2).
    destruct (equiv_dec b1).
    + inv e.
      rewrite <- (Mem.alloc_stamp _ _ _ _ _ _ _ _ _ H2) in *.
      congruence.
    + reflexivity.
  - intros lbl fr Hf.
    destruct (Mem.alloc Local m1' lbl fr) as [b1' m1''] eqn:E1.
    destruct (Mem.alloc Local m1 lbl fr) as [b2 m2] eqn:E2.
    simpl.
    eapply (Mem.alloc_local_comm _ _ _ m1 m1' m1'' m2 m1); eauto.
    congruence.
Qed.

Lemma a_alloc_high: forall size1 l1 a1 m1 b1 m1' size2 l2 a2 m2 b2 m2',
  m1 ~~m m2 ->
  a_alloc size1 l1 a1 m1 = Some (b1, m1') ->
  a_alloc size2 l2 a2 m2 = Some (b2, m2') ->
  l1 <: o = false ->
  l2 <: o = false ->
  m1' ~~m m2'.
Proof.
  unfold a_alloc, alloc; intros size1 l1 a1 m1 b1 m1' size2 l2 a2 m2 b2 m2' H H0 H1 H2 H3.
  destruct (zreplicate size1 a1) eqn:Ez1; try congruence; inv H0.
  destruct (zreplicate size2 a2) eqn:Ez2; try congruence; inv H1.
  split.
  * intros b Hb.
    rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H5).
    rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H4).
    destruct (equiv_dec b1).
    - inv e.
      rewrite <- (Mem.alloc_stamp _ _ _ _ _ _ _ _ _ H5) in *.
      congruence.
    - destruct (equiv_dec b2).
      + inv e.
        rewrite <- (Mem.alloc_stamp _ _ _ _ _ _ _ _ _ H4) in *.
        congruence.
      + destruct H; auto.
  * intros lbl fr Hf.
    destruct (Mem.alloc Local m1' lbl fr) as [b3 m1''] eqn:T1.
    destruct (Mem.alloc Local m2' lbl fr) as [b4 m2''] eqn:T2.
    simpl.
    destruct (Mem.alloc Local m1 lbl fr) as [b5 m1'''] eqn:T3.
    assert (b5=b3).
      eapply (Mem.alloc_local_comm _ _ _ m1 m1' m1'' m1''' m1); eauto.
      congruence.
    destruct (Mem.alloc Local m2 lbl fr) as [b6 m2'''] eqn:T4.
    assert (b6=b4).
      eapply (Mem.alloc_local_comm _ _ _ m2 m2' m2'' m2''' m2); eauto.
      congruence.
    destruct H as [ _ H].
    generalize (H _ fr Hf).
    rewrite T3; rewrite T4; simpl; congruence.
Qed.

Lemma a_alloc_loc_same_block: forall size l a1 m1 b1 m1' a2 m2 b2 m2',
  m1 ~~m m2 ->
  a_alloc size l a1 m1 = Some (b1, m1') ->
  a_alloc size l a2 m2 = Some (b2, m2') ->
  l <: o = true ->
  b1 = b2.
Proof.
  unfold a_alloc, alloc; intros size l a1 m1 b1 m1' a2 m2 b2 m2' H H0 H1 H2.
  destruct (zreplicate size a1) eqn:Ez1; try congruence; inv H0.
  destruct (zreplicate size a2) eqn:Ez2; try congruence; inv H1.
  destruct H as [_ H].
  generalize (Mem.alloc_next_block_no_fr _ _ _ m1 l l0 l1).
  rewrite H4; simpl; intros.
  generalize (H l l1 H2).
  rewrite H3; rewrite <- H0; auto.
Qed.

Lemma low_equiv_replicate: forall (a1 a2:Atom T T),
  a1 ~~a a2 -> forall size,
  Forall2 (low_equiv_atom o)
          (replicate size a1) (replicate size a2).
Proof.
  induction size; constructor; auto.
Qed.

Lemma low_equiv_zreplicate: forall size (a1 a2:Atom T T),
  a1 ~~a a2 ->
  match_options (Forall2 (low_equiv_atom o))
                (zreplicate size a1) (zreplicate size a2).
Proof.
  unfold zreplicate; intros.
  destruct Z_lt_dec; constructor.
  apply low_equiv_replicate; auto.
Qed.

Lemma a_alloc_loc: forall size l a1 m1 b1 m1' a2 m2 b2 m2',
  m1 ~~m m2 ->
  a1 ~~a a2 ->
  a_alloc size l a1 m1 = Some (b1, m1') ->
  a_alloc size l a2 m2 = Some (b2, m2') ->
  l <: o = true ->
  m1' ~~m m2'.
Proof.
  unfold a_alloc, alloc; intros size l a1 m1 b1 m1' a2 m2 b2 m2' H Ha H0 H1 H2.
  assert (b1 = b2) by (eapply a_alloc_loc_same_block; eauto).
  subst.
  unfold Atom in *; destruct (zreplicate size a1) eqn:Ez1; try congruence; inv H0.
  destruct (zreplicate size a2) eqn:Ez2; try congruence; inv H1.
  split.
  * intros b Hb.
    rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H4).
    rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H3).
    destruct (equiv_dec b2).
    - inv e.
      unfold Atom in *.
      rewrite <- Ez1; rewrite <- Ez2.
      apply low_equiv_zreplicate; auto.
    - destruct H; auto.
  * intros lbl fr Hf.
    destruct (lbl == l).
    - inv e.
      eapply Mem.alloc2_local; eauto.
    - destruct (Mem.alloc Local m1' lbl fr) as [b1' m1''] eqn:E1.
      destruct (Mem.alloc Local m2' lbl fr) as [b2' m2''] eqn:E2.
      simpl.
      destruct (Mem.alloc Local m1 lbl fr) as [b1'' m1'''] eqn:E1'.
      destruct (Mem.alloc Local m2 lbl fr) as [b2'' m2'''] eqn:E2'.
      assert (b2'' = b2').
      eapply Mem.alloc_local_comm with (3:=H3) (4:=E2) (5:=E2'); eauto.
      assert (b1'' = b1').
      eapply Mem.alloc_local_comm with (3:=H4) (4:=E1) (5:=E1'); eauto.
      destruct H.
      generalize (H5 lbl fr Hf).
      rewrite E1'; rewrite E2'.
      simpl; congruence.
Qed.

Definition inv_atom (a:Atom T T) (guard:T) : Prop :=
  match a with
    | (Vint _,_) => True
    | (Vptr p, l) => Mem.stamp (fst p) <: l \_/ guard = true
  end.

Lemma inv_atom_weaken :
  forall v lv l lv' l',
    inv_atom (v, lv) l ->
    lv \_/ l <: lv' \_/ l' = true ->
    inv_atom (v, lv') l'.
Proof.
  intros [?|[b off]]; simpl; auto.
  intros.
  eapply flows_trans; eauto.
Qed.

Definition inv_mem m : Prop :=
  forall p a, load p m = Some a -> inv_atom a (Mem.stamp (fst p)).

Inductive inv_stk : list (StkElmt T T) -> T -> Prop :=
| istk_nil : forall lpc, inv_stk nil lpc
| istk_data : forall a stk lpc
                     (STK : inv_stk stk lpc)
                     (ATOM : inv_atom a lpc),
                inv_stk (AData a :: stk) lpc
| istk_ret : forall pc b stk lpc
                    (STK : inv_stk stk (snd pc)),
               inv_stk (ARet pc b :: stk) lpc.

Lemma inv_stk_weaken :
  forall stk l l',
    inv_stk stk l ->
    l <: l' = true ->
    inv_stk stk l'.
Proof.
  intros.
  induction H; constructor; eauto using inv_atom_weaken.
  destruct a.
  eapply inv_atom_weaken; eauto 2; auto with lat.
Qed.

Lemma inv_stk_pop_to_return :
  forall stk pcv pcl b pcl' stk',
    inv_stk stk pcl' ->
    pop_to_return stk (ARet (pcv, pcl) b :: stk') ->
    inv_stk stk' pcl.
Proof.
  intros stk pcv pcl b pcl' stk' H1 H2.
  induction stk as [|[a|pc' b'] stk IH].
  - inv H2.
  - inv H1. inv H2. auto.
  - inv H1. inv H2. auto.
Qed.

Inductive inv_state : @a_state T -> Prop :=
| inv_state_def: forall m i s pc lpc
    (IMEM: inv_mem m)
    (ISTACK: inv_stk s lpc),
    inv_state (AState m i s (pc,lpc)).

Definition systable_inv (table : ASysTable T) : Prop :=
  forall id args sc res lpc
         (SYS : table id = Some sc)
         (IARGS : forall a, In a args -> inv_atom a lpc)
         (RES : sc.(asi_sem) args = Some res),
    inv_atom res lpc.

Hypothesis table_systable_inv : systable_inv atable.

Lemma inv_add : forall xv1 xl1 xv2 xl2 lpc xr,
                  add xv1 xv2 = Some xr ->
                  inv_atom (xv1, xl1) lpc ->
                  inv_atom (xv2, xl2) lpc ->
                  inv_atom (xr, xl1 \_/ xl2) lpc.
Proof.
  intros xv1 xl1 xv2 xl2 lpc xr H1 H2 H3.
  destruct xv1 as [xv1|[b1 off1]], xv2 as [xv2|[b2 off2]]; simpl in *;
  inv H1; trivial; simpl.
  - rewrite <- join_assoc. auto with lat.
  - rewrite (join_comm xl1). rewrite <- join_assoc. auto with lat.
Qed.

Lemma inv_sub : forall xv1 xl1 xv2 xl2 lpc xr,
                  sub xv1 xv2 = Some xr ->
                  inv_atom (xv1, xl1) lpc ->
                  inv_atom (xv2, xl2) lpc ->
                  inv_atom (xr, xl1 \_/ xl2) lpc.
Proof.
  intros xv1 xl1 xv2 xl2 lpc xr H1 H2 H3.
  destruct xv1 as [xv1|[b1 off1]], xv2 as [xv2|[b2 off2]]; simpl in *;
  inv H1; trivial; simpl.
  - rewrite (join_comm xl1). rewrite <- join_assoc. auto with lat.
  - match goal with
      | H : (if ?B then _ else _) = Some _ |- _ =>
        destruct B as [E|_]; inv H; compute in E; subst b2
    end.
    rewrite <- (join_refl lpc).
    rewrite <- join_assoc. rewrite (join_assoc xl2).
    rewrite (join_comm _ lpc).
    rewrite join_assoc.
    auto with lat.
Qed.

Lemma inv_alloc_mem :
  forall size sizel pcl a m b m'
         (ALLOC : a_alloc size (sizel \_/ pcl) a m = Some (b, m'))
         (ATOM : inv_atom a pcl)
         (MEM : inv_mem m),
    inv_mem m'.
Proof.
  intros.
  intros [b' off] a' LOAD. unfold a_alloc in ALLOC. simpl.
  erewrite load_alloc in LOAD; eauto.
  repeat match goal with
           | H : (if ?B then _ else _) = Some _ |- _ =>
             destruct B as [E|_] || destruct B; try solve [inv H]
         end.
  - compute in E. subst b'. inv LOAD.
    unfold alloc in ALLOC.
    destruct (zreplicate size a'); try discriminate.
    inv ALLOC.
    assert (STAMP : Mem.stamp b = sizel \_/ pcl) by eauto using Mem.alloc_stamp.
    rewrite STAMP. clear STAMP.
    destruct a' as [v' l']. clear - ATOM.
    eapply inv_atom_weaken; eauto 2.
    rewrite join_assoc. rewrite (join_comm l' sizel). rewrite <- join_assoc.
    auto with lat.
  - eapply MEM in LOAD. eauto.
Qed.

Lemma inv_alloc_res :
  forall size (sizel pcl : T) a m b m'
         (ALLOC : a_alloc size (sizel \_/ pcl) a m = Some (b, m')),
    inv_atom (Vptr (b, 0)%Z, sizel) pcl.
Proof.
  intros.
  unfold a_alloc, alloc in ALLOC.
  destruct (zreplicate size a); try discriminate.
  simpl. inv ALLOC.
  assert (E : Mem.stamp b = sizel \_/ pcl) by eauto using Mem.alloc_stamp.
  rewrite E. auto with lat.
Qed.

Lemma inv_store :
  forall p addrl xv xl pcl m m',
    inv_mem m ->
    inv_atom (xv, xl) pcl ->
    store p (xv, addrl \_/ pcl \_/ xl) m = Some m' ->
    inv_mem m'.
Proof.
  intros p addrl xv xl pcl m m' H1 H3 H4 p' a LOAD.
  erewrite load_store in LOAD; eauto.
  destruct (equiv_dec p p') as [E | E].
  - compute in E. subst p'. inv LOAD.
    eapply inv_atom_weaken; eauto 2. auto with lat.
  - apply H1. trivial.
Qed.

Lemma inv_stk_inv :
  forall s1 s2 pcl
         (DATA : forall se, In se s1 -> exists a, se = AData a)
         (INV : inv_stk (s1 ++ s2) pcl),
    (forall se, In se s1 -> exists a, se = AData a /\ inv_atom a pcl) /\
    inv_stk s2 pcl.
Proof.
  intros s1 s2 pcl DATA INV.
  induction s1 as [|se s1 IH]; simpl in *.
  - split; trivial.
    intuition.
  - inv INV; eauto.
    + exploit IH; eauto.
      intros [H1 H2].
      split; intuition eauto.
    + specialize (DATA _ (or_introl eq_refl)). destruct DATA. congruence.
Qed.

Lemma inv_stk_app :
  forall s1 s2 pcl
         (INV1 : forall se, In se s1 -> exists a, se = AData a /\ inv_atom a pcl)
         (INV2 : inv_stk s2 pcl),
    inv_stk (s1 ++ s2) pcl.
Proof.
  intros.
  induction s1 as [|se s1 IH]; simpl; trivial.
  exploit IH.
  { intros. apply INV1. intuition. }
  intros H.
  specialize (INV1 _ (or_introl eq_refl)).
  destruct INV1 as (? & ? & ?). subst.
  constructor; eauto.
Qed.

Lemma inv_step : forall as1 e as1',
  inv_state as1 ->
  a_step atable as1 e as1' ->
  inv_state as1'.
Proof.
  intros as1 e as1' Hi Hs.
  inv Hs; inv Hi; constructor;
  try assumption;
  repeat match goal with
           | H : inv_stk (_ :: _) _ |- _ => inv H
         end;
  try match goal with
        | |- inv_stk _ _ => constructor
      end;
  eauto using inv_add, inv_sub, inv_alloc_mem, inv_alloc_res,
              inv_store, inv_stk_weaken, inv_stk_pop_to_return,
              inv_atom_weaken;
  try solve [simpl; auto];
  try (exploit IMEM; [solve [eauto]|]).
  - apply index_list_In in IDX.
    eapply inv_stk_inv in DATA; eauto.
    destruct DATA as [H1 H2].
    edestruct H1 as (? & ? & ?); eauto. subst.
    constructor; eauto.
  - eapply inv_stk_inv in DATA; eauto.
    destruct DATA as [DATA INV].
    eapply inv_stk_app; eauto.
    eapply swap_forall; eauto.
  - simpl in ATOM. clear - ATOM. intros H.
    eapply inv_atom_weaken; eauto 2.
    rewrite (join_comm addrl). rewrite <- join_assoc.
    auto with lat.
  - eapply inv_stk_inv in ARGS; eauto.
    destruct ARGS as [ARGS INV].
    eapply inv_stk_app.
    + intros se IN. apply ARGS in IN.
      destruct IN as (a & ? & INV'). subst.
      eexists a. split; trivial.
      rewrite (surjective_pairing a) in *.
      eapply inv_atom_weaken in INV'; eauto.
      auto with lat.
    + constructor. eauto.
  - eapply inv_stk_inv in ISTACK; intuition eauto.
    rewrite in_map_iff in H. destruct H as (? & ? & ?). subst. eauto.
  - eapply table_systable_inv; eauto.
    clear - ISTACK.
    intros a H.
    induction args as [|a' args IH]; simpl in *; intuition; subst;
    inv ISTACK; auto.
Qed.

Lemma swap_low_equiv :
  forall T (R : T -> T -> Prop) n (l1 l1' l2 l2' : list T)
         (SWAP1 : swap n l1 = Some l1')
         (SWAP2 : swap n l2 = Some l2')
         (LEQUIV : Forall2 R l1 l2),
    Forall2 R l1' l2'.
Proof.
  unfold swap.
  intros.
  destruct l1 as [|y1 l1]; try congruence.
  destruct l2 as [|y2 l2]; try congruence.
  destruct (index_list n (y1 :: l1)) as [x1|] eqn:IDX1; try congruence.
  destruct (index_list n (y2 :: l2)) as [x2|] eqn:IDX2; try congruence.
  destruct n as [|n]; simpl in *; allinv; auto.
  inv LEQUIV.
  repeat match goal with
           | H : (match ?b with _ => _ end) = Some _ |- _ =>
             destruct b eqn:?; simpl in *; try congruence
         end;
  allinv.
  constructor.
  - eapply index_list_low_eq; eauto.
  - eapply update_list_low_gen; eauto.
Qed.

Lemma lowstep : forall as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  a_step atable as1 e as1' ->
  a_step atable as2 e' as2' ->
  inv_state as1 ->
  inv_state as2 ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros as1 e as1' as2 e' as2' He Hpc Hs1 Hs2 Hi1 Hi2.
  inv He. inv Hpc; congruence.

  inv Hs1; inv Hs2; try congruence;
  match goal with
    | H1 : ?x = _,
      H2 : ?x = _ |- _ =>
      rewrite H1 in H2; inv H2
  end;

  exploit_low; try (repeat inv_equiv_atom; go).

  - Case "Add".
    assert (Hmemv: low_equiv_atom o (xv, x1l \_/ x2l) (xv0, x1l0 \_/ x2l0)) by
      (eapply low_equiv_atom_binop_value; eauto).
    inv Hmemv; go.

  - Case "Sub".
    assert (Hmemv: low_equiv_atom o (xv, x1l \_/ x2l) (xv0, x1l0 \_/ x2l0)) by
      (eapply low_equiv_atom_binop_value; eauto).
    inv Hmemv; go.

  - Case "Dup".
    eapply low_equiv_low; eauto.
    constructor; auto.
    exploit index_list_low_eq; eauto using index_list_app.

  - Case "Swap".
    eapply low_equiv_low; eauto.
    clear DATA DATA0 INSTR Hi1 Hi2 Hpc.
    eapply swap_app with (l2 := s3) in SWAP0.
    eapply swap_app with (l2 := s2) in SWAP.
    eapply swap_low_equiv; eauto.

  - Case "Alloc".
    assert (m' ~~m m'0).
    + inv_equiv_atom.
      * eapply a_alloc_loc with (3:=ALLOC) (4:=ALLOC0); eauto with lat.
      * eapply a_alloc_high; eauto with lat.
    + inv_equiv_atom; try go.
      assert (b=b0).
      * eapply a_alloc_loc_same_block with (2:=ALLOC) (3:=ALLOC0); eauto with lat.
      * subst.
        go.

  - Case "Load".
    inv_equiv_atom; try go.
    SCase "Load from low addresses".
    assert (Mem.stamp (fst p0) <: addrl0 \_/ l = true).
    { inv Hi2. inv ISTACK. simpl in *. trivial. }
    assert (Hmemv: low_equiv_atom o (xv, xl) (xv0, xl0)) by
        (eapply load_equiv_mem; eauto with lat).
    inv Hmemv; go.

  - Case "Store".
    assert (Mem.stamp (fst p0) <: addrl0 \_/ l = true).
    { inv Hi2. inv ISTACK. simpl in *. trivial. }
    assert (Mem.stamp (fst p) <: addrl \_/ l = true).
    { inv Hi1. inv ISTACK. simpl in *. trivial. }
    repeat inv_equiv_atom;
    assert (m' ~~m m'0) by (
      eapply store_equiv_mem with (11:= STORE) (12:= STORE0);
      eauto with lat);
    go.

  - Case "Call".
    exploit Forall2_app_left ; eauto; intros Hl.
    exploit Forall2_app_right ; eauto; intros Hr.
    inv_equiv_atom.
    SCase "Low Call".
       constructor 2; eauto with lat.
       eapply Forall2_app ; eauto.

    SCase "High Call".
       constructor; auto with lat.
       rewrite below_lret_adata ; eauto.
       rewrite below_lret_adata ; eauto.
       simpl; rewrite Flowl; go.

  - Case "Ret".
    spec_pop_return.
    spec_pop_return.
    exploit low_equiv_step_pop_to_return; eauto; intros HspecRet.
    inv HspecRet.
    exploit_low.
    inv_equiv_atom; go.

  - Case "VRet".
    spec_pop_return.
    spec_pop_return.
    exploit low_equiv_step_pop_to_return; eauto; intros HspecRet.
    exploit_low.
    repeat inv_equiv_atom; go.

  - Case "SysCall".
    assert (sys_info0 = sys_info) by congruence. subst. clear SYS0.
    assert (EQ : map AData args ~~l map AData args0 /\ s ~~l s0).
    { split.
      - eapply Forall2_app_left; eauto.
        repeat rewrite map_length. congruence.
      - eapply Forall2_app_right; eauto.
        repeat rewrite map_length. congruence. }
    destruct EQ as [EQ1 EQ2].
    specialize (hyp_syscall_lowstep SYS args args0 EQ1 SYSSEM SYSSEM0).
    go.

  - Case "SizeOf".
    inv LEa.
    + assert (LEN : length fr = length fr0).
      { inv Hi1. inv ISTACK.
        simpl in *.
        destruct LEm as [LOWF _].
        assert (STAMP : Mem.stamp (fst p0) <: o = true) by eauto with lat.
        exploit LOWF; eauto. intros FRAMES.
        rewrite FRAME in FRAMES. rewrite FRAME0 in FRAMES.
        inv FRAMES. eapply Forall2_length; eauto. }
      rewrite LEN. clear LEN.
      go.
    + go.
Qed.

Lemma all_data_below_lret :
  forall o s1 s2
         (DATA : forall se, In se s1 -> exists a, se = AData a),
    below_lret o (s1 ++ s2) = below_lret o s2.
Proof.
  induction s1 as [|se' s1 IH]; intros; simpl; auto.
  destruct DATA with (se := se'); simpl; auto.
  subst.
  apply IH.
  intros se H.
  apply DATA.
  simpl. auto.
Qed.


Lemma highstep : forall as1 e as1',
  ~low_pc o as1 ->
  a_step atable as1 e as1' ->
  ~low_pc o as1' ->
  low_equiv_full_state o as1 as1'.
Proof.
  intros as1 e as1' Hpc Hs Hpc'.
  destruct as1. destruct apc. simpl in *.
  assert (t <: o = false) by (destruct (flows t o) eqn:E; congruence).
  clear Hpc. inv Hs; try go.

  - Case "Dup".
    constructor; auto.
    match goal with
      | SE : StkElmt T T |- _ =>
        destruct DATA with (se := SE); eauto
    end.
    subst.
    simpl.
    reflexivity.

  - Case "Swap".
    constructor; auto.
    repeat (rewrite all_data_below_lret; eauto).
    eapply swap_forall; eauto.

  - Case "Alloc".
    simpl in Hpc'.
    assert (amem ~~m m').
    + eapply a_alloc_high_step; eauto with lat.
    + go.
  - Case "Store".
    destruct (flows ml o) eqn:?.
    SCase "ml <: o = true".
      assert (t <: o = true) by eauto with lat.
      congruence.
    SCase "ml <: o = false".
      assert (amem ~~m m') by
        (eapply store_high_equiv_mem with (3:= LOAD) (4:= STORE); eauto with lat).
      constructor; eauto.

  - Case "Call".
    constructor; eauto with lat.
    simpl.
    erewrite below_lret_adata; [idtac|eauto].
    erewrite below_lret_adata; [idtac|eauto].
    simpl in *.
    destruct (t<:o) eqn:Hc; go.

  - Case "Ret".
    spec_pop_return.
    simpl in *.
    exploit @pop_to_return_spec2; eauto. intros HTEMP. inv HTEMP.
    exploit @pop_to_return_spec3; eauto. intros HTEMP. inv HTEMP.
    destruct (flows pcl' o) eqn:e; try congruence.
    constructor ; eauto.
    rewrite below_lret_adata; eauto.
    simpl. rewrite e.
    auto.

 - Case "VRet".
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto. intros HTEMP. inv HTEMP.
    exploit @pop_to_return_spec3; eauto. intros HTEMP. inv HTEMP.
    simpl in *.
    destruct (flows pcl' o) eqn:e; try congruence.
    constructor ; eauto.
    simpl.
    rewrite below_lret_adata; eauto.
    simpl. rewrite e.
    auto.

 - Case "SysCall".
   constructor; try congruence; try reflexivity.
   simpl.
   rewrite all_data_below_lret; try reflexivity.
   intros se IN.
   rewrite in_map_iff in IN. destruct IN as (a & ? & ?). eauto.

Qed.

Lemma highlowstep : forall as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  ~low_pc o as1 ->
  a_step atable as1 e as1' ->
  low_pc o as1' ->
  a_step atable as2 e' as2' ->
  low_pc o as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros as1 e as1' as2 e' as2' Heq Hpc Hs1 Hpc' Hs2 Hpc''.
  inv Heq; [clear Hpc | elim Hpc; simpl ; auto].

  exploit a_step_instr; eauto. intros [instr1 Hinstr1].

  (* instr1 is Ret or VRet *)
  inv Hs1; simpl in *;
  try assert (l1 <: o = true) by (eapply join_2_rev; eassumption);
  try congruence;
  inv Hs2; simpl in *;
  try assert (l2 <: o = true) by (eapply join_2_rev; eassumption);
  try congruence.

  - Case "P1 is Ret and P2 is Ret".
    spec_pop_return.
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.
    inv_equiv_atom; go.

  - Case "P1 is Ret and P2 is Vret". (* contradiction *)
    spec_pop_return.
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.

  - Case "P1 is VRet and P2 is Ret". (* contradiction *)
    spec_pop_return.
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.

  - Case "P1 is Vret and P2 is Vret".
    spec_pop_return.
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.
    inv_equiv_atom; go.
Qed.

End fix_observer.

Program Instance AMUnwindingSemantics
  (SL : forall o, syscall_lowstep o atable)
  (SI : systable_inv atable) :
  TINI.UnwindingSemantics AMObservation := {
  s_equiv := low_equiv_full_state;
  s_low := low_pc;
  s_low_dec := low_pc_dec;
  s_inv := inv_state
}.

Lemma Forall2_map : forall E1 E2
                           (R1: relation E1)
                           (R2: relation E2)
                           g f (l1 l2: list E1),
                      (forall x y, R1 x y -> R2 (f x) (g y)) ->
                      Forall2 R1 l1 l2 ->
                      Forall2 R2 (map f l1) (map g l2).
Proof.
  induction 2; intros; simpl; auto.
Qed.

Lemma below_lret_alldata :
  forall o l,
    (forall e, In e l -> exists a, e = AData a) ->
    (below_lret o l) = nil.
Proof.
  induction l ; intros.
  auto.
  destruct a ; simpl. eapply IHl ; eauto.
  intros ; eapply H ; eauto. constructor 2; auto.
  eelim (H (ARet p b)) ; eauto.
  congruence. constructor; auto.
Qed.


Lemma map_AData :
  forall T (l: list (Z* T)) e,
   In e (map (fun a : Z * T => let (i,lbl) := a in AData (Vint i,lbl)) l) -> exists a : Atom T T, e = AData a.
Proof.
  induction l ; intros; inv H; eauto.
  destruct a.
  eauto.
Qed.

Lemma map_AData' :
  forall T (l: list (Z* T)) (e:StkElmt T T),
   In e (map (fun a : Z * T => let (i,lbl) := a in AData (Vint i,lbl)) l) ->
   exists (i:Z) (lbl:T), e = AData (Vint i,lbl).
Proof.
  induction l ; intros; inv H; eauto.
  destruct a.
  eauto.
Qed.

Next Obligation.
  inv H.
  destruct (flows b o) eqn:?.
  constructor 2; eauto.
  eapply Forall2_map; eauto.
  destruct x; destruct y; simpl.
  intros.
  inv H; repeat econstructor; eauto.
  constructor ; eauto.
  rewrite below_lret_alldata; eauto.
  rewrite below_lret_alldata; eauto.
  apply map_AData.
  apply map_AData.
Qed.

Next Obligation.
  intros x y H. rewrite <- H. reflexivity.
Qed.

Next Obligation.
  inv H; split; intros H; inv H; try congruence;
  unfold low_pc; simpl; trivial.
Qed.

Next Obligation.
  destruct i as [[p d] b].
  constructor.
  - intros p' a.
    unfold load; intros.
    rewrite Mem.get_empty in H; discriminate.
  - induction d as [|[a l] d IH]; simpl; try constructor; simpl; trivial.
Qed.

Next Obligation.
  eapply inv_step; eauto.
Qed.

Next Obligation.
  unfold low_pc.
  inv H; simpl;
  try match goal with
        | H : visible_event _ _ |- _ =>
          inv H
      end.
  eauto with lat.
Qed.

Next Obligation.
  inv H1; inv H2;
  try solve [econstructor (intros H'; inv H'; solve [eauto])];
  match goal with
    | H : low_equiv_full_state _ _ _ |- _ =>
      inv H
  end;
  match goal with
    | H : low_pc _ _ |- _ =>
      unfold low_pc in H; simpl in H; try congruence
  end;
  try solve [
        constructor; intros H; inv H;
        match goal with
          | H1 : ?pcl <: ?o = false,
            H2 : ?l \_/ ?pcl <: ?o = true |- _ =>
            apply join_2_rev in H2; congruence
        end
      ];
  try congruence.
  exploit_low.
  inv LEa; try reflexivity.
  constructor 5; intros H; inv H;
  match goal with
    | H : ?l \_/ ?pcl <: ?o = true |- _ =>
      apply join_1_rev in H; congruence
  end.
Qed.

Next Obligation.
  eapply lowstep; eauto.
Qed.

Next Obligation.
  rewrite <- H0.
  symmetry.
  eapply highstep; eauto.
Qed.

Next Obligation.
  eapply highlowstep; eauto.
Qed.

Theorem abstract_noninterference_short
  (SL : forall o, syscall_lowstep o atable)
  (SI : systable_inv atable) :
  TINI.tini AMObservation.
Proof.
  apply TINI.noninterference.
  apply AMUnwindingSemantics; assumption.
Qed.

End ParamMachine.
