Require Import Datatypes.
Require Import ZArith.
Require Import List.
Require Import EquivDec.
Require Import String.
Require Import Show.

Require Import Utils.

Fixpoint replicate {A:Type} (n:nat) (a:A) : list A :=
  match n with
    | O => nil
    | S n' => a :: replicate n' a
  end.

Definition zreplicate {A:Type} (n:Z) (a:A) : option (list A) :=
  if Z_lt_dec n 0 then None
  else Some (replicate (Z.to_nat n) a).

Lemma index_list_replicate: forall A n (a:A) n',
  index_list n' (replicate n a) = if lt_dec n' n then Some a else None.
Proof.
  induction n; destruct n'; simpl; try congruence.
  rewrite IHn.
  do 2 destruct lt_dec; try congruence; try omega.
Qed.

Lemma index_list_Z_zreplicate: forall A z (a:A) z' l,
  zreplicate z a = Some l ->
  index_list_Z z' l = if Z_le_dec 0 z' then
                        if Z_lt_dec z' z then Some a else None else None.
Proof.
  unfold zreplicate, index_list_Z; intros.
  destruct (Z_lt_dec z 0); try congruence.
  inv H.
  destruct (z' <? 0)%Z eqn:Ez.
  - rewrite Z.ltb_lt in Ez.
    destruct Z_lt_dec; try omega.
    destruct Z_le_dec; auto; omega.
  - assert (~ (z' < 0 )%Z).
    rewrite <- Z.ltb_lt; try congruence.
    destruct Z_le_dec; try omega.
    rewrite index_list_replicate.
    assert ( (z'<z)%Z <-> (Z.to_nat z') < (Z.to_nat z)).
      apply Z2Nat.inj_lt; try omega.
    destruct lt_dec; destruct Z_lt_dec; auto; try omega.
Qed.

Inductive alloc_mode := Global | Local.

(* Frames are parameterized over the type of block and the type of Label *)
(* Cannot make this a parameter because we don't want it opaque.
   Keep it outside for now, until I figure out what's better *)
(* Any better solutions than the implicit arguments welcome *)
Inductive frame {A S} := Fr (stamp : S) (label : S) : list A -> @frame A S.


Module Type MEM.
  (* Type of memory is parameterized by the type of stamps and the type of block *)
  Parameter t : Type -> Type -> Type.

  Parameter block : Type -> Type.
  Declare Instance EqDec_block : forall {S} {_:EqDec S eq}, EqDec (block S) eq.
  Parameter stamp : forall {S}, block S -> S.

  (* For generation *)
  Parameter put_stamp : forall {S}, S -> block S -> block S.
  (* For indistinguishability - return all frames with stamps
     less than a label (called with top) *)

 (* For printing *)
  Declare Instance show_block : forall {S} {_: Show S}, Show (block S).

  (* DD -> DP : is a block some kind of "stamped pointer"? *)
  Parameter get_frame : forall {A S}, t A S -> block S -> option (@frame A S).
  Parameter upd_frame :
    forall {A S:Type} {EqS:EqDec S eq}, t A S -> block S -> @frame A S ->
                                        option (t A S).
  Parameter upd_get_frame : forall A S (EqS:EqDec S eq) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Parameter get_upd_frame : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b',
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter upd_frame_defined : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.


  Parameter get_blocks : forall {A S} , list S -> t A S -> list (block S).

  Parameter get_blocks_spec:
    forall {A S} (labs : list S) (mem: t A S) (b: block S),
      In (stamp b) labs /\
      (exists fr, get_frame mem b = Some fr) <->
      In b (get_blocks labs mem).

  Parameter empty : forall A S, t A S.
  Parameter get_empty : forall A S (b:block S), get_frame (empty A S) b = None.

  (* Create a memory with some block initialized to a frame *)
  (* Parameter init : forall A S {eqS:EqDec S eq}, *)
  (*                    alloc_mode -> *)
  (*                    block S -> *)
  (*                    @frame A S -> *)
  (*                    t A S. *)

  (* Parameter get_init_eq : forall A S {eqS:EqDec S eq} *)
  (*                                mode (b : block S) (f : @frame A S), *)
  (*                           get_frame (init A S mode b f) b = Some f. *)

  (* Parameter get_init_neq : forall A S {eqS:EqDec S eq} *)
  (*                                 mode (b b' : block S) (f : @frame A S), *)
  (*                            b' <> b -> *)
  (*                            get_frame (init A S mode b f) b' = None. *)

  Parameter alloc :
    forall {A S} {EqS:EqDec S eq}, alloc_mode -> t A S -> S -> @frame A S -> (block S * t A S).
  Parameter alloc_stamp : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> stamp b = s.
  Parameter alloc_get_fresh : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Parameter alloc_get_frame : forall A S (eqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter alloc_upd : forall A S (eqS:EqDec S eq) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Parameter alloc_local_comm :
    forall A S (EqS:EqDec S eq)  (m m1 m2 m1' m2':t A S) s s' fr fr' b1 b2 b1',
    s <> s' ->
    alloc Local m s fr = (b1,m1) ->
    alloc Local m1 s' fr' = (b2,m2) ->
    alloc Local m s' fr' = (b1',m1') ->
    b1' = b2.
  Parameter alloc2_local :
    forall A S (EqS:EqDec S eq)  (m1 m2 m1' m2':t A S) s fr1 fr2 fr' b,
    alloc Local m1 s fr1 = (b,m1') ->
    alloc Local m2 s fr2 = (b,m2') ->
    fst (alloc Local m1' s fr') = fst (alloc Local m2' s fr').

  Parameter alloc_next_block_no_fr :
    forall A S (EqS:EqDec S eq) (m:t A S) s fr1 fr2,
    fst (alloc Local m s fr1) = fst (alloc Local m s fr2).

  Parameter map : forall {A B S}, (@frame A S -> @frame B S) -> t A S -> t B S.
  Parameter map_spec : forall A B S (f: @frame A S -> @frame B S) (m:t A S),
    forall b, get_frame (map f m) b = option_map f (get_frame m b).

End MEM.

(* For indist/generation purposes, our implementation has to be less generic or
   give our labels a function "allLabelsBelow". For now do the latter *)
Module Mem: MEM.
  Definition block S := (Z * S)%type.

  Instance EqDec_block : forall {S} {EqS:EqDec S eq}, EqDec (block S) eq.
  Proof.
    intros S E (x,s) (x',s').
    destruct (Z.eq_dec x x').
    destruct (s == s').
    left; congruence.
    right; congruence.
    right; congruence.
  Qed.

  Definition stamp S : block S -> S := snd.
  Definition put_stamp S (s : S) (b : block S) : block S :=
    let (z,_) := b in (z,s).

  Record _t {A S} := MEM {
     content :> block S -> option (@frame A S);
     next : S -> Z;
     content_next : forall s i, (1 <= i < next s)%Z  <->
                                (exists fr, content (i,s) = Some fr);
     next_pos : forall s, (1 <= next s)%Z
     (* content_some :  *)
     (*   forall s i, (1 <= i <= (next s) -1)%Z <->  *)
     (*               (exists fr, content (i, s) = Some fr) *)
  }.

  Implicit Arguments _t [].
  Implicit Arguments MEM [A S].
  Definition t := _t.

  Definition get_frame {A S} (m:t A S) := content m.

  Definition Z_seq z1 z2 := map Z.of_nat (seq (Z.to_nat z1) (Z.to_nat z2)).

  Fixpoint list_of_option {A : Type} (l : list (option A)) : list A :=
    match l with
      | nil => nil
      | Some h :: t => h :: list_of_option t
      | None :: t => list_of_option t
    end.

  Definition get_blocks_at_level {A S} (m : t A S) (s : S):=
    let max := next m s in
    let indices := Z_seq 1%Z (max - 1) in
    map (fun ind => (ind,s)) indices.

  Definition get_blocks {A S} (ss : list S) (m : t A S) : list (block S) :=
    flat_map (get_blocks_at_level m) ss.

  Instance show_block {S} {_: Show S}: Show (block S) :=
  {|
    show b :=
      let (z,s) := b in
      ("(" ++ show z ++ " @ " ++ show s ++ ")")%string
  |}.

  Program Definition map {A B S} (f:@frame A S -> @frame B S) (m:t A S) : t B S:=
    MEM
      (fun b => option_map f (get_frame m b))
      (next m)
      _ _.
  Next Obligation.
    split.
    - intros Hrng. destruct (content_next m s i) as [H _]. destruct H.
      assumption. eexists. unfold get_frame. rewrite H. reflexivity.
    - intros [fr Heq]. destruct (content_next m s i) as [_ H].
      apply H. unfold get_frame in Heq. destruct (m (i, s)).
      eexists. reflexivity. discriminate.
  Qed.
  Next Obligation.
    destruct m. auto.
  Qed.

  Lemma map_spec : forall A B S (f:@frame A S -> @frame B S) (m:t A S),
    forall b, get_frame (map f m) b = option_map f (get_frame m b).
  Proof.
    auto.
  Qed.

  Program Definition empty A S : t A S := MEM
    (fun b => None) (fun _ => 1%Z) _ _.
  Next Obligation.
    split. omega. intros [fr contra]. congruence.
  Qed.


  Lemma get_empty : forall A S b, get_frame (empty A S)  b = None.
  Proof. auto. Qed.

  (* Program Definition init A S {eqS : EqDec S eq} (am : alloc_mode) b f : t A S:= MEM *)
  (*   (fun b' : block S => if b' == b then Some f else None) *)
  (*   (fun s => if s == stamp _ b then fst b + 1 else 1)%Z *)
  (*   _.  *)
  (* Next Obligation. *)
  (*   simpl in *. *)
  (*   destruct (s == s0) as [EQ | NEQ]. *)
  (*   - compute in EQ. subst s0. *)
  (*     destruct (equiv_dec (i,s)) as [contra|]; trivial. *)
  (*     inv contra. *)
  (*     omega. *)
  (*   - destruct (equiv_dec (i,s)) as [E|E]; try congruence. *)
  (* Qed. *)

  (* Lemma get_init_eq : forall A S {eqS:EqDec S eq} *)
  (*                            mode (b : block S) (f : @frame A S), *)
  (*                       get_frame (init A S mode b f) b = Some f. *)
  (* Proof. *)
  (*   unfold init. simpl. *)
  (*   intros. *)
  (*   match goal with *)
  (*     | |- context [if ?b then _ else _] => *)
  (*       destruct b; congruence *)
  (*   end. *)
  (* Qed. *)

  (* Lemma get_init_neq : forall A S {eqS:EqDec S eq} *)
  (*                             mode (b b' : block S) (f : @frame A S), *)
  (*                        b' <> b -> *)
  (*                        get_frame (init A S mode b f) b' = None. *)
  (* Proof. *)
  (*   unfold init. simpl. *)
  (*   intros. *)
  (*   match goal with *)
  (*     | |- context [if ?b then _ else _] => *)
  (*       destruct b; congruence *)
  (*   end. *)
  (* Qed. *)

  Program Definition upd_frame_rich {A S} {EqS:EqDec S eq} (m:t A S) (b0:block S) (fr:@frame A S)
  : option { m' : (t A S) |
             (forall b',
                get_frame m' b' = if b0 == b' then Some fr else get_frame m b')
           /\ forall s, next m s = next m' s} :=
    match m b0 with
      | None => None
      | Some _ =>
        Some (MEM
                (fun b => if b0 == b then Some fr else m b)
                (next m) _ _)
    end.
  Next Obligation.
    split.
    - destruct (equiv_dec b0).
      + destruct b0; inv e. eexists. reflexivity.
      + apply content_next; auto.
    - intros [fr' Hif].
      destruct b0.
      destruct (equiv_dec (z,s0) (i, s)). inv e.
      destruct (content_next m s i) as [_ H]. apply H.
      eexists. symmetry. exact Heq_anonymous.
      destruct (content_next m s i) as [_ H]. apply H.
      eexists. eassumption.
  Qed.
  Next Obligation.
    destruct m. auto.
  Qed.

  Definition upd_frame {A S} {EqS:EqDec S eq} (m:t A S) (b0:block S) (fr:@frame A S)
  : option (t A S) :=
    match upd_frame_rich m b0 fr with
      | None => None
      | Some (exist m' _) => Some m'
    end.

  Program Lemma upd_get_frame : forall A S (EqS:EqDec S eq) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Proof.
    unfold upd_frame, upd_frame_rich, get_frame.
    intros.
    generalize (@eq_refl (option (@frame A S)) (m b)).
    generalize (upd_frame_rich_obligation_3 A S EqS m b fr').
    generalize (upd_frame_rich_obligation_2 A S EqS m b fr').
    generalize (upd_frame_rich_obligation_1 A S EqS m b fr').
    simpl.
    rewrite H. intros. eauto.
  Qed.

  Lemma get_upd_frame : forall A S (eqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b',
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold upd_frame; intros.
    destruct (upd_frame_rich m b fr); try congruence.
    destruct s; inv H; intuition.
  Qed.

  Lemma upd_frame_defined : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.
  Proof.
    unfold upd_frame, upd_frame_rich, get_frame.
    intros until 0.
    generalize (@eq_refl (option (@frame A S)) (@content A S m b)).
    generalize (upd_frame_rich_obligation_3 A S EqS m b fr).
    generalize (upd_frame_rich_obligation_2 A S EqS m b fr).
    generalize (upd_frame_rich_obligation_1 A S EqS m b fr).
    simpl.
    intros.
    destruct (m b); eauto; congruence.
  Qed.

  Opaque Z.add.

  Program Definition alloc
             {A S} {EqS:EqDec S eq} (am:alloc_mode) (m:t A S) (s:S) (fr:@frame A S)
            : (block S * t A S) :=
    ((next m s,s),
     MEM
       (fun b' => if (next m s,s) == b' then Some fr else get_frame m b')
       (fun s' => if s == s' then (1 + next m s)%Z else next m s')
       _ _).
  Next Obligation.
    destruct (equiv_dec (next m s, s)).
    - inv e. split.
      + destruct (equiv_dec s0); try congruence.
        intros Hrng. eexists. reflexivity.
      + intros [fr' Heq]. inv Heq. split.
        apply next_pos.
        destruct (equiv_dec s0 s0). omega. congruence.
    - destruct (equiv_dec s s0).
      + inv e. split.
        * intros [Hrng1 Hrng2]. destruct (content_next m s0 i) as [H _].
          apply H. compute in c. split. assumption.
          apply Zlt_is_le_bool in Hrng2.
          rewrite Z.add_comm, <- Z.add_sub_assoc, Z.add_0_r in Hrng2.
          apply Zle_bool_imp_le in Hrng2. apply Zle_lt_or_eq in Hrng2.
          destruct Hrng2 as [Hrng2 | Hrng2]. assumption.
          subst. exfalso. apply c. reflexivity.
        * intros [fr' Heq]. destruct (content_next m s0 i) as [_ H].
          unfold get_frame in Heq.
          assert (ex: (exists fr0 : frame, m (i, s0) = Some fr0))
            by (eexists; eassumption).
          destruct (H ex) as [H1 H2]. split; omega.
      + split; intro Hrng; destruct (content_next m s0 i) as [H1 H2]; auto.
  Qed.
  Next Obligation.
    destruct (equiv_dec s s0);
    destruct m; simpl.
    - specialize (next_pos0 s); try omega.
    - specialize (next_pos0 s0); assumption.
  Qed.

  Lemma alloc_stamp : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> stamp _ b = s.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_get_fresh : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Proof.
    unfold alloc; intros.
    inv H.
    destruct (content_next m s (next m s)) as [_ H].
    unfold get_frame.
    destruct (m (next m s, s)).
    - assert (ex: exists fr0 : frame, Some f = Some fr0)
        by (eexists; reflexivity).
      specialize (H ex). omega.
    - reflexivity.
  Qed.

  Lemma alloc_get_frame : forall A S (eqS:EqDec S eq) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_upd : forall A S (eqS:EqDec S eq) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Proof.
    intros A S eqS am m b fr1 s fr2 m' H.
    unfold alloc, upd_frame in *; simpl.
    destruct (upd_frame_rich m b fr1); try congruence.
    destruct s0; inv H.
    destruct a as [_ T].
    rewrite T; auto.
  Qed.

  Lemma alloc_local_comm :
    forall A S (EqS:EqDec S eq) (m m1 m2 m1' m2':t A S) s s' fr fr' b1 b2 b1',
    s <> s' ->
    alloc Local m s fr = (b1,m1) ->
    alloc Local m1 s' fr' = (b2,m2) ->
    alloc Local m s' fr' = (b1',m1') ->
    b1' = b2.
  Proof.
    intros A S EqS m m1 m2 m1' m2' s s' fr fr' b1 b2 b1' H H0 H1 H2.
    inv H0; inv H1; inv H2.
    destruct (equiv_dec s s'); try congruence.
  Qed.

  Lemma alloc2_local :
    forall A S (EqS:EqDec S eq)  (m1 m2 m1' m2':t A S) s fr1 fr2 fr' b,
    alloc Local m1 s fr1 = (b,m1') ->
    alloc Local m2 s fr2 = (b,m2') ->
    fst (alloc Local m1' s fr') = fst (alloc Local m2' s fr').
  Proof.
    intros A S EqS m1 m2 m1' m2' s fr1 fr2 fr' b H H0.
    inv H; inv H0; simpl.
    rewrite H1; auto.
  Qed.

  Lemma alloc_next_block_no_fr :
    forall A S (EqS:EqDec S eq) (m:t A S) s fr1 fr2,
    fst (alloc Local m s fr1) = fst (alloc Local m s fr2).
  Proof.
    intros A S EqS m s fr1 fr2.
    unfold alloc; simpl; auto.
  Qed.

  Lemma in_seq_Z:
    forall z start len,
      (0 <= start)%Z ->
      (0 <= len)%Z ->
      ((start <= z < len + start)%Z <->
       In z (Z_seq start len)).
  Proof.
    intros z s l. intros Hle1 Hle2. split.
    - intros [H1 H2]. unfold Z_seq.
      apply in_map_iff. exists (Z.to_nat z).
      split. apply Z2Nat.id. omega.
      apply Z2Nat.inj_lt in H2; try omega.
      rewrite Z2Nat.inj_add in H2; try omega.
      apply Z2Nat.inj_le in H1; try omega.
      apply Z2Nat.inj_le in Hle1; try omega.
      apply Z2Nat.inj_le in Hle2; try omega.
      simpl in *. remember (Z.to_nat s) as start.
      remember (Z.to_nat l) as len.
      remember (Z.to_nat z) as z'. clear Heqlen l Heqstart s Heqz' z Hle1.
      generalize dependent start. generalize dependent z'.
      induction len as [| l IHl]; intros s start Hle1 Hle3.
      + omega.
      + simpl in *. apply le_lt_or_eq in Hle1. destruct Hle1 as [H1 | H2].
        right. apply IHl; try omega.
        left. assumption.
    - intros HIn. unfold Z_seq in HIn.
      apply in_map_iff in HIn. destruct HIn as [z' [Heq HIn]]. subst.
      assert (H: Z.to_nat s <= z' < (Z.to_nat l) + (Z.to_nat s) ->
                 (s <= (Z.of_nat z') < l + s)%Z).
      { intros [H1 H2]. split.
        apply Z2Nat.inj_le; try omega. rewrite Nat2Z.id. assumption.
        apply Z2Nat.inj_lt; try omega. rewrite Nat2Z.id, Z2Nat.inj_add;
         try omega; assumption. }
      apply H.
      apply Z2Nat.inj_le in Hle1; try omega.
      apply Z2Nat.inj_le in Hle2; try omega.
      remember (Z.to_nat s) as start.
      remember (Z.to_nat l) as len.
      clear H Heqlen l Heqstart s.
      generalize dependent start. generalize dependent z'.
      induction len as [| len IHlen].
      + contradiction.
      + intros z' start Hle HIn. simpl in *.
        destruct HIn. subst. split; omega.
        rewrite plus_n_Sm.
        assert (H': S start <= z' < len + S start ->
                    start <= z' < len + S start).
        { intros [H1 H2]. split; try omega. }
        apply H'. apply IHlen; try omega. assumption.
  Qed.

  Lemma get_blocks_spec :
    forall A S (labs : list S) (mem: t A S) b,
      In (stamp _ b) labs /\
      (exists fr, get_frame mem b = Some fr) <->
      In b (get_blocks labs mem).
  Proof.
    intros A S labs mem b.
    split.
    - intros [HIn [fr Hget]].
      unfold get_blocks. apply in_flat_map. eexists; split; [eassumption |].
      unfold get_blocks_at_level. apply in_map_iff. exists (fst b);
      destruct b; simpl; split.
      + reflexivity.
      + apply in_seq_Z; try omega.
        * apply Zle_minus_le_0. apply next_pos.
        * rewrite <- Z.sub_sub_distr, Z.sub_0_r. simpl.
          apply content_next. eexists. eassumption.
    - intros HIn. unfold get_blocks, get_blocks_at_level in *.
      apply in_flat_map in HIn. destruct HIn as [l [HInl HIn]].
      apply in_map_iff in HIn. destruct HIn as [z [Heq HIn]]. subst.
      split. assumption.
      unfold get_frame. apply content_next. apply in_seq_Z in HIn; try omega.
      apply Zle_minus_le_0. apply next_pos.
  Qed.

End Mem.
