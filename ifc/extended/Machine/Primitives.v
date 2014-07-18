Require Import ZArith.
Require Export Instructions.
Require Import List.
Require Import Rules.

Require Import Memory.
Require Import Lattices.
Require Import EquivDec.

Open Scope Z_scope.
Open Scope bool_scope.

(** * Semantics *)

Definition eval_binop (b : BinOpT) : Z -> Z -> option Z :=
  match b with
    | BAdd => fun z1 z2 => Some (z1 + z2)
    | BMult => fun z1 z2 => Some (z1 * z2)
  end.

(** memory frame pointers. *)
Definition mframe: Type := Mem.block Label.

(* observables *)
Inductive Obs_value : Type :=
  | OVint (n:Z)
.

Definition Obs_eq_dec : forall o1 o2 : Obs_value, {o1 = o2} + {o1 <> o2}.
  intros. repeat (decide equality).
Qed.

Definition Obs_value_eq o1 o2 := if Obs_eq_dec o1 o2 then true else false.

Definition trace := list (Obs_value * Label).

(* values *)
Inductive Pointer : Type :=
  | Ptr (fp:mframe) (i:Z).

Inductive Value : Type :=
  | Vint  (n:Z)
  | Vptr  (p:Pointer)
  | Vcptr (addr : Z) (* CH: Why not just nat? *) (* Maybe we want a CptrOffset? *)
          (* TODO: remove this crap, we have no way to create them! *)
  | Vlab  (L:Label).

Definition obs_value_to_value (ov:Obs_value) : Value :=
  match ov with
    | OVint n => Vint n
  end.
Coercion obs_value_to_value : Obs_value >-> Value.

Inductive Atom : Type :=
 | Atm (v:Value) (l:Label).

Inductive Ptr_atom : Type :=
 | PAtm (i:Z) (l:Label).

Definition imem := list Instruction.

Definition instr_lookup (m:imem) (pc:Ptr_atom) : option Instruction :=
  let '(PAtm i _) := pc in
  index_list_Z i m.

Notation "m [ pc ]" := (instr_lookup m pc) (at level 20).

Definition add_pc (pc:Ptr_atom) (n:Z) : Ptr_atom :=
  let '(PAtm i L) := pc in 
  PAtm (Zplus i n) L.
Infix "+" := add_pc.

Definition pc_lab (pc:Ptr_atom) : Label :=
  let '(PAtm _ L) := pc in L.
Notation "'∂' pc" := (pc_lab pc) (at level 0). 
(* Remark: the ott file use \mathcal{L} *)

Definition atom_lab (a : Atom) : Label :=
  let '(Atm _ l) := a in l.

(* Registers *)
Definition register := Atom.
Definition regSet := list register.

(* Stack *)
Inductive Stack :=
  | Mty                                       (* empty stack *)
  | RetCons (pc_L:Ptr_atom * Label * regSet * regPtr) (s:Stack) 
(* stack frame marker cons (with return pc and protecting label) *)
.
Infix ":::" := RetCons (at level 60, right associativity).

Infix "@" := Atm (no associativity, at level 50).

Class Join (t :Type) := {
    join_label: t -> Label -> t
  }.
Notation "x ∪ y" := (join_label x y) (right associativity, at level 55).

Instance JoinLabel : Join Label := { join_label := join }.

Definition atom_join (a:Atom) (l':Label) : Atom :=
  match a with
    | Atm v l => Atm v (join l l')
  end.

Definition ptr_atom_join (pc:Ptr_atom) (l':Label) : Ptr_atom :=
  let '(PAtm i l) := pc in PAtm i (l ∪ l').

Instance JoinAtom : Join Atom := { join_label := atom_join }.
Instance JoinPtrAtom : Join Ptr_atom := { join_label := ptr_atom_join }.

Ltac try_split_congruence := 
  try solve [left; congruence | right; congruence].

(* Proof-stuff previously in Memory.v *)
Instance EqDec_block : EqDec Value eq.
Proof.
  intros x y; 
  unfold complement, equiv; simpl;
  destruct x; destruct y; try_split_congruence.
  - destruct (Z.eq_dec n n0); subst; auto; try_split_congruence.
  - destruct p; destruct p0; 
    destruct (Z.eq_dec i i0); destruct (fp == fp0); 
    try_split_congruence.
  - destruct addr; destruct addr0; try_split_congruence;
    destruct (Pos.eq_dec p p0); try_split_congruence.
  - destruct (LatEqDec Label L L0); try_split_congruence.
Qed.

Definition val (v1 v2 : Value) : Value :=
  Vint (if v1 == v2 then 1 else 0).

Definition memory := Mem.t Atom Label.
(* Specialize the Memory frame declaration *)
Definition frame := @frame Atom Label.

Definition alloc (size:Z) (lab stamp:Label) (a:Atom) (m:memory)
: option (mframe * memory) :=
  match zreplicate size a with
    | Some fr => Some (Mem.alloc Local m stamp (Fr stamp lab fr))
    | _ => None
  end.

Definition load (m : memory) (p : Pointer) : option Atom :=
  let '(Ptr f addr) := p in
  match Mem.get_frame m f with
    | None => None
    | Some (Fr _ _ fr) => index_list_Z addr fr
  end.

Definition store (m : memory) (p : Pointer) (a:Atom)
: option (memory) :=
  let '(Ptr f addr) := p in
  match Mem.get_frame m f with
    | None => None
    | Some (Fr stamp lab data) => 
      match update_list_Z addr a data with
        | None => None
        | Some data' => (Mem.upd_frame m f (Fr stamp lab data'))
      end
  end.

Definition msize (m:memory) (p:Pointer) : option nat :=
  let (fp,i) := p in
  match Mem.get_frame m fp with
    | Some (Fr _ _ data) => Some (length data)
    | _ => None
  end.

Definition mlab (m:memory) (p:Pointer) : option Label :=
  let (fp,i) := p in
  match Mem.get_frame m fp with
    | Some (Fr _ L _) => Some L
    | _ => None
  end.

Lemma load_alloc : forall size stamp label a m m' mf,
    alloc size stamp label a m = Some (mf, m') ->
    forall mf' ofs',
      load m' (Ptr mf' ofs') =
        if mf == mf' then 
          if Z_le_dec 0 ofs' then
            if Z_lt_dec ofs' size then Some a else None
          else None
        else load m (Ptr mf' ofs').
Proof.
  unfold alloc, load; intros.
  destruct (zreplicate size a) eqn:Ez; try congruence; inv H.
  rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H1).
  destruct (equiv_dec mf).
  - inv e.
    destruct (equiv_dec mf'); try congruence.
    eapply index_list_Z_zreplicate; eauto.
  - destruct (equiv_dec mf); try congruence.
Qed.

Lemma load_store : forall {m m'} {b ofs a}, 
    store m (Ptr b ofs) a = Some m' ->
    forall b' ofs', 
      load m' (Ptr b' ofs') =
      if b == b' then
        if Z_eq_dec ofs ofs' then Some a else load m (Ptr b' ofs')
      else load m (Ptr b' ofs').
Proof.
  unfold store, load; intros.
  destruct (Mem.get_frame m b) eqn:E1; try congruence.
  destruct f as [stmp lab l].
  destruct (update_list_Z ofs a l) eqn:E2; try congruence.
  rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H).
  destruct (equiv_dec b);
  destruct (equiv_dec b); try congruence.
  - inv e; clear e0.
    destruct Z.eq_dec.
    + inv e.
      eapply update_list_Z_spec; eauto.
    + rewrite E1.
      symmetry.
      eapply update_list_Z_spec2; eauto.
Qed.

Lemma load_store_old : forall {m m':memory} {b ofs a}, 
    store m (Ptr b ofs) a = Some m' ->
    forall b' ofs', 
      (b',ofs') <> (b,ofs) ->
      load m' (Ptr b' ofs') = load m (Ptr b' ofs').
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec mframe); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_store_new : forall {m m':memory} {b ofs a}, 
    store m (Ptr b ofs) a = Some m' ->
    load m' (Ptr b ofs) = Some a.
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec mframe); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_some_store_some : forall {m:memory} {b ofs a}, 
    load m (Ptr b ofs) = Some a ->
    forall a':Atom,
      exists m', store m (Ptr b ofs) a' = Some m'.
Proof.
  unfold load, store; intros.
  destruct (Mem.get_frame m b) eqn:E; try congruence.
  destruct f eqn:?. (* I don't like this *)
  exploit index_list_Z_valid; eauto.
  destruct 1.                                
  destruct (@update_list_Z_Some _ a' l ofs); auto.
  rewrite H2.
  eapply Mem.upd_get_frame; eauto.
Qed.

Lemma alloc_get_frame_old :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (f f' : @Memory.frame T S) b b' mem'
         (ALLOC : Mem.alloc mode mem stamp f' = (b', mem'))
         (FRAME : Mem.get_frame mem b = Some f),
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b' == b) as [E | E]; auto.
  compute in E. subst b'.
  exploit Mem.alloc_get_fresh; eauto.
  congruence.
Qed.

Lemma alloc_get_frame_new :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (frame : @Memory.frame T S) b mem'
         (ALLOC : Mem.alloc mode mem stamp frame = (b, mem')),
    Mem.get_frame mem' b = Some frame.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b) as [E | E]; auto.
  congruence.
Qed.

Lemma get_frame_upd_frame_eq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b f m'
         (UPD : Mem.upd_frame m b f = Some m'),
    Mem.get_frame m' b = Some f.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b); eauto.
  congruence.
Qed.

Lemma get_frame_upd_frame_neq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b b' f m'
         (UPD : Mem.upd_frame m b f = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b'); congruence.
Qed.

Lemma get_frame_store_neq :
  forall (m : memory ) b b' off a m'
         (STORE : store m (Ptr b off) a = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  unfold store.
  intros.
  destruct (Mem.get_frame m b) as [f|] eqn:FRAME; try congruence.
  destruct f as [stamp lab l] eqn:?.
  destruct (update_list_Z off a l) as [l'|] eqn:NEWFRAME; try congruence.
  eapply get_frame_upd_frame_neq; eauto.
Qed.

Lemma alloc_get_frame_eq :
  forall m s (mem : memory) f b mem',
    Mem.alloc m mem s f = (b, mem') ->
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b); congruence.
Qed.

Lemma alloc_get_frame_neq :
  forall m s (mem : memory) f b b' mem',
    Mem.alloc m mem s f = (b, mem') ->
    b <> b' ->
    Mem.get_frame mem' b' = Mem.get_frame mem b'.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b'); congruence.
Qed.

Definition extends (m1 m2 : memory) : Prop :=
  forall b fr, Mem.get_frame m1 b = Some fr -> Mem.get_frame m2 b = Some fr.

Lemma extends_refl : forall (m : memory), extends m m.
Proof. unfold extends. auto. Qed.

Lemma extends_trans : forall (m1 m2 m3 : memory), extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof. unfold extends. auto. Qed.

Lemma extends_load (m1 m2 : memory) b off a :
  forall (EXT : extends m1 m2)
         (DEF : load m1 (Ptr b off) = Some a),
    load m2 (Ptr b off) = Some a.
Proof.
  intros.
  unfold load in *.
  destruct (Mem.get_frame m1 b) as [fr|] eqn:FRAME; inv DEF.
  erewrite EXT; eauto.
Qed.

Section Injections.

Definition meminj := mframe -> option mframe.

Inductive match_vals (mi : meminj) : Value -> Value -> Prop :=
| mv_num : forall z, match_vals mi (Vint z) (Vint z)
| mv_ptr : forall b1 b2 off
                  (BLOCK : mi b2 = Some b1),
             match_vals mi (Vptr (Ptr b1 off)) (Vptr (Ptr b2 off))
| mv_cptr : forall z, match_vals mi (Vcptr z) (Vcptr z)
| mv_vlab : forall l, match_vals mi (Vlab l) (Vlab l).
Hint Constructors match_vals.

Variable match_tags : Label -> Label -> memory -> Prop.
Variable valid_update : memory -> memory -> Prop.
Hypothesis valid_update_match_tags :
  forall t1 t2 m2 m2',
    match_tags t1 t2 m2 ->
    valid_update m2 m2' ->
    match_tags t1 t2 m2'.

Inductive match_atoms (mi : meminj) : Atom -> Atom -> memory -> Prop :=
| ma_intro : forall v1 v2 t1 t2 m2
                    (VALS : match_vals mi v1 v2)
                    (TAGS : match_tags t1 t2 m2),
               match_atoms mi (v1@t1) (v2@t2) m2.
Hint Constructors match_atoms.

Inductive match_frames (mi : meminj) : frame -> frame -> memory -> Prop :=
| ma_fr : forall (st lab : Label) (d1 d2 : list Atom) (m : memory),
  Forall2 (fun a1 a2 => match_atoms mi a1 a2 m) d1 d2 ->
  match_frames mi (Fr st lab d1) (Fr st lab d2) m.
Hint Constructors Forall2.
Hint Constructors match_frames.

Record Meminj (m1 : memory) (m2 : memory) (mi : meminj) := {

  mi_valid : forall b1 b2
                    (INJ : mi b2 = Some b1),
             exists f1 f2,
               Mem.get_frame m1 b1 = Some f1 /\
               Mem.get_frame m2 b2 = Some f2 /\
               match_frames mi f1 f2 m2;

  mi_invalid : forall b2,
                 Mem.get_frame m2 b2 = None ->
                 mi b2 = None;

  mi_inj : forall b1 b2 b2',
             mi b2 = Some b1 ->
             mi b2' = Some b1 ->
             b2 = b2'

}.

(* A weaker version of the corresponding axiom which is easier to use
in some cases *)
Lemma mi_valid' :
  forall m1 m2 mi
         b1 b2 f2
         (INJ : Meminj m1 m2 mi)
         (LOAD : Mem.get_frame m2 b2 = Some f2)
         (MATCH : mi b2 = Some b1),
    exists f1,
      Mem.get_frame m1 b1 = Some f1 /\
      match_frames mi f1 f2 m2.
Proof.
  intros.
  exploit mi_valid; eauto.
  intros [f1 [f2' [H1 [H2 H3]]]].
  rewrite LOAD in H2.
  inv H2.
  eauto.
Qed.

Definition update_meminj (mi : meminj) (b2 : mframe) (b1 : mframe) : meminj :=
  fun b2' =>
    if b2' == b2 then Some b1
    else mi b2'.

Lemma update_meminj_eq : forall mi b2 b1,
                           update_meminj mi b2 b1 b2 = Some b1.
Proof.
  intros.
  unfold update_meminj.
  destruct (@equiv_dec mframe) as [E | E].
  - trivial.
  - compute in E. intuition.
Qed.
Hint Resolve update_meminj_eq.

Lemma update_meminj_neq : forall mi b2 b1 b2'
                                 (NEQ : b2' <> b2),
                            update_meminj mi b2 b1 b2' = mi b2'.
Proof.
  intros.
  unfold update_meminj.
  destruct (@equiv_dec mframe) as [E | E].
  - congruence.
  - trivial.
Qed.

Lemma meminj_mem_alloc :
  forall mi mode1 mode2 stamp1 stamp2 m1 b1 m1' f1 m2 b2 m2' f2,
  forall (INJ : Meminj m1 m2 mi)
         (MATCH : match_frames mi f1 f2 m2)
         (E1 :  Mem.alloc mode1 m1 stamp1 f1 = (b1, m1'))
         (E2 : Mem.alloc mode2 m2 stamp2 f2 = (b2, m2'))
         (VALID : valid_update m2 m2'),
    Meminj m1' m2' (update_meminj mi b2 b1).
Proof.
  intros.
  constructor.

  - intros b1' b2' FRAME.
    destruct (b2' == b2) as [E | E].
    + compute in E. subst b2'.
      rewrite update_meminj_eq in FRAME.
      symmetry in FRAME. inv FRAME.
      exists f1.
      erewrite alloc_get_frame_eq; eauto.
      eexists; repeat (split; eauto).
      { erewrite alloc_get_frame_eq; eauto. }
      assert (Hb2 : mi b2 = None).
      { eapply mi_invalid; eauto.
        eapply Mem.alloc_get_fresh; eauto. }
      clear - Hb2 MATCH VALID valid_update_match_tags.
      induction MATCH; eauto.
      constructor; auto.
      clear - Hb2 VALID valid_update_match_tags H.
      induction H; eauto.
      constructor; eauto.
      inv H.
      inv VALS; eauto.
      constructor; eauto.
      constructor; eauto.
      rewrite update_meminj_neq; auto.
      congruence.
    + rewrite update_meminj_neq in FRAME; auto.
      exploit mi_valid; eauto.
      intros [f1' [f2' [H1 [H2 H3]]]].
      exists f1'. exists f2'.
      split; try split.
      * erewrite Mem.alloc_get_frame; eauto.
        destruct (b1 == b1') as [Eb1|Eb1]; trivial.
        compute in Eb1. subst b1'.
        erewrite Mem.alloc_get_fresh in H1; eauto; try congruence.
      * erewrite Mem.alloc_get_frame; eauto.
        destruct (b2 == b2') as [Eb1|Eb1]; try congruence.
      * clear H1 H2.
        inv H3; auto.
        induction H; auto.
        constructor; eauto.
        constructor.
        inv H.
        constructor; eauto.
        inv VALS; auto. 
        constructor; auto.
        rewrite update_meminj_neq; eauto.
        cut (mi b2 = None); try congruence.
        eapply mi_invalid; eauto.
        erewrite Mem.alloc_get_fresh; eauto.
        inv IHForall2; auto.
  - intros b2' H.
    erewrite Mem.alloc_get_frame in H; eauto.
    destruct (b2 == b2'); try congruence.
    rewrite update_meminj_neq; eauto.
    eapply mi_invalid; eauto.

  - unfold update_meminj.
    intros b1' b2' b2'' H1 H2.
    destruct (@equiv_dec mframe) as [H1' | H1'].
    + inv H1.
      destruct (@equiv_dec mframe) as [H2' | H2'].
      * congruence.
      * eapply mi_valid in H2; eauto.
        destruct H2 as [f1' [_ [contra [_ _]]]].
        eapply Mem.alloc_get_fresh in E1.
        congruence.
    + destruct (@equiv_dec mframe) as [H2' | H2'].
      * inv H2.
        eapply mi_valid in H1; eauto.
        destruct H1 as [f1' [_ [contra [_ _]]]].
        eapply Mem.alloc_get_fresh in E1.
        congruence.
      * eapply mi_inj; eauto.

Qed.

Lemma zreplicate_match_data : 
  forall mi a1 a2 m size l1 l2,
    match_atoms mi a1 a2 m ->
    zreplicate size a1 = Some l1 ->
    zreplicate size a2 = Some l2 ->
    Forall2 (fun a1 a2 => match_atoms mi a1 a2 m) l1 l2.
Proof.
  intros.
  unfold zreplicate in *.
  destruct (ZArith_dec.Z_lt_dec size 0); try congruence.
  gdep (BinInt.Z.to_nat size).
  clear - H.
  intros n. gdep l1. gdep l2.
  induction n; intros; simpl in *. 
  inv H0; inv H1; auto.  
  inv H0; inv H1; constructor; auto.
Qed.  
(*
Lemma zreplicate_match_oframes :
  forall z mi a1 a2 m2 stamp lab,
    match_atoms mi a1 a2 m2 ->
    match_oframes mi (Fr stamp lab (zreplicate z a1)) 
                     (Fr stamp lab (zreplicate z a2)) m2.
Proof.
  intros.
  unfold zreplicate.
  destruct (ZArith_dec.Z_lt_dec z 0); constructor.
  gdep (BinInt.Z.to_nat z).
  clear - H.
  intros n.
  induction n; simpl; auto.
Qed.
*)
(*
Lemma add_defined : forall mi v11 v12 v21 v22 r2
                           (ADD : add v21 v22 = Some r2)
                           (V1 : match_vals mi v11 v21)
                           (V2 : match_vals mi v12 v22),
                      exists r1,
                        add v11 v12 = Some r1 /\
                        match_vals mi r1 r2.
Proof.
  intros.
  inv V1; inv V2; simpl in *; inv ADD; eauto.
Qed.

Lemma sub_defined : forall mi v11 v12 v21 v22 r2
                           (SUB : sub v21 v22 = Some r2)
                           (V1 : match_vals mi v11 v21)
                           (V2 : match_vals mi v12 v22),
                      exists r1,
                        sub v11 v12 = Some r1 /\
                        match_vals mi r1 r2.
Proof.
  intros.
  inv V1; inv V2; simpl in *; eauto; try congruence;
  try match goal with
        | H : context[if ?b then _ else _] |- _ =>
          destruct b as [E | E]; compute in E; subst; try congruence
      end;
  allinv;
  eauto.
  match goal with
    | H1 : ?x = _,
      H2 : ?x = _ |- _ =>
      rewrite H2 in H1; inv H1
  end.
  match goal with
    | |- context[if ?b then _ else _] =>
      destruct b as [E | E]; try congruence
  end.
  eauto.
Qed.

Lemma match_vals_eq :
  forall m1 m2 mi v11 v12 v21 v22
         (INJ : Meminj m1 m2 mi)
         (VALS1 : match_vals mi v11 v21)
         (VALS2 : match_vals mi v12 v22),
    match_vals mi (val_eq v11 v12)
                  (val_eq v21 v22).
Proof.
  intros. unfold val_eq.
  destruct (v11 == v12) as [E1 | E1]; compute in E1; subst;
  destruct (v21 == v22) as [E2 | E2]; compute in E2; subst;
  auto;
  inv VALS1; inv VALS2; try congruence.
  cut (b2 = b3); try congruence.
  eapply mi_inj; eauto.
Qed.
*)

Lemma match_frames_valid_index :
  forall mi st1 lab1 f1 st2 lab2 f2 off a2 m2
         (FRAMES : match_frames mi (Fr st1 lab1 f1) (Fr st2 lab2 f2) m2)
         (INDEX : index_list_Z off f2 = Some a2),
    exists a1,
      index_list_Z off f1 = Some a1 /\
      match_atoms mi a1 a2 m2.
Proof.
  unfold index_list_Z.
  intros.
  destruct (BinInt.Z.ltb off 0); try congruence.
  gdep (BinInt.Z.to_nat off). clear off.
  inversion FRAMES. 
  generalize dependent d1.  
  generalize dependent d2.
  induction H6; intros off INDEX; intros; destruct off;
  simpl in *; try congruence; eauto.
  subst.
  unfold index_list in *. 
  destruct n; eauto; try inv INDEX0; eauto.
  destruct n; simpl in *; try congruence; eauto.
  exists x. repeat split; eauto. subst. 
  inv INDEX0; subst; eauto.
  eapply IHForall2; eauto.
  inv FRAMES; eauto.
Qed. (* I horribly-fied this proof *)

Lemma meminj_load :
  forall m1 m2 mi b1 b2 off a2
         (INJ : Meminj m1 m2 mi)
         (LOAD : load m2 (Ptr b2 off) = Some a2)
         (MATCH : mi b2 = Some b1),
    exists a1,
      load m1 (Ptr b1 off) = Some a1 /\
      match_atoms mi a1 a2 m2.
Proof.
  unfold load.
  intros.
  destruct (Mem.get_frame m2 b2) as [f2|] eqn:E2; try congruence.
  exploit mi_valid'; eauto.

  intros [f1 [H1 H2]].
  rewrite H1. destruct f1; destruct f2.
  eapply match_frames_valid_index; eauto.
Qed.

Lemma match_frames_update_success :
  forall mi st1 lab1 f1 st2 lab2 f2 f2' off a1 a2 m2
         (FRAMES : match_frames mi (Fr st1 lab1 f1) (Fr st2 lab2 f2) m2)
         (ATOMS : match_atoms mi a1 a2 m2)
         (INDEX : update_list_Z off a2 f2 = Some f2'),
    exists f1',
      update_list_Z off a1 f1 = Some f1' /\
      match_frames mi (Fr st1 lab1 f1') (Fr st2 lab2 f2') m2.
Proof.
  unfold update_list_Z.
  intros.
  destruct (BinInt.Z.ltb off 0); try congruence.
  gdep (BinInt.Z.to_nat off). clear off.
  gdep f2'.
  inv FRAMES.  
  induction H6; intros f2' off INDEX; intros; destruct off;
  simpl in *; try congruence; eauto.
  - inv INDEX. eauto.
  - match goal with
      | H : (match ?UP with _ => _ end) = Some _ |- _ =>
        destruct UP eqn:E; try congruence
    end.
    destruct (update_list off a1 l) eqn:?; try congruence.
    inv INDEX.
    pose proof (IHForall2 l0 off E).
    inv H0. inv H1. rewrite H0 in Heqo. inv Heqo.
    exists (x :: l1). repeat split; eauto.
    constructor; eauto.
    inv H2; eauto.
    pose proof (IHForall2 l0 off E).
    inv H0.
    inv H1. congruence.
Qed.

Lemma match_atoms_valid_update :
  forall mi a1 a2 m2 m2'
         (ATOMS : match_atoms mi a1 a2 m2)
         (VALID : valid_update m2 m2'),
    match_atoms mi a1 a2 m2'.
Proof. intros. inv ATOMS; eauto. Qed.
Hint Resolve match_atoms_valid_update.

Lemma match_frames_valid_update :
  forall mi f1 f2 m2 m2'
         (FRAMES : match_frames mi f1 f2 m2)
         (VALID : valid_update m2 m2'),
    match_frames mi f1 f2 m2'.
Proof. intros. inv FRAMES. induction H; eauto. repeat constructor; eauto. 
       inv IHForall2; eauto. Qed.
Hint Resolve match_frames_valid_update.

Lemma match_frames_upd_frame :
  forall m1 m2 m2' mi
         b1 b2 f1 f2
         (INJ : Meminj m1 m2 mi)
         (FRAMES : match_frames mi f1 f2 m2)
         (UPD : Mem.upd_frame m2 b2 f2 = Some m2')
         (MATCH : mi b2 = Some b1)
         (VALID : valid_update m2 m2'),
    exists m1',
      Mem.upd_frame m1 b1 f1 = Some m1' /\
      Meminj m1' m2' mi.
Proof.
  intros.
  exploit mi_valid; eauto.
  intros [f1' [_ [Hf1' [_ _]]]].
  eapply Mem.upd_get_frame in Hf1'.
  destruct Hf1' as  [m1' Hf1].
  eexists.
  split; eauto.
  constructor.

  - clear - INJ UPD MATCH FRAMES Hf1 VALID valid_update_match_tags.
    intros b1' b2' Hb1b2.
    eapply Mem.get_upd_frame with (b' := b2') in UPD.
    destruct (b2 == b2') as [EQ|NEQ]; try congruence.
    + rewrite UPD.
      compute in EQ; subst b2'.
      assert (b1 = b1') by congruence.
      subst b1'. clear Hb1b2.
      erewrite Mem.get_upd_frame; eauto.
      match goal with
        | |- context[if ?b then _ else _] =>
          destruct b; eauto; try congruence
      end.

      repeat eexists. eauto.
    + rewrite UPD.
      clear UPD. (* FRAMES. *)
      exploit mi_valid; eauto.
      intros [f1' [f2' [H1 [H2 H3]]]].
      eexists. exists f2'.
      repeat split; eauto.
      erewrite Mem.get_upd_frame; eauto.
      match goal with
        | |- context[if ?b then _ else _] =>
          destruct b as [EQ|_]; try congruence
      end.
      compute in EQ. subst b1.
      cut (b2 = b2'); try congruence.
      eapply mi_inj; eauto.
  - intros b2' H.
    destruct (mi b2') as [f2'|] eqn:Eb2'; trivial.
    exploit mi_valid; eauto.
    intros [? [? [? [? ?]]]].
    erewrite Mem.get_upd_frame in H; eauto.
    destruct (b2 == b2'); congruence.
  - eapply mi_inj; eauto.
Qed.

Lemma meminj_store :
  forall m1 m2 mi
         b1 b2 off a1 a2 m2'
         (INJ : Meminj m1 m2 mi)
         (STORE : store m2 (Ptr b2 off) a2 = Some m2')
         (VALS : match_atoms mi a1 a2 m2)
         (MATCH : mi b2 = Some b1)
         (VALID : valid_update m2 m2'),
    exists m1',
      store m1 (Ptr b1 off) a1 = Some m1' /\
      Meminj m1' m2' mi.
Proof.
  unfold store.
  intros.
  destruct (Mem.get_frame m2 b2) as [f2|] eqn:Ef2; try congruence.
  exploit mi_valid'; eauto.
  intros [f1 [H1 H2]].
  rewrite H1.
  destruct f1 eqn:?; destruct f2 eqn:?.
  destruct (update_list_Z off a2 l0) eqn:E; try congruence.
  exploit match_frames_update_success; eauto.
  intros [f1' [Ef' ?]].
  rewrite Ef'.
  eapply match_frames_upd_frame; eauto.
Qed.
(*
Lemma meminj_alloc : forall mi size lab2 stamp2 m1 a1 m2 a2 b2 m2',
                     forall (INJ : Meminj m1 m2 mi)
                            (ALLOC : alloc size stamp2 lab2 a2 m2 = Some (b2, m2'))
                            (ATOMS : match_atoms mi a1 a2 m2)
                            (VALID : valid_update m2 m2'),
                     forall stamp1 lab1, 
                       exists b1 m1',
                         alloc size stamp1 lab1 a1 m1 = Some (b1, m1') /\
                         Meminj m1' m2' (update_meminj mi b2 b1).
Proof.
  unfold alloc.
  intros.

  destruct (zreplicate size a1) eqn:ZREP1;
  destruct (zreplicate size a2) eqn:ZREP2;
  try congruence.

  eapply zreplicate_match_data with (size := size) in ATOMS; eauto.

  destruct (Mem.alloc Local m1 lab1 (Fr lab1 stamp1 l)) as [b1 m1'] eqn:E.
  exists b1. exists m1'.
  split. reflexivity.

  eapply meminj_mem_alloc.

  Focus 3. eassumption.
  Focus 3. inv ALLOC. eassumption.
  eauto. 

  inv ATOMS.
  inv ALLOC.
  destruct (Mem.alloc Local m1 lab1 (Fr lab1 stamp1 nil)) as [b1 m1'] eqn:E.
  exists b1. exists m1'.
  split. reflexivity.
  eapply meminj_mem_alloc; eauto.


  
Qed.
*)
End Injections.
