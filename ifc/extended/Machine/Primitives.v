Require Import ZArith.
Require Import List.
Require Import EquivDec.

Require Import Utils.
Require Import Labels.
Require Import Rules.
Require Import Memory.
Require Export Instructions.

Open Scope bool_scope.

(* CH: Why not just merge all this in the semantics file? *)

Section Primitives.

Context {Label: Type}.
(* TODO: CH: Any way to reduce this boilerplate?
             Why would I need to explicitly mention subclasses? *)
Context {JSL: JoinSemiLattice Label}.
Context {LL : Lattice Label}.
Context {FL: FiniteLattice Label}.

(** memory frame pointers. *)
Definition mframe : Type := Mem.block Label.

(* observables *)
Inductive Obs_value : Type :=
  | OVint (n:Z).

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

Definition add_pc (pc:Ptr_atom) (n:Z) : Ptr_atom :=
  let '(PAtm i L) := pc in
  PAtm (Zplus i n) L.

Definition pc_lab (pc:Ptr_atom) : Label :=
  let '(PAtm _ L) := pc in L.
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

Class Join (t :Type) := {
    join_label: t -> Label -> t
  }.

Global Instance JoinLabel : Join Label := { join_label := join }.

Definition atom_join (a:Atom) (l':Label) : Atom :=
  match a with
    | Atm v l => Atm v (join l l')
  end.

Definition ptr_atom_join (pc:Ptr_atom) (l':Label) : Ptr_atom :=
  let '(PAtm i l) := pc in PAtm i (join_label l l').

Global Instance JoinAtom : Join Atom := { join_label := atom_join }.
Global Instance JoinPtrAtom : Join Ptr_atom := { join_label := ptr_atom_join }.

Ltac try_split_congruence :=
  try solve [left; congruence | right; congruence].

(* Proof-stuff previously in Memory.v *)
Global Instance EqDec_block : EqDec Value eq.
Proof.
  intros x y;
  unfold complement, equiv; simpl;
  destruct x; destruct y; try_split_congruence.
  - destruct (Z.eq_dec n n0); subst; auto; try_split_congruence.
  - destruct p; destruct p0;
    destruct (Z.eq_dec i i0); destruct (fp == fp0);
    try_split_congruence.
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

End Primitives.

Notation "m [ pc ]" := (instr_lookup m pc) (at level 20).
Infix ":::" := RetCons (at level 60, right associativity).
Infix "@" := Atm (no associativity, at level 50).
Infix "+" := add_pc.
Notation "'∂' pc" := (pc_lab pc) (at level 0).
Notation "x ∪ y" := (join_label x y) (right associativity, at level 55).
