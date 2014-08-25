Require Import List. Import ListNotations.
Require Import String.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype finset.
Require Import path fingraph. (* This depends on Mathematical Components 1.5
                 http://www.msr-inria.fr/projects/mathematical-components-2/ *)


Require Import Utils Labels Rules Memory Instructions Machine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module NIProof (Lattice : FINLAT).

Module GenericMachine := MachineM Lattice.

Import GenericMachine.

Definition def_atom := Vint 0 @ ⊥.

Definition mframe_eq (m1 m2 : mframe) : bool :=
  Mem.EqDec_block m1 m2.

(* TODO: prove once mframe is actually made finite *)
Axiom f : mframe -> ordinal (2^32).
Axiom g : ordinal (2^32) -> mframe.
Axiom fgK : cancel f g.

Definition mframe_eqMixin := CanEqMixin fgK.
Canonical mframe_eqType := Eval hnf in EqType mframe mframe_eqMixin.

Definition mframe_choiceMixin := CanChoiceMixin fgK.
Canonical mframe_choiceType := Eval hnf in ChoiceType mframe mframe_choiceMixin.

Definition mframe_countMixin := CanCountMixin fgK.
Canonical mframe_countType := Eval hnf in CountType mframe mframe_countMixin.

Definition mframe_finMixin := CanFinMixin fgK.
Canonical mframe_finType := Eval hnf in FinType mframe mframe_finMixin.

Definition eqAtom (a1 a2 : Atom) :=
  match a1, a2 with
  | v1@l1, v2@l2 => EqDec_block v1 v2 && (LatEqDec _ l1 l2)
  end.

Lemma eqAtomP : Equality.axiom eqAtom.
Proof.
admit.
Qed.

Canonical Atom_eqMixin := EqMixin eqAtomP.
Canonical Atom_eqType := Eval hnf in EqType Atom Atom_eqMixin.

Definition isLow (l obs : Label) := flows l obs.

Definition is_low_pointer obs (a : Atom) : bool :=
  if a is Vptr p @ l then isLow l obs else false.

Definition extract_mframe (a : Atom) : option mframe :=
  if a is Vptr (Ptr fp _) @ _ then Some fp else None.

Definition mframes_from_atoms obs (atoms : list Atom) : {set mframe} :=
  [set t in pmap extract_mframe (filter (is_low_pointer obs) atoms)].

Lemma mframes_from_atoms_upd obs r rk r' atom :
  registerUpdate r rk atom = Some r' ->
  mframes_from_atoms obs r' \subset mframes_from_atoms obs r :|: mframes_from_atoms obs [:: atom].
Proof.
move=> upd_rk.
rewrite /mframes_from_atoms.
apply/subsetP=> x.
rewrite !inE /=.
admit.
Qed.

Fixpoint root_set_stack obs (s : Stack) : {set mframe} :=
  match s with
    | Mty => set0
    | RetCons (pc, _, rs, _) s' =>
      if isLow ∂pc obs then
        mframes_from_atoms obs rs :|: root_set_stack obs s'
      else root_set_stack obs s'
  end.

Definition root_set_registers obs (r : regSet) pcl :=
  if isLow pcl obs then mframes_from_atoms obs r
  else set0.

Lemma root_set_registers_upd obs pcl r rk r' atom :
  registerUpdate r rk atom = Some r' ->
  root_set_registers obs r' pcl \subset root_set_registers obs r pcl :|: mframes_from_atoms obs [:: atom].
Proof.
rewrite /root_set_registers.
case: ifP => _; first exact: mframes_from_atoms_upd.
by rewrite sub0set.
Qed.

Lemma joinC l1 l2 : l1 \_/ l2 = l2 \_/ l1.
Proof.
by apply/flows_antisymm; rewrite join_minimal ?flows_join_left ?flows_join_right.
Qed.

Lemma low_join l1 l2 l : isLow (l1 \_/ l2) l = isLow l1 l && isLow l2 l.
Proof.
rewrite /isLow.
case Hl1: (flows l1 l).
  case Hl2: (flows l2 l).
    by rewrite (join_minimal _ _ _ Hl1 Hl2).
  by rewrite joinC (not_flows_not_join_flows_left _ _ _ Hl2).
by rewrite (not_flows_not_join_flows_left _ _ _ Hl1).
Qed.

Lemma root_set_registers_join obs r l1 l2 :
  root_set_registers obs r (l1 \_/ l2) = root_set_registers obs r l1 :&: root_set_registers obs r l2.
Proof.
rewrite /root_set_registers /=.
rewrite low_join.
case: (isLow l1 obs); last by rewrite set0I.
case: (isLow l2 obs); first by rewrite setIid.
by rewrite setI0.
Qed.

Definition root_set obs (st : State) : {set mframe} :=
  let '(St _ _ s r pc) := st in
  root_set_registers obs r ∂pc :|: root_set_stack obs s.

Definition references obs (mem : memory) (f1 f2 : mframe) :=
  if Mem.get_frame mem f1 is Some (Fr _ l atoms) then
    f2 \in mframes_from_atoms obs atoms
  else false.

Definition reachable obs (mem : memory) : rel mframe :=
  connect (references obs mem).

Definition well_formed_label (st : State) (l : Label) :=
  forall f1 f2, f1 \in root_set l st -> reachable l (st_mem st) f1 f2 ->
  isLow (Mem.stamp f2) l.

Definition well_formed (st : State) :=
  forall l, well_formed_label st l.

Lemma well_formed_preservation st st' : well_formed st ->
  fstep default_table st = Some st' -> well_formed st'.
Proof.
move=> wf_st /fstepP step.
move: wf_st.
elim: {st st'} step.
(* Lab *)
+ move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> ? ? [<- <-] upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd _ _ upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* PcLab *)
+ move=> im μ σ pc r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd _ _ upd_r1)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* MLab *)
+ move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> ? ? get_r1 [].
  rewrite /Vector.nth_order /= => <- <- upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd _ _ upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* PutLab *)
+ move=> im μ σ pc r r' r1 j LPC rl rpcl l' -> ? [<- <-] upd_r1 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd _ _ upd_r1)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* Call *)
+ move=> im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl -> ? get_r1 get_r2 [<- <-] wf_st l f1 f2.
  rewrite /Vector.nth_order /=.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite root_set_registers_join !inE; case/orP.
    by case/andP=> _ in_regs_f1; apply: wf_st; rewrite inE in_regs_f1.
  rewrite low_join.
  case: ifPn=> [/andP [_ low_Lpc]|_ in_stack_f1].
    by rewrite /root_set_registers low_Lpc in wf_st *.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* BRet *)
+ move=> im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl -> -> ? get_r1.
  rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
  case: ifPn=> // Hjoins [<- <-] upd_r1 wf_st l f1 f2 /=.
  move: wf_st => /(_ l f1 f2) /=.
  rewrite !inE => wf_st.
  case/orP=> [|in_stack_f1].
    rewrite /root_set_registers; case: ifP => low_LPC'; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd _ upd_r1)).
    rewrite inE; case/orP=> [in_r'_f1|].
      by rewrite low_LPC' inE in_r'_f1 orbT in wf_st; apply: wf_st.
    have r1_in_r: a@R \in r by admit.
    case: a get_r1 upd_r1 r1_in_r => [?|[fp i]|?] get_r1 upd_r1 r1_in_r; rewrite /mframes_from_atoms /= !inE //.
    case: ifP=> // low_B.
    rewrite /= inE => /eqP eq_f1.
    rewrite /root_set_registers in wf_st.
    have low_RLPC: isLow (R \_/ LPC) l.
      exact/(flows_trans _ _ _ Hjoins)/join_minimal.
    rewrite low_join in low_RLPC.
    case/andP: low_RLPC => low_R low_LPC.
    have in_r_fp: f1 \in mframes_from_atoms l r.
      rewrite eq_f1 inE.
      rewrite mem_pmap.
      apply/mapP.
      exists (Vptr (Ptr fp i) @ R) => //.
      by rewrite mem_filter /= low_R r1_in_r.
    by rewrite low_LPC in_r_fp in wf_st; apply: wf_st.
  by case: (isLow LPC' l) wf_st; rewrite ?inE in_stack_f1 !orbT; apply.
(* Alloc *)
Abort.


End NIProof.