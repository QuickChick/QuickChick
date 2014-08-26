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

(* Interface with non-ssr definitions *)
Lemma replicateE T (a : T) n : replicate n a = nseq n a.
Proof.
by elim: n=> //= n ->.
Qed.

Definition def_atom := Vint 0 @ ⊥.

Lemma upd_natE r r' rk a : upd_nat r rk a = Some r' ->
  r' = set_nth def_atom r rk a.
Proof.
elim: r rk r' => // x l IHl [r' [<-]|rk] // [|y r'] /=.
  by case: (upd_nat l rk a)=> //.
case H: (upd_nat l rk a) => //; case=> <- <-.
by congr cons; apply: IHl.
Qed.

Lemma updE r r' rk a : registerUpdate r rk a = Some r' ->
  r' = set_nth def_atom r (BinInt.Z.to_nat rk) a.
Proof.
rewrite /registerUpdate /upd; case: (ZArith_dec.Z_lt_dec rk 0)=> // _.
exact: upd_natE.
Qed.

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
rewrite mem_pmap.
case/mapP=> a.
rewrite mem_filter.
case/andP => low_pt.
case/(nthP def_atom) => i.
(* TODO: use updE *)
admit.
Qed.

Arguments mframes_from_atoms_upd [obs r rk r' atom] _.

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

Lemma root_set_registers_nth r r1 fp i lbl obs pcl :
  registerContent r r1 = Some (Vptr (Ptr fp i) @ lbl) ->
  isLow pcl obs -> isLow lbl obs ->
  fp \in root_set_registers obs r pcl.
Proof.
move=> get_r1 low_pcl low_lbl.
rewrite /root_set_registers low_pcl.
rewrite inE.
rewrite mem_pmap.
apply/mapP.
exists (Vptr (Ptr fp i) @ lbl) => //.
rewrite mem_filter /= low_lbl. admit.
Qed.

Lemma root_set_registers_upd obs pcl r rk r' atom :
  registerUpdate r rk atom = Some r' ->
  root_set_registers obs r' pcl \subset root_set_registers obs r pcl :|: mframes_from_atoms obs [:: atom].
Proof.
rewrite /root_set_registers.
case: ifP => _; first exact: mframes_from_atoms_upd.
by rewrite sub0set.
Qed.

Lemma joinC : commutative join.
Proof.
move=> l1 l2.
by apply/flows_antisymm; rewrite join_minimal ?flows_join_left ?flows_join_right.
Qed.

Lemma flows_join l1 l2 l : flows (l1 \_/ l2) l = flows l1 l && flows l2 l.
Proof.
case Hl1: (flows l1 l).
  case Hl2: (flows l2 l).
    by rewrite (join_minimal _ _ _ Hl1 Hl2).
  by rewrite joinC (not_flows_not_join_flows_left _ _ _ Hl2).
by rewrite (not_flows_not_join_flows_left _ _ _ Hl1).
Qed.

Lemma low_join l1 l2 l : isLow (l1 \_/ l2) l = isLow l1 l && isLow l2 l.
Proof. exact: flows_join. Qed.

Lemma joinA : associative join.
Proof.
(* Cannot use wlog because of missing type class resolution *)
have: forall l1 l2 l3, l1 \_/ (l2 \_/ l3) <: (l1 \_/ l2) \_/ l3.
  move=> l1 l2 l3.
  rewrite flows_join.
  apply/andP; split; first exact/join_1/join_1/flows_refl.
  rewrite flows_join.
  apply/andP; split; first exact/join_1/join_2/flows_refl.
  exact/join_2/flows_refl.
move=> H l1 l2 l3.
apply/flows_antisymm; first exact:H.
rewrite [_ \_/ l3]joinC [l2 \_/ l3]joinC [l1 \_/ l2]joinC.
by rewrite [l1 \_/ (_ \_/ _)]joinC; apply: H.
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

Lemma stamp_alloc μ μ' sz lab stamp i li fp :
  alloc sz lab stamp (Vint i@li) μ = Some (fp, μ') ->
  Mem.stamp fp = stamp.
Proof.
rewrite /alloc /zreplicate.
case: (ZArith_dec.Z_lt_dec sz 0) => // lt0sz [alloc_sz].
by rewrite (Mem.alloc_stamp _ _ _ _ _ _ _ _ _ alloc_sz).
Qed.

Lemma reachable_alloc_int μ μ' sz lab stamp i li fp l f1 f2 :
  alloc sz lab stamp (Vint i@li) μ = Some (fp, μ') ->
  reachable l μ' f1 f2 = reachable l μ f1 f2.
Proof.
rewrite /alloc /zreplicate.
case: (ZArith_dec.Z_lt_dec sz 0) => // lt0sz.
rewrite replicateE => [[]] alloc_sz.
apply/eq_connect=> x y.
rewrite /references.
have [<-|neq_fpx] := fp =P x.
  (* How about using implicit arguments? *)
  rewrite (alloc_get_frame_eq _ _ _ _ _ _ alloc_sz) inE /=.
  rewrite (Mem.alloc_get_fresh _ _ _ _ _ _ _ _ _ alloc_sz).
  set s := filter _ _.
  have /eqP->//: s == [::].
  by rewrite -[_ == _]negbK -has_filter has_nseq andbF.
by rewrite (alloc_get_frame_neq _ _ _ _ _ _ _ alloc_sz neq_fpx).
Qed.

Arguments reachable_alloc_int [μ μ' sz lab stamp i li fp l f1 f2] _.

(*
Lemma reachable_alloc μ μ' sz lab stamp a fp l f1 f2 :
  alloc sz lab stamp a μ = Some (fp, μ') ->
  reachable l μ' f1 f2 = reachable l μ f1 f2 || (reachable l μ' f1 a && reachable l μ' a f2).

*)

Lemma well_formed_preservation st st' : well_formed st ->
  fstep default_table st = Some st' -> well_formed st'.
Proof.
move=> wf_st /fstepP step.
move: wf_st.
case: {st st'} step.
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
    move/(subsetP (mframes_from_atoms_upd upd_r1)).
    rewrite inE; case/orP=> [in_r'_f1|].
      by rewrite low_LPC' inE in_r'_f1 orbT in wf_st; apply: wf_st.
    case: a get_r1 upd_r1 => [?|[fp i]|?] get_r1 upd_r1; rewrite /mframes_from_atoms /= !inE //.
    case: ifP=> // low_B.
    rewrite /= inE => /eqP eq_f1.
    move: wf_st.
    rewrite eq_f1 (root_set_registers_nth get_r1); first exact.
      exact/(join_2_rev R)/(flows_trans _ _ _ Hjoins)/join_minimal.
    exact/(join_1_rev R LPC)/(flows_trans _ _ _ Hjoins)/join_minimal.
  by case: (isLow LPC' l) wf_st; rewrite ?inE in_stack_f1 !orbT; apply.
(* Alloc *)
+ move=> im μ μ' σ pc r r' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp -> ? get_r1 get_r2 [<- <-] alloc_i.
  move: (alloc_i); rewrite /alloc.
  case: (zreplicate i (Vint 0 @ ⊥)) => // ? [malloc].
  rewrite /Vector.nth_order /= => upd_r3 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /=.
  rewrite (reachable_alloc_int alloc_i) !inE => wf_st.
  case/orP=> [|in_stack_f1].
    rewrite /root_set_registers.
    case: ifP => low_LPC; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_r3)).
    rewrite inE.
    case/orP=> [in_r_f1|].
      by move: wf_st; rewrite /root_set_registers low_LPC in_r_f1; apply.
    rewrite /mframes_from_atoms /=.
    case low_KK': (isLow (K \_/ K') l); last by rewrite inE.
    rewrite /= !inE => /eqP ->.
    case/connectP=> [[_ ->|]] /=.
      by rewrite (stamp_alloc alloc_i) /= joinA low_join low_KK' low_LPC.
    move=> a s.
    by rewrite /references /= (Mem.alloc_get_fresh _ _ _ _ _ _ _ _ _ malloc).
  by move: wf_st; rewrite in_stack_f1 orbT; apply.
(* Load *)
+ move=> im μ σ pc C p K r r' r1 r2 j LPC v Ll rl rpcl -> ? get_r1 load_p mlab_p [<- <-].
  rewrite /Vector.nth_order /= => upd_r2 wf_st l f1 f2 /=.
  move: wf_st => /(_ l f1 f2) /=.
  rewrite !inE => wf_st.
  case/orP.
    rewrite /root_set_registers.
    case: ifP => low_LPCKC; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_r2)).
    rewrite inE; case/orP=> [in_r_f1|].
      move: low_LPCKC wf_st; rewrite /root_set_registers low_join => /andP [-> _].
      by rewrite in_r_f1; apply.
    rewrite inE /=; case: v load_p upd_r2 => // [[fp ?]] load_p upd_r2.
    case low_Ll: (isLow Ll l) => //=.
    rewrite !inE.

rewrite /load in load_p.
    
admit.
admit.
(* Store *)
admit.
(* Write *)
admit.
(* Jump *)
admit.
(* BNZ *)
admit.
(* BNZ *)
admit.
(* PSetOff *)
admit.
(* Put *)
admit.
(* BinOp *)
admit.
(* Nop *)
admit.
(* MSize *)
admit.
(* PGetOff *)
admit.
(* Mov *)
admit.
Qed.

End NIProof.