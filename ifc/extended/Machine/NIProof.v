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
  if Mem.EqDec_block m1 m2 then true else false.

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

Definition isLow (l obs : Label) := flows l obs.

Definition is_low_pointer obs (a : Atom) : bool :=
  if a is Vptr p @ l then isLow l obs else false.

Definition extract_mframe (a : Atom) : option mframe :=
  if a is Vptr (Ptr fp _) @ _ then Some fp else None.

Definition mframes_from_atoms obs (atoms : list Atom) : {set mframe} :=
  [set t in pmap extract_mframe (filter (is_low_pointer obs) atoms)].

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

Lemma root_set_registers_upd obs pcl r rk r' atom atom' :
  registerContent r rk = Some atom ->
  registerUpdate r rk atom' = Some r' ->
  root_set_registers obs r' pcl \subset root_set_registers obs r pcl :|: mframes_from_atoms obs [:: atom'].
Proof.
admit.
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
+ move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> ? ? [<- <-] upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    have [? get_r2] : exists atom, registerContent r r2 = Some atom.
      admit.
    move/(subsetP (root_set_registers_upd _ _ get_r2 upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
+ move=> im μ σ pc r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    have [? get_r1] : exists atom, registerContent r r1 = Some atom.
      admit.
    move/(subsetP (root_set_registers_upd _ _ get_r1 upd_r1)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
+ move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> ? ? get_r1 [].
  rewrite /Vector.nth_order /= => <- <- upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    have [? get_r2] : exists atom, registerContent r r2 = Some atom.
      admit.
    move/(subsetP (root_set_registers_upd _ _ get_r2 upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
Abort.


End NIProof.