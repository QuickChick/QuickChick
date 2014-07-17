Require Import QuickChick SetOfOutcomes.

Require Import Common Machine Generation GenerationProofsHelpers. 

Require Import List.
Require Import ZArith.  
Require Import EquivDec.

Require Import ssreflect ssrbool ssrnat eqtype.


Lemma gen_from_length_correct: forall l,
  (gen_from_length l) <--> (fun z => (Z.le 0 z /\ Z.le z (l-1))).
Proof.
  move => l z. rewrite /gen_from_length choose_def. 
  split => [[/Z.compare_le_iff H1 /Z.compare_ge_iff H2]|
            [/Z.compare_le_iff H1 /Z.compare_ge_iff H2]];
    by split; auto.
Qed.

Lemma gen_from_nat_length_correct: forall l,
  (gen_from_nat_length l) <--> (fun z => (Z.le 0 z /\ Z.le z ((Z.of_nat l)-1))).
Proof.
  move => l z.
  rewrite /gen_from_nat_length. 
  move/(_ (Z.of_nat l)): gen_from_length_correct; apply. 
Qed.

Lemma gen_BinOpT_correct : 
  peq gen_BinOpT all.
Proof.
  rewrite /gen_BinOpT /all. move => op. 
  split => // _.  
  apply oneof_equiv. left. 
  case : op; [exists (pure BAdd) | exists (pure BMult)]; split => //=;
  [|right]; by left.
Qed.

Lemma gen_label_correct : 
  forall (l : Label),
    (gen_label l) <--> (fun e => In e (allThingsBelow l)).
Proof.
  move=> l. rewrite /gen_label. move => l'. 
  split => [/elements_equiv [H1 | [H1 H2]] //= | HIn]; subst.   
  + rewrite /allThingsBelow  /allBelow in H1. apply map_eq_nil in H1.
    by move/powerset_nonempty : H1.
  + apply elements_equiv. by left.
Qed.

Section WithDataLenNonEmpty.

Variable inf : Info.
Hypothesis data_len_nonempty : data_len inf <> [].


Lemma gen_label_inf_correct :
  (gen_label_inf inf) <--> (fun e => In e (allThingsBelow (top_prin inf))).
Proof.
  apply/gen_label_correct.
Qed.

(* PC *)

Definition PC_spec (pc : Ptr_atom) :=
  let '(PAtm z l) := pc in
  (In l (allThingsBelow (top_prin inf))) /\ 
  (0 <= z <= (code_len inf) - 1)%Z.

Lemma gen_PC_correct: 
  (gen_PC inf) <--> PC_spec.
Proof. 
  move=> ptr. rewrite /gen_PC /smart_gen /smart_gen_label.
  split.
  + rewrite bindGen_def. move => [lab [gen_lab H]]. 
    move/gen_label_inf_correct: gen_lab.
    rewrite bindGen_def in H. 
    move : H => [z [/gen_from_length_correct H1 Hret]].
    rewrite returnGen_def in Hret. subst. by split.
  + case : ptr => z l. move => [Hin Hrng]. 
    rewrite bindGen_def. exists l; split.
    by apply /gen_label_inf_correct.
    rewrite bindGen_def. exists z; split => //.
    by apply /gen_from_length_correct.
Qed.


(* Pointer *)
Definition Pointer_spec (ptr : Pointer) :=
  let '(Ptr mf addr) := ptr in
  (exists len, In (mf, len) (data_len inf) /\ 
               (0 <= addr <= len - 1)%Z). 

Lemma gen_Pointer_correct: 
    (gen_Pointer inf) <--> Pointer_spec.                        
Proof. 
  move => ptr. remember inf as Inf.
  destruct Inf.
  rewrite /gen_Pointer.
  split.
  * rewrite bindGen_def. move => [[mf z] [/elements_equiv Helem  H]].
    rewrite bindGen_def in H. move : H => [a [/gen_from_length_correct H Hret]].
    rewrite returnGen_def in Hret. subst ptr.
    simpl. case : Helem => [HIn | [Heq1 [Heq2 Heq3]]].
    - exists z. split => //. rewrite -HeqInf. assumption. 
    - by subst.
  * case: ptr => mf z.
    destruct data_len as [| x xs].
    - rewrite bindGen_def. 
      move=> [len  [//= HIn Hrng]].
    -  Opaque bindGen choose Z.compare returnGen. 
       move=> [len  [//= HIn [Hrng1 Hrng2]]].
       rewrite bindGen_def.  
       exists (mf, len). split.
       apply/elements_equiv. 
       by left; rewrite -HeqInf in HIn. 
       rewrite bindGen_def. 
       exists z. split => //. split. by apply/Z.compare_le_iff. 
       by apply/Z.compare_ge_iff.
Qed.

(* Value *)

Definition val_spec (inf : Info) (v : Value) :=
  match v with 
    | Vint _ => True
    | Vptr ptr =>
      let '(Ptr mf addr) := ptr in
      (exists len, In (mf, len) (data_len inf) /\ 
                   (0 <= addr <= len - 1)%Z) 
    | Vcptr z => (0 <= z <= (code_len inf) - 1)%Z
    | Vlab l => In l (allThingsBelow (top_prin inf))
  end.


Lemma gen_value_correct:  
    (gen_Value inf) <--> (val_spec inf).
Proof. 
  rewrite /gen_Value /val_spec.  
  clear data_len_nonempty. remember inf as Inf.
  case : Inf HeqInf => def clen dlen top reg HeqInf. case; rewrite !HeqInf.
  + (* VInt *) 
    move => z. split => // _. apply/frequency_equiv.
    left. exists 1. eexists. split. by constructor.
    split => //.
    rewrite liftGen_def. eexists; split => //.
    apply/frequency_equiv. left.
    exists 10. exists arbitrary. split. by constructor.
    split => //. by apply/arbInt_correct.
  + (* Vptr *)  
    case => mf addr.   
    split. Opaque bindGen choose Z.compare returnGen gen_Pointer.    
    - move/frequency_equiv => [[n [ g [H1 [H2 H3]]]] | [[// | H1] H2]]. 
      * case:H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | 
                                   [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
        subst n g; try (subst Heq1 Heq2);
        try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]);
        try discriminate.  
        move/gen_Pointer_correct: H2 H2' => H2 [H2']; subst.
        move : H2 => //= [len [ HIn Hrng]]. exists len. split => //.
        by rewrite -HeqInf in HIn.
      * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
    - move => [len [HIn [Hrng1 Hrg2]]].
      apply/frequency_equiv. left. exists 1. eexists. 
      split. apply in_cons.  apply in_cons. constructor. 
      reflexivity.
      rewrite liftGen_def. split => //. eexists.
      split => //. 
      apply gen_Pointer_correct. exists len. split => //.
   + (* Vcptr *)
     move => addr. split. 
     - move/frequency_equiv => [[n [g [H1 [H2 H3]]]] | [H1 H2]]. 
       * case: H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
         subst; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]); 
         try discriminate.
         move : H2 H2' => [/Z.compare_le_iff H1 /Z.compare_ge_iff H2] [H2']; subst.
         by split.
       * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
     - move => [/=  H1  H2].
       apply/frequency_equiv. left. exists 1. eexists. split. 
       apply in_cons. constructor. 
       reflexivity. 
       rewrite liftGen_def. split => //. exists addr. split => //=. 
       split. by apply/Z.compare_le_iff. 
       rewrite -HeqInf /= in H2.
       by apply/Z.compare_ge_iff.
   + (* Vlab *)
     move => L. split.
     - move/frequency_equiv => [[n [g [H1 [H2 H3]]]] | [H1 H2]].
       * case: H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
         subst g n; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]);
         try discriminate.  
         by move : H2 H2' => /gen_label_inf_correct H1 [H2']; subst.
       * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
     - move => H. apply/frequency_equiv. left. exists 1. eexists.
       split. apply in_cons. apply in_cons. apply in_cons. constructor. 
       reflexivity.
       rewrite liftGen_def. split => //. exists L. split => //=.
       by apply/gen_label_inf_correct.
Qed.
      
(* Atom *) 

Definition atom_spec inf atm  := 
  let '(Atm val lab) := atm in
  val_spec inf val /\ 
  In lab (allThingsBelow (top_prin inf)).
       
Lemma gen_atom_correct:
    (gen_atom inf) <--> (atom_spec inf).
Proof.
  move => atm. rewrite /gen_atom /liftGen2 bindGen_def. case: atm => val lab. 
  split. 
  + move => [val' [/gen_value_correct Hval Hbind]].
    rewrite bindGen_def in Hbind.
    move : Hbind => [lab' [/gen_label_inf_correct Hlab Hret]].
    rewrite returnGen_def in Hret. 
    by move : Hret => [Heq1 Heq2]; subst.
  + move => [Hval Hlab].
    exists val. split; [by apply/gen_value_correct| ].
    rewrite bindGen_def. exists lab. split => //.
    by apply/gen_label_inf_correct.
Qed.
  
(* regSet  *)

Definition regs_spec inf regs :=
  (length regs = no_regs inf) /\
  (forall reg, 
     In reg regs ->
     let '(Atm val lab) := reg in
     val_spec inf val /\ 
     In lab (allThingsBelow (top_prin inf))).

Lemma gen_registers_correct:
  (gen_registers inf) <--> (regs_spec inf).
Proof.    
  move => regs. 
  rewrite /gen_registers. split.
  + move /vectorOf_equiv => [H1 H2].
    split => //. move => reg HIn. by apply/gen_atom_correct; apply H2. 
  + move => [Hlen Hregs]. apply/vectorOf_equiv. split => // x HIn.
    apply/gen_atom_correct. by apply Hregs.
Qed.

(* stack_loc *)

Definition stack_loc_spec (inf : Info) g (l1 l2: Label) t : Prop:=
  let '(ptr_a, lab, regs, ptr_r) := t in
  In lab (allThingsBelow (top_prin inf)) /\
  regs_spec inf regs /\
  (0 <= ptr_r <= (Z.of_nat (no_regs inf) - 1))%Z /\
  let 'PAtm addr lab' := ptr_a in
  (0 <= addr <= ((code_len inf) - 1))%Z /\
  g l1 l2 lab'.

Lemma gen_stack_loc_correct :
  forall f g l1 l2, 
    (f l1 l2) <--> (g l1 l2) ->
    (smart_gen_stack_loc f l1 l2 inf) <--> (stack_loc_spec inf g l1 l2).
Proof.
  move=> f g l1 l2 Hequiv. 
  rewrite /smart_gen_stack_loc /smart_gen /bindGen /returnGen 
          /PredMonad /bindP /returnP //=.
  move => [[[ptr_a lab] regs] ptr_r]. split.
  + move =>  
    [regs' [/gen_registers_correct Hregs 
             [ptr_a' [[lab' [/gen_label_inf_correct Hlab H']]
                      [z [[/Z.compare_le_iff H1 /Z.compare_ge_iff H2] H]]]]]].
    move: H => [a [/gen_label_inf_correct Hlab' [lab'' [fl1l2 Hret]]]].
    case: ptr_a' lab' Hret Hlab H' => addr_a' lab_a' lab' Hret' Hlab H'.
    move : Hret' => [Heq1 Heq2 Heq3 Heq4]; subst.
    rewrite  /bindGen /returnGen /PredMonad /bindP /returnP //= in H'.
    move: H' => [z' [[/Z.compare_le_iff H1' /Z.compare_ge_iff H2'] [Heq1 Heq2]]]; subst.
    repeat (split  => //=; by auto). split => //=. split => //=. split => //=.
    split => //=. auto. auto. by apply Hequiv.
  + case: ptr_a. move => addr_a l_a [H1 [H2 [[H3 H3'] [[H4 H5] H6]]]].
    eexists; split. by apply/gen_registers_correct. 
    eexists; split. exists lab. split.
    by apply /gen_label_inf_correct.
    rewrite bindGen_def. 
    exists addr_a. split. 
    split. by apply/Z.compare_le_iff. 
    by apply/Z.compare_ge_iff. rewrite returnGen_def. reflexivity.
    exists ptr_r. split. split. 
    by apply/Z.compare_le_iff. by apply/Z.compare_ge_iff.
    exists lab. split. by apply /gen_label_inf_correct.
    exists l_a. split => //=. by apply Hequiv.
Qed.
   
(* gen_label_between_lax *)

Lemma gen_label_between_lax_correct :
  forall l1 l2,
    (gen_label_between_lax l1 l2) <--> (fun l => 
                                          (l1 <: l /\ In l (allThingsBelow l2))
                                          \/ l = l2 /\ l1 <: l2 = false).
Proof.
  move => l1 l2 l.  rewrite /gen_label_between_lax. split. 
  + move/elements_equiv => [ /filter_In [H1 H2] | 
                             [/filter_nil [/allThingsBelow_nonempty //| H1] H2]]. subst.  
    by left. 
    right. split => //=. apply H1. 
    rewrite /allThingsBelow /allBelow. (* Search _ (map _ _) In. *)
    rewrite -[X in In X _]label_of_list__elements. apply in_map.
    by apply powerset_in_refl.
  + move => [[H1 H2] | [H1 H2]]; subst; apply elements_equiv.
    by left; apply filter_In.
    right.  split => //. apply filter_nil.  
    right => x /allThingsBelow_isLow In.
    remember (l1 <: x) as b. symmetry in Heqb. case: b Heqb => heqb //.
    have H : l1 <: l2 = true by eapply flows_trans; eauto.
    congruence. 
Qed.

Definition gen_label_between_lax_spec (l1 l2 l: Label) : Prop := 
  (l1 <: l /\ l <: l2) \/ l = l2 /\ l1 <: l2 = false.


Lemma gen_label_between_lax_correct_admited :
  forall l1 l2,
    (gen_label_between_lax l1 l2) <--> (gen_label_between_lax_spec l1 l2).
Proof.
  move => l1 l2 l.  rewrite /gen_label_between_lax. split. 
  + move/elements_equiv => [ /filter_In [H1 H2] | 
                             [/filter_nil [/allThingsBelow_nonempty //| H1] H2]]; subst.  
    - left; split => //. by apply/allThingsBelow_isLow.
    - right. split => //=. apply H1. 
      rewrite /allThingsBelow /allBelow.
      rewrite -[X in In X _]label_of_list__elements. apply in_map.
        by apply powerset_in_refl.
  + move => [[H1 H2] | [H1 H2]]; subst; apply elements_equiv.
    left. apply filter_In. split => //.
    by apply/allThingsBelow_isLow'.  (* Here is the admited part *)
    right. split => //. apply filter_nil.  
    right => x /allThingsBelow_isLow In. 
    remember (l1 <: x) as b. symmetry in Heqb. case: b Heqb => heqb //.
    have H : l1 <: l2 = true by eapply flows_trans; eauto.
    congruence.  
Qed.

(* Stack *)

Definition stack_spec (pc: Ptr_atom) inf (s: Stack) : Prop :=
  s = Mty \/ 
  exists loc, s = loc ::: Mty /\ 
              stack_loc_spec inf gen_label_between_lax_spec bot ∂pc loc.

Lemma gen_stack_correct: 
  forall (pc: Ptr_atom),
    (smart_gen_stack pc inf) <--> (stack_spec pc inf). 
Proof.
  Opaque smart_gen_stack_loc.
  rewrite /smart_gen_stack /stack_spec. move => pc st.
  split. 
  + move/frequency_equiv => [[n [gen [[[Heq1 Heq2] | [[Heq1 Heq2] | //]] [Hg Hneq]]]] | 
                             [[H1 //= | H1] H2]]; subst.
    by left; rewrite Hg. 
    rewrite bindGen_def in Hg. move: Hg => [loc (* [[[ptr_a l] regs] reg_ptr] *) 
                                              [/gen_stack_loc_correct H1 H2]].
    rewrite returnGen_def in H2. subst. right.
    exists loc.  split => //. apply H1.
    apply gen_label_between_lax_correct_admited.
    by left; rewrite H2. 
  +  move => [Heq | H]; subst; apply frequency_equiv.
     - left; eexists; eexists; split. by constructor. by split => //.
     - case: st H => [H |loc st [loc' [[H1] H2]]]; left; eexists; eexists; split; subst.
       * by constructor. by split => //.
       * by apply in_cons; constructor. 
         rewrite bindGen_def. split => //. exists loc'.
         split => //. eapply gen_stack_loc_correct.
         by apply (gen_label_between_lax_correct_admited ⊥ ∂(pc)).
         assumption.
Qed.

(* frame *)    

Definition mem_single_upd_spec (inf : Info) mem mf (mem' : memory) := 
  match Mem.get_frame mem mf with 
    | Some (Fr stamp lab data) => 
      exists fr, Mem.upd_frame mem mf fr = Some mem' /\
                 let 'Fr stamp' lab' data' := fr in 
                 lab' = lab /\ stamp' = stamp /\ 
                 length data' = length data /\ 
                 forall atm, In atm data' -> atom_spec inf atm
    | None => mem' = mem
  end. 
  

Lemma populate_frame_correct : 
  forall mem mf,
    (populate_frame inf mem mf) <--> (mem_single_upd_spec inf mem mf).
Proof. 
  move=> mem mf mem'.  rewrite /populate_frame /mem_single_upd_spec.
  remember (Mem.get_frame mem mf) as opt. 
  case: opt Heqopt => [fr | ] Heqopt. 
  case: fr Heqopt => stamp lab data Heq. 
  - rewrite bindGen_def. 
    symmetry in Heq. move/Mem.upd_get_frame : (Heq) => Hupd.
    split. 
    + move => [atmlst [/vectorOf_equiv [Hl Hvec] Hmatch]]. 
      move/(_ (Fr stamp lab atmlst)): Hupd => [fr Hfr].
      rewrite Hfr returnGen_def in Hmatch; subst.
      exists (Fr stamp lab atmlst). repeat split => //.
      move => atm HIn. apply/gen_atom_correct. by apply Hvec.
    + move => [fr [Hget H]]. 
      case: fr Hupd Hget H => 
        stamp' lab' data' Hupd Hget [Heq1 [Heq2 [Heq3 H]]]; subst.
      exists data'. split. 
      apply/vectorOf_equiv. split => // x HIn. by apply/gen_atom_correct; eauto.
      by rewrite Hget.
  - by rewrite /pure returnGen_def.
Qed.

(* Instruction *)

Definition Instruction_spec (st : State) instr := 
  let '(St im m pr stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [] [] [] [] Z0 in
  match instr with 
    | Nop => True | Halt => False
    | PcLab z | PutBot z | Put _ z => (0 <= z <= (Zlength regs -1))%Z
    | Lab z1 z2 => 
      (0 <= z1 <= (Zlength regs-1))%Z /\ (0 <= z2 <= (Zlength regs-1))%Z
    | MLab z1 z2 | Load z1 z2 | Store z1 z2 | MSize z1 z2 | PGetOff z1 z2 => 
      dptr <> [] /\ In z1 dptr /\  (0 <= z2 <= (Zlength regs-1))%Z
    | FlowsTo z1 z2 z3 | LJoin z1 z2 z3 => 
      lab <> [] /\ In z1 lab /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BCall z1 z2 z3 => 
      cptr <> [] /\ lab <> [] /\  
      In z1 cptr /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BRet => (containsRet stk = true) 
    | Alloc z1 z2 z3 =>
      num <> [] /\ lab <> [] /\  
      In z1 num /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Jump z => cptr <> [] /\ In z cptr
    | BNZ z1 z2 => num <> [] /\ (-1 <= z1 <= 2)%Z /\ In z2 num
    | PSetOff z1 z2 z3 =>
      dptr <> [] /\ num <> [] /\  
      In z1 dptr /\ In z2 num /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Output z1 => 
      num <> [] /\ In z1 num  
    | BinOp _ z1 z2 z3 => 
      num <> [] /\ In z1 num /\ In z2 num /\ (0 <= z3 <= (Zlength regs-1))%Z 
  end. 

Ltac discr_gen_eq :=
  match goal with 
    | H : (_, liftGen ?f ?gen) = (?n, ?g),
      Hg : ?g _ |- _ => 
        move : H => [Heq1 Heq2]; subst;
        rewrite liftGen_def in Hg; move: Hg => [a [_ H]]; discriminate
    | H : (_, returnGen ?a) = (?n, ?g),
      Hg : ?g _ |- _ => 
        move : H => [Heq1 Heq2]; subst; discriminate
    | H : (_, liftGen2 ?f ?gen1 ?gen2) = (?n, ?g),
      Hg : ?g _ |- _ => 
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen2_def in Hg;
      move: Hg => [a [_ [a' [_ H]]]]; subst; discriminate
    | H : (_, liftGen3 ?f ?gen1 ?gen2 ?gen3) = (?n, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen3_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ H]]]]]]; subst; discriminate
    | H : (_, liftGen4 _ _ _ _ _) = (_, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen4_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ [a''' [ _ H]]]]]]]]; subst; discriminate

  end.

Ltac discr_or_first := 
  match goal with 
    | HIn : ((_, _) = (_ , _) \/ _) |- _ =>  case: HIn => [Heq | HIn]; [discr_gen_eq | ]
    | HIn : In (_, _) _ |- _ => case: HIn => [Heq | HIn]; [discr_gen_eq | ]
  end.
 

Ltac unfold_gen := 
  match goal with
    | Hg : returnGen _ _ |- _ =>
      rewrite returnGen_def in Hg; subst
    | Hg : liftGen _ _ _ |- _ => 
      rewrite liftGen_def in Hg; move: Hg => [b [H1 [Heq]]]; subst
    | Hg : liftGen2 _ _ _ _ |- _ => 
      rewrite liftGen2_def in Hg; 
        move: Hg => [b [H1 [b' [H2 [Heq1 Heq2]]]]]; subst
    | Hg : liftGen3 _ _ _ _ _ |- _ => 
      rewrite liftGen3_def in Hg; 
        move: Hg => [b [H1 [b' [H2 [b'' [H3 [Heq1 Heq2 Heq3]]]]]]]; subst
    | Hg : liftGen4 _ _ _ _ _ _ |- _ => 
      rewrite liftGen4_def in Hg; 
       move: Hg=>[b [H1 [b' [H2 [b'' [ H3 [b''' [H4 [Heq1 Heq2 Heq3 Heq4]]]]]]]]]; subst
  end.


Ltac find_instr instr lst k :=
  match lst with
    | nil => k 0 (pure Nop) 
    | (?n, liftGen4 ?c ?a1 ?a2 ?a3 ?a4) :: ?lst' => (* match with liftGen4 *)
      match instr with
        | c _ _ _ _ => k n (liftGen4 c a1 a2 a3 a4)
        | _ => find_instr instr lst' k
      end 
    | (?n, liftGen3 ?c ?a1 ?a2 ?a3) :: ?lst' => (* match with liftGen3 *)
      match instr with
        | c _ _ _ => k n (liftGen3 c a1 a2 a3)
        | _ => find_instr instr lst' k
      end 
    | (?n, liftGen2 ?c ?a1 ?a2) :: ?lst' => (* match with liftGen2 *)
      match instr with
        | c _ _  => k n (liftGen2 c a1 a2)
        | _ => find_instr instr lst' k 
      end
    | (?n, liftGen ?c ?a1) :: ?lst' => (* match with liftGen *)
      match instr with
        | c _  => k n (liftGen c a1)
        | _ => find_instr instr lst' k
      end
    | (?n, ?f ?c) :: ?lst' => (* match with pure/returnGen *)
      match instr with
        | c  => k n (f c)
        | _ => find_instr instr lst' k
      end
  end. 


Ltac instantiate_exists :=
  match goal with 
    | |- exists n g, In (n, g) ?lst /\ _ ?cnstr /\ _ =>
      find_instr cnstr lst ltac:(fun n g => pose cnstr; exists n; exists g);
      split; [repeat ((try by apply in_eq); apply in_cons) | split => //]
  end.

Ltac try_solve2 := 
  match goal with 
    | Hand : _ /\ _ |- _ => destruct Hand; by try_solve2
    | |- _ = _ => reflexivity
    | |- _ /\ _ => split; [| by try_solve2]; by try_solve2
    | |- liftGen4 _ _ _ _ _ _ => rewrite liftGen4_def; by try_solve2
    | |- liftGen3 _ _ _ _ _ => rewrite liftGen3_def; by try_solve2
    | |- liftGen2 _ _ _ _ => rewrite liftGen2_def; by try_solve2
    | |- liftGen _ _ _ => rewrite liftGen_def; by try_solve2
    | |- elements _ _ _ => apply/elements_equiv; left; by try_solve2
    | |- choose _ _ => rewrite choose_def => /=; by try_solve2
    | |- ~ (_ ?= _)%Z = Lt => by apply/Z.compare_ge_iff
    | |- ~ (_ ?= _)%Z = Gt  => by apply/Z.compare_le_iff
    | |- ~ onNonEmpty ?l _ = 0 => by destruct l
    | |- exists _, _ => eexists; by try_solve2
    | |- ~ (( _ * onNonEmpty ?c _)%coq_nat * onNonEmpty ?l _)%coq_nat = 0 =>
        by destruct c; destruct l
    | |- gen_BinOpT _ => by apply gen_BinOpT_correct
    | |- ~ (if ?b then _ else _) = 0 => by destruct b
    | _ => by []
  end. 

Ltac try_solve :=
      match goal with 
        | |- _ /\ _ => split => //=; by try_solve
        | Hand : _ /\ _ |- _ => destruct Hand; by try_solve
        | Hor : _ \/ _ |- _ => destruct Hor; by try_solve
        | |- ~ _ => move => contra; subst; by try_solve
       | Hchoose : choose _ _ |- _ =>
          rewrite choose_def /= in Hchoose; by try_solve
        | Helem : elements _ _ _ |- _ => 
          move/elements_equiv : Helem => [Helem //= | [Helem1 Helem2] //=]; subst;
          by try_solve 
 
        | HIn: In _ [] |- _ => by []
        | Hnonempty : ~ (onNonEmpty [] _ = 0) |- _ =>
           by rewrite /onNonEmpty in Hnonempty
        | Hnonempty : ~ (_ * (onNonEmpty [] _))%coq_nat = 0 |- _ => 
            by rewrite [X in (_ * X)%coq_nat]/onNonEmpty -mult_n_O in Hnonempty
        | Hif: ~ ((if ?b then _ else _ ) = _) |- ?b = true =>
            by case: b Hif
        | |- (_ <= _)%Z => by apply/Z.compare_ge_iff
        | |- (_ <= _)%Z => by apply Z.compare_le_iff
        | |- _ => by []
      end. 


(* Lemma gen_ainstrSSNI_correct : *)
(*   forall (st : State), (ainstrSSNI st) <--> (Instruction_spec st). *)
(* Proof. *)
(*   move=> st instr. rewrite /ainstrSSNI /Instruction_spec. *)
(*   case: st => im m pr stk regs pc. *)
(*   set st := {| *)
(*              st_imem := im; *)
(*              st_mem := m; *)
(*              st_pr := pr; *)
(*              st_stack := stk; *)
(*              st_regs := regs; *)
(*              st_pc := pc |}. *)
(*   case: (groupRegisters st regs [] [] [] [] Z0)=> [[[dptr cptr] num] lab]. *)
(*   split.   *)
(*   - case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 | *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 | *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; *)
(*     move /frequency_equiv =>  [[n [g [HIn [Hg Hn]]]] | [[H | H] H' //=]]; *)
(*     rewrite /gen_from_length /pure in HIn; repeat discr_or_first; *)
(*     by (case: HIn => [[Heq1 Heq2] | HIn]; subst;   *)
(*      [by unfold_gen; try_solve | by repeat discr_or_first]). *)
(*  -  Opaque mult choose. *)
(*     case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 | *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 | *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; *)
(*                    move => H; apply frequency_equiv; left;  *)
(*     instantiate_exists; try rewrite /gen_from_length; try by try_solve2. *)
(*     rewrite liftGen2_def. eexists. split; [| try_solve2]. *)
(*     rewrite /arbitrary /arbInt. by apply arbInt_correct. *)
(* Qed. *)


(* Proofs for variations *) 
Require Import Indist.

(* Vary Atom *)
Lemma gen_vary_atom_correct :
  forall (l : Label) (a : Atom),
    let 'v @ la := a in 
    val_spec inf v -> 
    (gen_vary_atom l inf a) <--> (fun a' => 
                                    let 'v' @ la' := a' in 
                                    indist l a a' /\ val_spec inf v').
Proof.  
  move=> l a. case: a => va la.
  move=> Hspec; case => va' la'.
  rewrite /gen_vary_atom /indist /indistAtom /isHigh /isLow.  
  case: (la <: l). 
  + (* la lower that observability level *) 
    split.  
    * (* Correctness *)
      rewrite returnGen_def. move  => [Heq1 Heq2]; subst.  
      split => //. apply/andP; split. 
      by rewrite /label_eq; apply/andP; split; apply flows_refl. 
      apply/orP. right. rewrite /indist /indistValue /val_spec in Hspec *.   
      case: va' Hspec => [i' | Ptr' | i' | lv'] Hspec;
      repeat
      (match goal with 
        | |-  is_true (Z_eq ?n ?n) => 
          rewrite /Z_eq; by case (Z.eq_dec n n)
        | |- is_true (label_eq ?l ?l) => 
          rewrite /label_eq; apply/andP; split; apply flows_refl
        | |- _ => 
          case Ptr' => fp z; apply/andP; split; 
          [rewrite /mframe_eq; case: (Mem.EqDec_block fp fp) => //=; congruence |]
       end).   
    * (* Completeness *)
      move=> [/andP [/andP [Hflows1 Hflows2] /orP [H1 //= | H1]] H2]. 
      rewrite /indist /indistValue in H1. rewrite returnGen_def. 
      move: (flows_antisymm _ _ Hflows2 Hflows1) => Heq; subst.
      case: va Hspec H1 H2 => [i | ptr | i | lv];  
      case: va' => [i' | ptr' | i' | lv'] => // Hspec H1 H2; try 
       match goal with 
         | H : is_true (Z_eq ?i ?i') |- _ => 
           rewrite /Z_eq in H; by case : (Z.eq_dec i i') H => Heq H;  subst
         | H: is_true (match ?p with Ptr _ _ => false end) |- _ => by destruct p
         | H: is_true (label_eq ?l ?l') |- _ => 
           rewrite /label_eq in H; move/andP : H => [Hf1 Hf2]; 
           by move: (flows_antisymm _ _ Hf1 Hf2) => Heq; subst
       end. 
      case: ptr H1 {Hspec H2}; case : ptr' => fp z fp' z' /andP [H1 H2].
      rewrite /Z_eq in H2. rewrite /mframe_eq in H1.
      case: (Z.eq_dec z' z) H2 => //=; case: (Mem.EqDec_block fp' fp) H1 => //=.
      rewrite /equiv. by move => -> _ ->  _.
  + (* la higher than observable state *)
    rewrite bindGen_def. 
    split.    
    * (* Correctness *) 
      case: va Hspec=> [i | ptr | i | lv];  case: va' => [i' | ptr' | i' | lv'];
      move => Hpec [val [Hgen Hret]];
      rewrite returnGen_def in Hret; move : Hret => [Heq1 Heq2]; subst;
      (split; [apply/andP; split => //; rewrite /label_eq; apply/andP; split; 
                 by apply/flows_refl | 
               by apply gen_value_correct in Hgen]).
    * (* Completeness *) 
      move=> [/andP[/andP [H1 H2] /orP [_| H3]]   H];
      move: (flows_antisymm _ _ H2 H1) => Heq; subst;
      exists va'; split => //; by apply gen_value_correct.
Qed.
  
(* Vary Ptr_atom *)

Lemma gen_vary_pc_correct: 
  forall (obs: Label) (pc : Ptr_atom),
    (PC_spec pc) ->
    (gen_vary_pc obs inf pc) <--> (fun pc' =>
                                       indist obs pc pc' /\ PC_spec pc').
Proof.
  move => obs pc Hspec pc'.
  rewrite /gen_vary_pc /indist /indistPtrAtm /isHigh /isLow /pure. 
  case: pc Hspec => z lpc; case: pc' => z' lpc' Hspec.
  split. 
  + (* Correctness *)   
    remember (lpc <: obs) as b; 
    remember (lpc' <: obs) as b'.
    case: b Heqb; case: b' Heqb' => Heqb' Heqb.
    - move => [Heq Heq']; subst. split => //=.
      apply/andP. split. rewrite /label_eq. 
      by apply/andP; split; apply/flows_refl.
      rewrite /Z_eq. by case: (Z.eq_dec z' z').
    - move => [Heq Heq']; subst. congruence. 
    - rewrite bindGen_def. move => [pc'' [Hspec'' H]]. 
      case: pc'' Hspec'' H => z'' lpc''. 
      rewrite returnGen_def. move=> Hspec''. remember (lpc'' <: obs) as b''.
      case : b'' Heqb'' => Heqb'' ; move => [Heq1 Heq2]; subst; symmetry in Heqb. 
      * apply not_flows_not_join_flows_right with (l1 := lpc'') in Heqb.
        rewrite /join /ZsetLat -Heqb' in Heqb. congruence.
      * congruence.
    - rewrite bindGen_def. move => [pc'' [Hspec'' H]]. 
      case: pc'' Hspec'' H => z'' lpc'' /gen_PC_correct Hspec''.
      remember (lpc'' <: obs) as b''.
      case : b'' Heqb'' => Heqb''; move => [Heq1 Heq2]; subst;  
      symmetry in Heqb; split => //. 
      * rewrite /PC_spec -/Zset.union in Hspec'' Hspec *. 
        move : Hspec'' Hspec => [/allThingsBelow_isLow HIn'' Hrng] 
                                [/allThingsBelow_isLow HIn _].
        split => //=.
        apply/allThingsBelow_isLow'. (* This is admited ..*)
        by apply/join_minimal.
  + (* Completeness *)   
    Opaque PC_spec. remember (lpc <: obs) as b; 
    remember (lpc' <: obs) as b'.
    case: b Heqb; case: b' Heqb' => Heqb' Heqb [H1 H2] //.
    + move : H1 => /andP [/andP [Hf Hf'] H1']. rewrite /Z_eq in H1'.
      move: (flows_antisymm _ _ Hf Hf') => Heq; subst. 
      by case: ( Z.eq_dec z z') H1' => // Heq _; subst.
    + rewrite /PC_spec in H2. 
      rewrite bindGen_def. exists (PAtm z' lpc').
      split. by apply gen_PC_correct.
      by  rewrite -Heqb'. 
Qed.
  
(* Vary Stack *)

Fixpoint stack_size st : nat  := 
  match st with 
    | Mty => 0 
    | _ ::: st => S (stack_size st)
  end.

Lemma forallb2_forall : 
  forall (A : Type) (f : A -> A -> bool) (l1 l2 : list A),
    forallb2 f l1 l2 = true <-> 
    (length l1 = length l2 /\ 
     forall x y : A, In (x, y) (seq.zip l1 l2) -> f x y = true).
Proof.
  move=> A f l1 l2. split.
  + elim: l1 l2 => [| x l1 IHxs]; case => //= y l2 /andP [H1 H2].
    move/(_ l2 H2) : IHxs => [-> HIn]. split => //. 
    move=> x' y' [[Heq1 Heq2] | HIn']; subst; by auto.
  + elim: l1 l2 => [| x l1 IHxs]; case => [|y l2] //=; try by move => [H _].
    move => [Hlen HIn]. apply/andP; split. by eauto.
    apply IHxs. split; by eauto.
Qed.

Lemma zip_combine: 
  forall {A} {B} (l1 : list A) (l2 : list B), 
    length l1 = length l2 ->
    seq.zip l1 l2 = combine l1 l2.
Proof.
  move => A B. elim => //= [| x xs IHxs]; case => //= y yx Hlen.
  rewrite IHxs //. by apply/eq_add_S. 
Qed.
 

Lemma in_zip: 
  forall {A} {B} (l1 : list A) (l2 : list B) x y, 
  (In (x, y) (seq.zip l1 l2) -> (In x l1 /\ In y l2)).
Proof.
  Opaque In. 
  move => A B. elim => [| x xs IHxs]; case => // y ys x' y' [[Heq1 Heq2] | HIn]. 
  + by subst; split; apply in_eq. 
  + move/IHxs: HIn => [HIn1 HIn2]. split; constructor(assumption).
Qed.


Lemma in_map_zip : 
  forall {A B C} (l1 : list A) (l2 : list B) x y (f : B -> C), 
     In (x, y) (seq.zip l1 l2) -> In (x, f y) (seq.zip l1 (map f l2)).
Proof.
  move=> A B C. 
  elim => [| x xs IHxs]; case => // y ys x' y' f [[Heq1 Heq2] | HIn]; subst.
  + by constructor.
  + move/IHxs : HIn => /(_ f) HIn. 
    by constructor(assumption). 
Qed.

Lemma in_zip_swap:
    forall {A B} (l1 : list A) (l2 : list B) x y, 
     In (x, y) (seq.zip l1 l2) <->  In (y, x) (seq.zip l2 l1).
Proof.
  move=> A B. 
  elim => [| x xs IHxs]; case => // y ys x' y'. 
  split; move=>  [[Heq1 Heq2] | HIn] ; subst; (try by constructor);
  by move/IHxs: HIn => HIn; constructor(assumption).
Qed.

Lemma gen_var_stack_sound_indist: 
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (gen_vary_stack obs inf st) (fun st' => 
                                   indist obs st st').
Proof.
  move=> st obs pc Hspec st'.
  rewrite /stack_spec in Hspec.
  move : Hspec => [Heq | [loc [Heq Hspec]]].
 (* Stack empty *)  
  - subst. by move => <-. 
 (* Stack Singleton *)   
  - subst. case: st'. 
    + rewrite /gen_vary_stack bindGen_def. move => [loc' [Hvary Hgen]].
      move: Hgen. rewrite bindGen_def. move=> [st' [_ Heq]]. discriminate.
    + rewrite /gen_vary_stack bindGen_def. move => loc' st' [loc'' [Hvary Hgen]].
      move: Hgen. rewrite bindGen_def /pure. move=> [st'' [Heq [Heq1 Heq2]]].
      rewrite returnGen_def in Heq. subst loc'' st'' st'. simpl.
      case: loc Hspec Hvary => [[[pc1 l] regs] regptr]. 
      case: loc' => [[[pc2 l'] regs'] regptr']. 
      rewrite /stack_loc_spec /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc.
      case: pc1 => v_pc1 l_pc1; case: pc2 => v_pc2 l_pc2.
      remember  (isLow l_pc1 obs) as b.   
      case: b Heqb => Heqb [HIn [Hspec [Hrng1 [Hrng2 Hgen]]]]; rewrite -Heqb.
      - rewrite bindGen_def. 
        move => [regs'' [/sequenceGen_equiv [Hlen HIn'] [eq1 eq2 eq3 eq4 eq5]]]; 
        subst. rewrite -Heqb. rewrite /indistStackHelper.
        repeat (apply/andP; split => //; try rewrite /indist /indistPtrAtm -Heqb); 
        try (by rewrite /Z_eq; case: (Z.eq_dec _ _)); try by apply flows_refl.  
        apply forallb2_forall. split. by rewrite Hlen map_length. 
        move => r1 r2 HIn''. 
        have /HIn' H : In (r2, gen_vary_atom obs inf r1)
                             (seq.zip regs' (map (gen_vary_atom obs inf) regs))
        by apply/in_map_zip/in_zip_swap. 
        simpl in H. apply in_zip in HIn''. 
        move: Hspec HIn''=> [Hlen' Hval] [/Hval HIn1 HIn2].  
        case: r1 H HIn1 HIn2; case: r2 => v1 l1 v2 l H [Hvalspec HIn1] HIn2.
        by  move/(gen_vary_atom_correct obs (v2 @ l) Hvalspec): H => [H _].
      - rewrite bindGen_def. move => [regs'' [/vectorOf_equiv [Hlen Hvec] H]].
        move: H. rewrite bindGen_def. move=> [regps'' [Hvary H]].
         move: H. rewrite bindGen_def. move=> [lab'' [Hgenlab H]].
         move: H. rewrite bindGen_def. move=> [regptr'' [Hgenreg [Heq1 Heq2 Heq3 Heq4]]].
         subst. rewrite /smart_vary /smart_vary_pc /gen_vary_pc in Hgen Hvary.
         rewrite -Heqb bindGen_def in Hvary. move: Hvary => [pc3 [H1 H2]].
         case: pc3 H1 H2=> v_pc3 l_pc3 H1 H2. rewrite /isHigh in H2. 
         remember (isLow l_pc3 obs) as b'.  
         case: b' Heqb' H2 =>  Heqb' /= [Heq1 Heq2]; subst. 
         - symmetry in Heqb. simpl in Heqb. 
           move: (not_flows_not_join_flows_right obs l_pc3 l_pc1 Heqb).
           rewrite /join /ZsetLat /isLow. move => -> . split => //.
         - rewrite -Heqb'. split => //. 
Qed.

Lemma gen_var_stack_sound_spec:
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (gen_vary_stack obs inf st) (fun st' => 
                                   stack_spec pc inf st' /\
                                   stack_size st = stack_size st').
Proof.
  Opaque choose. 
  move=> st obs pc Hspec st' Hvary.
  move : (gen_var_stack_sound_indist st obs pc Hspec st' Hvary) => Hindist.
  rewrite /stack_spec in Hspec.  
  move : Hspec => [Heq | [loc [Heq Hspec]]].
 (* Stack empty *)  
  - subst. move: Hvary. rewrite /gen_vary_stack /pure. 
    move => <-. split => //. by rewrite /stack_spec; left.
  - subst. move: Hvary. rewrite /gen_vary_stack /pure.  
    move=> [loc' [Hvary Hgen]]. move: Hgen.
    move => [st H]. rewrite !returnGen_def in H. move : H => [Heq1 Heq2]; subst.
    split => //. rewrite /stack_spec. right.
    exists loc'; split => //. rewrite /indist /indistStack in Hindist.
    case: loc Hspec Hvary Hindist => [[[pc1 l1] regs1] reg1]. 
    case: loc'=> [[[pc2 l2] regs2] reg2].
    rewrite /stack_loc_spec. case: pc1; case: pc2 => zpc1 lpc1 zpc2 lpc2.
    move => [HIn [[Hlen Hspec] [Hrng1 [Hrng2 H]]]].
    remember (isLow lpc2 obs) as b.  case: b Heqb => Heqb. 
    + simpl.  rewrite -Heqb. 
      move=> [regs [/sequenceGen_equiv [Hlen' HIn'] [eq1 eq2 eq3 eq4]]] Heq Hind; 
      subst. repeat split => //. by rewrite Hlen' map_length. 
      case => vr2 lr2 HIn2. 
      rewrite /indistStackHelper -Heqb in Hind.
      move/andP: Hind => [/andP [_ /forallb2_forall [Hlen'' Hind]] _].  
      move: (HIn2) =>  Hsplit. apply in_split in Hsplit.
      move : Hsplit => [lst1 [lst2 Heq]]. 
      case: regs1 Hlen Hspec Hlen' HIn' Hlen'' Hind => [| reg1f regs1'].
      - subst regs2. move=> Hlen Hspec Hlen' HIn' Hlen'' Hind. 
        rewrite app_length /= in Hlen''. omega. 
      - set regs1 := reg1f :: regs1'. 
        move=> Hlen Hspec Hlen' HIn' Hlen'' Hind. 
        set r1 := nth (length lst1) regs1 reg1f. case: r1 => vr1 lr1.
        have/in_zip_swap Hadm : In (vr1 @ lr1, vr2 @ lr2) (seq.zip regs1 regs2) by admit. 
        eapply in_map_zip with (f := (gen_vary_atom obs inf)) in Hadm.
        move/HIn' : Hadm => /= Hadm. 
        remember (Zset.incl lr1 obs) as b'. 
        have/Hspec HIn'' : In (vr1 @ lr1) regs1 by admit.
        case: b' Heqb' Hadm => Heqb'; 
        [ move => [Heq1 Heq2] | move => [vr2' [/gen_value_correct H2 [Heq1 Heq2]]]].  
        * by subst vr2 lr2.
        * subst vr2' lr2. split => //. by move: HIn'' => [_ HIn'']. 
     + rewrite /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc 
               bindGen_def -Heqb.  
       move => [regs3 [/vectorOf_equiv [Hlen' HIn']] 
                      [pc' [genpc' [lab [/gen_label_inf_correct Hlab [regptr' [/gen_from_nat_length_correct [Hrng Hrng'] [eq1 eq2 eq3 eq4]]]]]]]].
       subst pc' lab regs3 regptr'.  
       rewrite /smart_vary /smart_vary_pc /gen_vary_pc -Heqb in genpc'. 
       move: genpc' => [pc' [[pc_l [genl [pc_z [/gen_from_length_correct 
                                                 [Hrng3 Hrng4]  
                                                 Hret]]]]] Hgen] Hind. 
       remember (isLow lpc1 obs) as b'. case: b' Heqb' Hind => Heqb' Hind.
       rewrite /cropTop -Heqb' -Heqb in Hind. discriminate. 
       rewrite returnGen_def in Hret. subst. rewrite /isHigh in Hgen.
       remember (isLow pc_l obs) as b''. 
       case: b'' Heqb'' Hgen => /= heqb'' [eq1 eq2]; subst.
       repeat split => //.  
       by move => [val2 lab2] /HIn'/gen_atom_correct HInreg2. 
       rewrite /gen_label_between_lax_spec in H *. 
       move: H => [[H1 H2] | [H1 H2]].

(*              
       Search _ (_ <: _= true). 
       move : Hgen. rewrite bindGen_def. move 

congruence. discriminate. 

      Search (length (_ ++ _)).

      Set reg2 := nth
*)    
Abort.      
      (* rewrite /indist /indistReg in Hind. *)
      
      (* remember (isLow lpc1 obs) as b'.  case: b' Heqb' => Heqb'.  *)
      (* have /HIn' H : In ((vr2 @ lr2), gen_vary_atom obs inf regs1) *)
      (*                   (seq.zip regs2 (map (gen_vary_atom obs inf) regs1)) *)
      (*   by apply/in_map_zip/in_zip_swap.  *)

      (* move: Hspec => [Hlen' Hval]. [/Hval HIn1 HIn2].   *)
      (*   case: r1 H HIn1 HIn2; case: r2 => v1 l1 v2 l H [Hvalspec HIn1] HIn2. *)
      (*   by  move/(gen_vary_atom_correct obs (v2 @ l) Hvalspec): H => [H _]. *)

      
      
    
    
    
               
 (* Stack Singleton *)   

  

Lemma gen_var_stack_correct: 
  forall st obs pc,
    stack_spec pc inf st -> 
    (gen_vary_stack obs inf st) <--> (fun st' => 
                                        indist obs st st' /\
                                        stack_spec pc inf st' /\
                                        stack_size st = stack_size st').
Proof.
  move=> st obs pc Hspec st'.
  rewrite /stack_spec in Hspec.
  have Hadm: 
    forall {A} {B} (l1 : list A) (l2 : list B) x y, 
      length l1 = length l2 ->
      (In (x, y) (seq.zip l1 l2) <-> (In x l1 /\ In y l2)) by admit.
  move : Hspec => [Heq | [loc [Heq Hspec]]].
 (* Stack empty *) 
  + subst. rewrite /gen_vary_stack /pure returnGen_def. 
    split. 
    - move => Heq; subst. split => //. split => //.
      by rewrite /stack_spec; left.
    - rewrite /indist /indistStack /stack_spec /=. 
      case: st' => // loc' st'. move => [H1 [H2 H3]]. 
      discriminate. 
  (* Stack singleton *)
   + subst. split. 
     - rewrite /smart_vary /gen_vary_stack.
       rewrite !bindGen_def /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc.
       move=> [loc' [Hvary H]]. 
       rewrite bindGen_def in H.
       move : H => [st'' [Heq1 Heq2]].
       rewrite /pure !returnGen_def in Heq1, Heq2. subst. 
       case: loc Hspec Hvary => [[[pc' lab] regs] regptr] Hspec Hvary. 
       case: loc' Hvary => [[[pc'' lab'] regs'] regptr'] Hvary. 
       simpl. remember (isLow ∂(pc') obs) as b. 
       case: b Heqb Hvary => Heqb. rewrite bindGen_def;  
       move => [regs'' [/sequenceGen_equiv [Hlen HIn] [Heq1 Heq2 Heq3 Heq4]]]; subst;
       rewrite -Heqb. 
       * split; [| split => //].  
         - rewrite /indistStackHelper.  
           repeat (apply/andP; split => //); try by apply flows_refl. 
           rewrite /indist /indistPtrAtm. case: pc''{Heqb Hspec} => z l.
           rewrite /isHigh. case: (isLow l obs) => //=.
           apply/andP; split. by rewrite /label_eq flows_refl.
           rewrite /Z_eq. by case: (Z.eq_dec z z).
           rewrite /Z_eq. by case: (Z.eq_dec _ _). 
           rewrite /indist /indistReg.
           apply forallb2_forall. move : (Hlen) => Hlen'. 
           rewrite map_length in Hlen. 
           split => //. move => r1 r2.
           move=> H. move/(_ (r2, (gen_vary_atom obs inf r1))) : HIn => HIn.
           Opaque indist. simpl in HIn. 
           rewrite /smart_vary /= in Hlen'.
           move/(_ _ _ regs' (map (gen_vary_atom obs inf) regs) _ _ Hlen'): (Hadm) => Hadm'. 
           symmetry in Hlen.
           move/(_ _ _ regs regs' r1 r2 Hlen): (Hadm) => Hadm''. 
           move/Hadm'': H => [H1 H2]. 
           have /HIn HIn'' : In (r2, gen_vary_atom obs inf r1)
                     (seq.zip regs' (map (gen_vary_atom obs inf) regs)).
           apply Hadm'. split => //. by apply in_map.
           rewrite /gen_vary_atom /indist /indistAtom /isHigh /isLow in HIn'' *.
           case: r1 HIn'' {HIn Hadm'' H1 H2}; case: r2 => v1 l1 v2 l2 HIn.
           case: (l2 <: obs) HIn => //= [[Heq1 Heq2]|]; subst.
           apply/andP; split => //. rewrite /label_eq. apply/andP; split; by apply flows_refl.
           rewrite /indist /indistValue. case: v1.       
           move=> z. rewrite /Z_eq. by case: (Z.eq_dec z z).
           case. move => fp i. apply/andP; split. rewrite /mframe_eq.
           case: (Mem.EqDec_block fp fp)=> //. congruence.
           rewrite /Z_eq. by case: (Z.eq_dec i i).
           move=> z. rewrite /Z_eq. by case: (Z.eq_dec z z).
           move=> l. rewrite /label_eq. apply/andP; split; by apply flows_refl.
           rewrite bindGen_def. move =>  [v [_ [Heq1 Heq2]]]; subst.
           apply/andP; split => //. rewrite /label_eq. apply/andP; split; by apply flows_refl.
         - rewrite /stack_spec.  right. eexists. split. reflexivity. 
           rewrite /stack_loc_spec in Hspec *. 
           move : Hspec  => [HIn' [[H1 H2] [Hrng Hlet]]]. repeat split => //.
           by rewrite Hlen map_length.
Abort.
(*
           exact H2. assumption.  move => reg HIn''.
           
           assumption.
       * rewrite bindGen_def. move => [regs'' [/vectorOf_equiv [Hlen Hvec] H]].
         move: H. rewrite bindGen_def. move=> [ptr'' [Hgen H]].
         move: H. rewrite bindGen_def. move=> [lab'' [Hgenlab H]].
         move: H. rewrite bindGen_def. move=> [regptr'' [Hgenreg [Heq1 Heq2 Heq3 Heq4]]].
         subst. rewrite /smart_vary /smart_vary_pc /gen_vary_pc in Hgen. 
         case: pc' Hgen Hspec Heqb => z_pc' l_pc' Hgen Hspec Heqb.  
         rewrite -Heqb in Hgen. 
         move: Hgen. rewrite bindGen_def. move=> [pc' [Hgen H]].
         case: pc' Hgen H => z_pc l_pc Hgen H. rewrite /isHigh in H. 
         case: pc'' H => z_pc'' l_pc'' H. 
         remember (isLow l_pc obs) as b'.  
         case: b' Heqb' H =>  /= ; move => Heqb' [Heq1 Heq2]; subst. 
         - symmetry in Heqb. simpl in Heqb. 
           move: (not_flows_not_join_flows_right obs l_pc l_pc' Heqb).
           rewrite /join /ZsetLat /isLow. move => -> . split => //.
           split => //. rewrite /stack_spec. right. by eexists; split=> //. 
         - rewrite -Heqb'. split => //. split => //.
           rewrite /stack_spec. right. by eexists; split => //.
    + move => [Hindist [[//= | [loc' Hspec'] Hsize]].   
      case: st' Hindist Hsize => // loc'  st'.
      case: st'=> //.
      case: loc Hspec => [[[ptr lab] regs] regptr]. 
      case: loc'=> [[[ptr' lab'] regs'] regptr'] Hspec Hindist _.
      rewrite /indist  /indistStack /= in Hindist. 
      case: ptr Hspec Hindist => z pc_lab. case: ptr'=> z' //= pc_lab' Hspec Hindist.
      rewrite /isHigh. remember (isLow pc_lab obs) as b. remember (isLow pc_lab' obs) as b'.
      case: b Heqb  Hindist =>//= Heqb; case: b' Heqb' => Heqb' Hindist.  
      - (*both pcs are low *) 
        move: Hindist => /andP [Hindist _]. move: Hindist => /andP [Hindist H1]. 
        move: Hindist => /andP [Hindist H2]. move: Hindist => /andP [Hindist H3].
        rewrite bindGen_def. eexists. rewrite bindGen_def.  
        split. Focus 2.  
        * rewrite bindGen_def. by exists Mty; split => //.
        * eexists.
          rewrite /indist /indistPtrAtm -Heqb -Heqb' /= in H3.
          move /andP: H3 => [H3 H4]. 
          rewrite /Z_eq in H4 H2. case: (Z.eq_dec z z') H4 => // H4 _.
          case: (Z.eq_dec regptr regptr') H2 => // H2 _.
          rewrite /label_eq in Hindist H3. 
          move: Hindist H3 => /andP [H5 H5'] /andP [H3 H3'].
          have Heq1: lab = lab' by apply flows_antisymm.
          have Heq2: pc_lab' = pc_lab by apply flows_antisymm. subst.
          split; [| reflexivity]. clear H3 H3' H5 H5'. 
          apply/sequenceGen_equiv. rewrite /indist /indistReg in H1. 
          move/forallb2_forall : H1 => [Hlen H1]. 
          split. by rewrite map_length.
          move => [r1 gen] //= HIn. 
          move/Hadm : HIn. rewrite map_length.
          symmetry in Hlen. move/(_ Hlen) => [HIn1 /in_map_iff [r2 [Heq HIn2]]].
          subst gen. 
          have/H1 Hindist: In (r2, r1) (seq.zip regs regs') by apply Hadm.
          rewrite /indist /indistAtom /gen_vary_atom in Hindist *. 
          case: r1 HIn1 Hindist => v1 l1. case: r2 HIn2=> v2 l2 HIn2 HIn1.
          move=> /andP [Heq /orP [/Bool.negb_true_iff Hhigh | Hind]]. 
          rewrite /isLow in Hhigh. rewrite Hhigh bindGen_def. exists v1.
          split. apply /gen_value_correct. rewrite /val_spec. move/(_ (v2 @ ) ())

Search _ (~~ _  = true). rewrite /isHight in Hhigh.
         
          
eassumption. move=> [r1 Predr] HIn. simpl.
      move/Hadm : HIn. rewrite map_length. symmetry in Hlen.
      move/(_ Hlen)=> [HIn1 /in_map_iff [r2 [Hgen HIn2]]].
      subst Predr. 
      have /H1 Hindist' : In (r2, r1) (seq.zip regs regs').
      by apply Hadm => //.
      rewrite /indist /indistAtom in Hindist'.
      case: r1 HIn1 Hindist'=> v1 l1 HIn1. case: r2 HIn2 => v2 l2 HIn2.
      move/andP => [Heq /orP [/Bool.negb_true_iff Hhigh | Hinidst''']].
      rewrite /gen_vary_atom. rewrite /isLow in Hhigh. rewrite Hhigh. 
      rewrite bindGen_def. 
      rewrite /isHigh /= in Hhigh. 
      move: Hspec => [_ [Hreg _]].
      rewrite /regs_spec in Hreg. move: Hreg => [_ /(_ (v2@l2) HIn2) [Hval _]].
      exists v1. split. apply gen_value_correct. rewrite /val_spec.
      rewrite /indist /indistPtrAtm in H3. 
*)    




Axiom frame_spec' : Info -> frame -> Prop.    

Lemma gen_var_frame_correct:
  forall (obs: Label) (inf: Info) (fr : frame),
    (frame_spec' inf fr) -> 
    (gen_var_frame obs inf fr) <--> (fun fr' => 
                                        indist obs fr fr' /\ frame_spec' inf fr').
Proof. admit. Qed.

Axiom mem_spec : Info -> memory -> Prop.    

Lemma gen_vary_memory_correct:
  forall (obs: Label) (inf: Info) (m : memory),
    (mem_spec inf m) -> 
    (gen_vary_memory obs inf m) <--> (fun m' => 
                                        indist obs m m' /\ mem_spec inf m').
Proof. admit. Qed.





(* Main theorem *)

Lemma combine_l : forall {A} (l : list A) x y, 
                    In (x, y) (combine l l) -> x = y.
Proof. admit. Qed.

Lemma incl_empty : forall s, Zset.incl Zset.empty s.
Proof.
  move=> s. apply Zset.incl_spec. by rewrite Zset.elements_empty. 
Qed.

Lemma incl_same : forall s, Zset.incl s s.
Proof.
  move => s.
  by apply/Zset.incl_spec/incl_refl. 
Qed.

Require Import ZArith.

Lemma forallb_indist : 
  forall (l : list frame),
    forallb
      (fun x : frame * frame =>
         let (f1, f2) := x in indist Zset.empty f1 f2)
      (combine l l).
Proof.
  move => l. apply forallb_forall. case => x y H.
  apply combine_l in H. subst. case: y => s lab l0. 
  rewrite /indist /indistFrame /isLow.
  case: (s <: Zset.empty) =>  //=.  
  rewrite /label_eq flows_refl /=.
  case: (Zset.incl lab Zset.empty) =>  //=. 
  elim : l0 => // x l0 IHl0. simpl.
  apply/andP. split => //=.
Abort.
(*
  case: x => valx labx. rewrite incl_same //=. 
  rewrite /isHigh /isLow .  
  case: (labx <: Zset.empty)=> //= .
  case: valx => //=. 
  try (by rewrite /Z_eq; move => n ; case (Z.eq_dec n n)).
  case. move => fp i. apply/andP. split => //. 
  rewrite /mframe_eq. 
  case: (Mem.EqDec_block fp fp) => //=. 
  congruence. by rewrite /Z_eq; case: (Z.eq_dec i i).
  (by rewrite /Z_eq; move => n ; case (Z.eq_dec n n)).
  move => L; apply/andP; split; apply incl_same.
Qed.
*)

Lemma gen_variation_state_correct :
  gen_variation_state <--> (fun b =>
                              let '(Var L s1 s2) := b in
                              indist L s1 s2 = true).
Proof.
  (* The statement is not complete as we need the states to satisfy 
     some validity requirements *)
Abort.
  (* case => Lab s1 s2. split. rewrite /gen_variation_state.  *)
  (* rewrite bindGen_def.  *)
  (* move => [l1 [Htop H]].  *)
  (* rewrite bindGen_def in H.  *)
  (* move: H => [[mem mframes] [Hinit H]].  *)
  (* case: mframes Hinit H => [ | mframe1 mframes] Hinit H. *)
  (* - rewrite returnGen_def /= in H.  *)
  (*   move : H => [Heq1 Heq2 Heq3]. subst.  *)
  (*   rewrite /indist /indistState /failed_state !trace_axiom //=. *)
  (*   rewrite /label_eq /isHigh /isLow /flows. simpl.  *)
  (*   have Ht: Zset.incl Zset.empty Zset.empty = true by *)
  (*       apply/Zset.incl_spec; rewrite Zset.elements_empty.  *)
  (*   rewrite Ht -beq_nat_refl /indistMemHelper.  *)
  (*   simpl. by rewrite forallb_indist. *)
  (* - case : mframe1 Hinit H => mf1 Z1 Hinit H1. *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ptr_a [sgen H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [regset [sgen2 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [st [sgen3 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [memg [sgen4 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [instr [sgen5 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [lab [sgen6 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ST' [sgen7 H1]].      *)
  (*   rewrite returnGen_def in H1. *)
  (*   move : H1 => [Heq1 Heq2 Heq3]; subst. *)
  (*   rewrite /smart_gen in sgen, sgen2, sgen3, sgen4, sgen5, sgen6, sgen7 . *)


End WithDataLenNonEmpty.
