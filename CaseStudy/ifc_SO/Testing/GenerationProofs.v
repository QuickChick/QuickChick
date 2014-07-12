Require Import QuickChick SetOfOutcomes.

Require Import Common Machine Generation. 

Require Import List.
Require Import ZArith.

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


Lemma powerset_nonempty : 
  forall {A} (l : list A), powerset l <> nil.
Proof.
  move => A. elim => //= x xs IHxs.
  case: (powerset xs) IHxs => //=. 
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

Lemma gen_label_inf_correct : forall inf,
  peq (gen_label_inf inf) (fun e => In e (allThingsBelow (top_prin inf))).
Proof.
  move => inf. apply/gen_label_correct.
Qed.
 

Definition PC_spec (inf : Info) (pc : Ptr_atom) :=
  let '(PAtm z l) := pc in
  (In l (allThingsBelow (top_prin inf))) /\ 
  (0 <= z <= (code_len inf) - 1)%Z.

Lemma gen_PC_correct: 
  forall inf, 
    (gen_PC inf) <--> (PC_spec inf).
Proof.
  move=> inf ptr. rewrite /gen_PC.
  split.
  + rewrite bindGen_def. move => [lab [/gen_label_inf_correct gen_lab H]].
    rewrite bindGen_def in H. move : H => [z [/gen_from_length_correct H1 Hret]].
    rewrite returnGen_def in Hret. subst. by split.
  + case : ptr => z l. move => [Hin Hrng]. 
    rewrite bindGen_def. exists l; split.
    by apply /gen_label_inf_correct.
    rewrite bindGen_def. exists z; split => //.
    by apply /gen_from_length_correct.
Qed.


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

(* Move it at arbitrary.v ? *)
Lemma arbInt_correct : 
  arbitrary <--> (fun (z : Z) => True).
Proof.
  rewrite /arbitrary /arbInt /arbitraryZ.  
  rewrite sized_def. move => z. split => //= _. 
  exists (Z.abs_nat z).
  split. 
  + apply/Z.compare_le_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
  + apply/Z.compare_ge_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
Qed.

(* I don't know if this is reasonable, but otherwise some generators are 
  broken (suck as gen_Pointer) *)

Axiom data_len_nonempty : forall (inf : Info), data_len inf <> [].

Lemma gen_Pointer_correct: 
  forall inf, 
    (gen_Pointer inf) <--> (fun ptr => 
                              let '(Ptr mf addr) := ptr in
                              (exists len, In (mf, len) (data_len inf) /\ 
                                           (0 <= addr <= len - 1)%Z)). 
Proof.
  move => inf ptr. 
  move: (data_len_nonempty inf) => non_empty. 
  case: inf non_empty => def clen dlen top regs non_empty. rewrite /gen_Pointer.
  split.
  * rewrite bindGen_def. move => [[mf z] [/elements_equiv Helem  H]].
    rewrite bindGen_def in H. move : H => [a [/gen_from_length_correct H Hret]].
    rewrite returnGen_def in Hret; subst.
    simpl. case : Helem => [HIn | [Heq1 [Heq2 Heq3]]]; subst.
    by exists z. omega.
  * case: ptr => mf z. 
    case: dlen {non_empty} =>  [| x xs].
    - rewrite bindGen_def. 
      move=> [len  [//= HIn Hrng]].
    -  Opaque bindGen choose Z.compare returnGen. 
       move=> [len  [//= HIn [Hrng1 Hrng2]]].
       rewrite bindGen_def.  
       exists (mf, len). split.
       apply/elements_equiv. by left. 
       rewrite bindGen_def. 
       exists z. split => //. split. by apply/Z.compare_le_iff.
       by apply/Z.compare_ge_iff.
Qed.

Lemma gen_value_correct: 
  forall inf,
    (gen_Value inf) <--> (val_spec inf).
Proof.
  rewrite /gen_Value /val_spec.
  case=> def clen dlen top regs. case.
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
      * case:H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
        subst; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]); 
        try discriminate.      
        move/gen_Pointer_correct: H2 H2' => H2 [H2']; subst.
        move : H2 => //= [len [ HIn Hrng]].  
      * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
    - move => [len [HIn [Hrng1 Hrg2]]].
      apply/frequency_equiv. left. exists 1. eexists. 
      split. apply in_cons.  apply in_cons. constructor. 
      reflexivity.
      rewrite liftGen_def. split => //. eexists.
      split => //. apply gen_Pointer_correct. by exists len.
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
       by apply/Z.compare_ge_iff.
   + (* Vlab *)
     move => L. split.
     - move/frequency_equiv => [[n [g [H1 [H2 H3]]]] | [H1 H2]].
       * case: H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
         subst; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]); 
         try discriminate.
         by move : H2 H2' => /gen_label_inf_correct H1 [H2']; subst.
       * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
     - move => H. apply/frequency_equiv. left. exists 1. eexists.
       split. apply in_cons. apply in_cons. apply in_cons. constructor. 
       reflexivity.
       rewrite liftGen_def. split => //. exists L. split => //=.
       by apply/gen_label_inf_correct.
Qed.
      
Definition atom_spec inf atm  := 
  let '(Atm val lab) := atm in
  val_spec inf val /\ 
  In lab (allThingsBelow (top_prin inf)).
       
Lemma gen_atom_correct:
  forall inf,
    (gen_atom inf) <--> (atom_spec inf).
Proof.
  move => inf atm. rewrite /gen_atom /liftGen2 bindGen_def. case: atm => val lab. 
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
  
Definition regs_spec inf regs :=
  (length regs = no_regs inf) /\
  (forall reg, 
     In reg regs ->
     let '(Atm val lab) := reg in
     val_spec inf val /\ 
     In lab (allThingsBelow (top_prin inf))).
Lemma gen_registers_correct:
  forall inf,
    (gen_registers inf) <--> (regs_spec inf).
Proof.    
  move => inf regs. 
  rewrite /gen_registers. split.
  + move /vectorOf_equiv => [H1 H2].
    split => //. move => reg HIn. by apply/gen_atom_correct; apply H2. 
  + move => [Hlen Hregs]. apply/vectorOf_equiv. split => // x HIn.
    apply/gen_atom_correct. by apply Hregs.
Qed.

Definition stack_loc_spec (inf : Info) g (l1 l2: Label) t : Prop:=
  let '(ptr_a, lab, regs, ptr_r) := t in
  In lab (allThingsBelow (top_prin inf)) /\
  regs_spec inf regs /\
  (0 <= ptr_r <= (Z.of_nat (no_regs inf) - 1))%Z /\
  let 'PAtm addr lab' := ptr_a in
  (0 <= addr <= ((code_len inf) - 1))%Z /\
  g l1 l2 lab'.

Lemma gen_stack_loc_correct :
  forall f g l1 l2 inf, 
    (f l1 l2) <--> (g l1 l2) ->
    (smart_gen_stack_loc f l1 l2 inf) <--> (stack_loc_spec inf g l1 l2).
Proof.
  move=> f g l1 l2.
  case=> def clen dlen top noregs Hequiv. 
  rewrite /smart_gen_stack_loc /smart_gen /bindGen /returnGen /PredMonad /bindP /returnP //=.
  move => [[[ptr_a lab] regs] ptr_r]. split.
  + move =>  
    [regs' [/gen_registers_correct Hregs [ptr_a' [[lab' [/gen_label_inf_correct Hlab H']]
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
   
Lemma elements__label_of_list:
  forall (lst : list Z) x zt,
    List.In x (Zset.elements (fold_left (fun (a : Zset.t) (b : Z) => Zset.add b a) lst zt)) <->
    List.In x (lst ++ (Zset.elements zt)).
Proof.
  move => lst. 
  elim : lst => //=  x xs IHxs x' init.
  split. 
  + move => H. move/IHxs: H => H. apply in_app_or in H.
    move : H => [H | H]. 
    * by right; apply in_or_app; left.
    * move/Zset.In_add : H => [Heq | HIn]. 
      - by left.
      - right. apply in_or_app. by right.
  + move=> [Heq | H]; apply IHxs; subst. 
    * apply in_or_app. right. 
      by apply/Zset.In_add; left.
    * apply in_app_or in H. move : H => [Heq | HIn].
      - by apply in_or_app; left.
      - apply in_or_app; right. by apply/Zset.In_add; right.
Qed.

Lemma label_of_list__elements:
  forall l,
    label_of_list (Zset.elements l)  = l .
Proof. 
  move => l. apply flows_antisymm. 
  apply Zset.incl_spec. move => a HIn.
  move/elements__label_of_list : HIn => HIn. apply in_app_or in HIn.
  rewrite Zset.elements_empty in HIn.
  by case : HIn. 
  apply Zset.incl_spec. move => a HIn.
  apply/elements__label_of_list/in_or_app. 
  by left.
Qed.

Lemma powerset_in: 
  forall {A} (a : A) (l l' : list A),
    In a l -> In l (powerset l') -> In a l'.
Proof.
  move=> A a l l'. elim : l' l a => //= [|x xs IHxs] l a   HIn HIn'; subst.
  + by case: HIn' => H; subst. 
  +  apply in_app_or in HIn'. move : HIn' => [/in_map_iff [x' [Heq HIn']] | HIn']; subst.
     - case: HIn => [Heq | HIn]; subst.
       * by left.
       * right. eapply IHxs; eauto.  
     - by right; eapply IHxs; eauto.
Qed.

Lemma in_nil_powerset :
  forall {A} (l : list A), In [] (powerset l).
Proof.
  move=> A l. elim l => //= [| x xs IHxs]. by left.
  by apply in_or_app; right. 
Qed.


Lemma allThingsBelow_isLow : 
  forall l l', 
    In l (allThingsBelow l') -> l <: l'.
Proof. 
  move => l l'. (* split *)  
  + move=> /in_map_iff [x [Heq HIn]]. subst. 
    apply/Zset.incl_spec. move => a /elements__label_of_list H. 
    rewrite Zset.elements_empty app_nil_r in H. 
      by eapply powerset_in; eauto.
Qed.

Lemma allThingsBelow_isLow' : 
  forall l l', 
    l <: l' -> In l (allThingsBelow l').
Proof. 
  move => l l'. move=> Hf. 
  rewrite /allThingsBelow /allBelow.
  rewrite -[X in In X _]label_of_list__elements. apply in_map.
  admit.
Qed.

Lemma filter_nil: 
  forall {A} (f : A -> bool) l,
    filter f l = [] <-> 
    l = [] \/ forall x, In x l -> f x = false.
Proof.
  move=> A f l. split. 
  - elim: l => //= [_ | x xs  IHxs H].
    * by left.
    * right. move=> x' [Heq | HIn]; subst.
        by case: (f x') H.
        case: (f x) H => //= Hf.
        move : (IHxs Hf) => [Heq | HIn']; subst => //=; auto. 
  - move => [Heq | H]; subst => //=.
    elim : l H => // x xs IHxs H.
    simpl. rewrite (H x (in_eq x xs)). 
    apply IHxs. move=> x' HIn. apply H.
    by apply in_cons.
Qed.

Lemma powerset_in_refl: 
forall {a} (l : list a), In l (powerset l).
Proof.
  move=> a. elim => //= [| x xs IHxs].
  by left.
  by apply in_or_app; left; apply in_map.
Qed.
  
Lemma allThingsBelow_nonempty: forall l2, allThingsBelow l2 <> [].
Proof.
  rewrite /allThingsBelow /allBelow. 
  by move =>  l1 /map_eq_nil/powerset_nonempty c.
Qed.


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
    rewrite /allThingsBelow /allBelow. Search _ (map _ _) In.
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


Definition stack_spec (pc: Ptr_atom) inf (s: Stack) : Prop :=
  s = Mty \/ 
  exists loc, s = loc ::: Mty /\ 
              stack_loc_spec inf gen_label_between_lax_spec bot ∂pc loc.

Lemma gen_stack_correct: 
  forall inf (pc: Ptr_atom),
    (smart_gen_stack pc inf) <--> (stack_spec pc inf). 
Proof.
  Opaque smart_gen_stack_loc.
  rewrite /smart_gen_stack /stack_spec. move => inf pc st.
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
    
   
Require Import EquivDec.

Lemma equiv_dec_refl: forall mf : mframe, equiv_dec mf mf.
Proof.
  move=> mf.  rewrite /equiv_dec. 
  case Mem.EqDec_block.
  by move => e. 
  move => c. simpl. congruence.
Qed.
  
Definition frame_spec (inf : Info) mem mf
           (mem' : memory) := 
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
  forall inf mem mf,
    (populate_frame inf mem mf) <-->
    (frame_spec inf mem mf).
Proof. 
  move=> inf mem mf mem'.  rewrite /populate_frame /frame_spec.
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
    | H : (_, pure ?a) = (?n, ?g),
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

Ltac try_solve :=
      match goal with 
        | |- ~ _ => move => contra; subst
        | HIn: In _ [] |- _ => by []
        | Hnonempty : ~ (onNonEmpty [] _ = 0) |- _ =>
           by rewrite /onNonEmpty in Hnonempty
        | Hnonempty : ~ (_ * (onNonEmpty [] _))%coq_nat = 0 |- _ => 
            by rewrite [X in (_ * X)%coq_nat]/onNonEmpty -mult_n_O in Hnonempty
        | |- _ /\ _ => split => //=
        | Hand : _ /\ _ |- _ => destruct Hand
        | Hor : _ \/ _ |- _ => destruct Hor
        | |- (_ <= _)%Z => by apply/Z.compare_ge_iff
        | |- (_ <= _)%Z => by apply Z.compare_le_iff
        | Helem : elements _ _ _ |- _ => 
          move/elements_equiv : Helem => [Helem //= | [Helem1 Helem2] //=]; subst
        | Hchoose : choose _ _ |- _ =>
          rewrite choose_def /= in Hchoose
        | Hif: ~ ((if ?b then _ else _ ) = _) |- ?b = true =>
          by case: b Hif
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
      split; [repeat ((try by apply in_eq); apply in_cons) | split => //=]
  end.

Ltac trysolve2 := 
  match goal with 
    | Hand : _ /\ _ |- _ => destruct Hand; by trysolve2
    | |- _ = _ => reflexivity
    | |- _ /\ _ => split; [| by trysolve2]; by trysolve2
    | |- liftGen4 _ _ _ _ _ _ => rewrite liftGen4_def; by trysolve2
    | |- liftGen3 _ _ _ _ _ => rewrite liftGen3_def; by trysolve2
    | |- liftGen2 _ _ _ _ => rewrite liftGen2_def; by trysolve2
    | |- liftGen _ _ _ => rewrite liftGen_def; by trysolve2
    | |- elements _ _ _ => apply/elements_equiv; left; by trysolve2
    | |- choose _ _ => rewrite choose_def => /=; by trysolve2
    | |- ~ (_ ?= _)%Z = Lt => by apply/Z.compare_ge_iff
    | |- ~ (_ ?= _)%Z = Gt  => by apply/Z.compare_le_iff
    | |- ~ onNonEmpty ?l _ = 0 => by destruct l
    | |- exists _, _ => eexists; by trysolve2
    | |- ~ (( _ * onNonEmpty ?c _)%coq_nat * onNonEmpty ?l _)%coq_nat = 0 =>
        by destruct c; destruct l
    | |- gen_BinOpT _ => by apply gen_BinOpT_correct
    | |- ~ (if ?b then _ else _) = 0 => by destruct b
    | _ => by []
  end. 

(* Lemma gen_ainstrSSNI_correct : *)
(*   forall (st : State), (ainstrSSNI st) <--> (Instruction_spec st).      *)
(* Proof. *)
(*   move=> st instr. rewrite /ainstrSSNI /Instruction_spec. *)
(*   case: st => im m pr stk regs pc. *)
(*   set st := {| *)
(*              st_imem := im; *)
(*              st_mem := m; *)
(*              st_pr := pr;  *)
(*              st_stack := stk; *)
(*              st_regs := regs; *)
(*              st_pc := pc |}. *)
(*   case: (groupRegisters st regs [] [] [] [] Z0)=> [[[dptr cptr] num] lab]. *)
(*   split.  *)
(*   - case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 | *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 | *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; *)
(*     move /frequency_equiv =>  [[n [g [HIn [Hg Hn]]]] | [[H | H] H' //=]]; *)
(*     (repeat discr_or_first); *)
(*     try by (case: HIn => [[Heq1 Heq2] | HIn]; subst;   *)
(*     try unfold_gen; [by repeat try_solve |  by repeat discr_or_first]). *)
(*   - Opaque mult. *)
(*     case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 |  *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 |  *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; simpl;  *)
(*                    move => H; apply frequency_equiv; left;          *)
(*     instantiate_exists; try by trysolve2.   *)
(*     rewrite liftGen2_def. eexists. split; [| trysolve2].  *)
(*     exists (Z.abs_nat z). rewrite choose_def Zabs2Nat.id_abs. split => /=;  *)
(*     [apply/Z.compare_le_iff | apply/Z.compare_ge_iff]; destruct z => //=; apply Z.le_refl.  *)
(* Qed. *)

(* Proofs for variations *) 
Require Import Indist.

Lemma gen_vary_atom_correct :
  forall (l : Label) (inf : Info) (a : Atom),
    let 'v @ la := a in 
    val_spec inf v -> 
    (gen_vary_atom l inf a) <--> (fun a' => 
                                    let 'v' @ la' := a' in 
                                    indist l a a' /\ val_spec inf v').
Proof.  
  move=> l inf a. case: a => va la.
  move=> Hspec; case => va' la'.
  rewrite /gen_vary_atom /indist /indistAtom /isHigh /isLow.  
  case: (la <: l). 
  + (* la lower that observability state *) 
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
  

Lemma gen_vary_pc_correct: 
  forall (obs: Label) (inf: Info) (pc : Ptr_atom),
    (PC_spec inf pc) ->
    (gen_vary_pc obs inf pc) <--> (fun pc' =>
                                       indist obs pc pc' /\ PC_spec inf pc').
Proof.
  move => obs inf pc Hspec pc'.
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

Axiom trace_axiom: forall {A} x (y : A), Property.trace x y = y.

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
    