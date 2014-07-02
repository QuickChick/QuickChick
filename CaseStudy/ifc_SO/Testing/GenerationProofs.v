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

Lemma gen_PC_correct: 
  forall inf, 
    (gen_PC inf) <--> (fun pc => let '(PAtm z l) := pc in
                                 (In l (allThingsBelow (top_prin inf))) /\ 
                                 (0 <= z <= (code_len inf) - 1)%Z).
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
      
        
Lemma gen_atom_correct:
  forall inf,
    (gen_atom inf) <--> (fun atm =>
                           let '(Atm val lab) := atm in
                           val_spec inf val /\ 
                           In lab (allThingsBelow (top_prin inf))).
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


Lemma smart_gen_stack_loc_correct :
  forall f g l1 l2 inf, 
    (f l1 l2) <--> (g l1 l2) ->
    (smart_gen_stack_loc f l1 l2 inf) <--> 
    (fun t =>
       let '(ptr_a, lab, regs, ptr_r) := t in
       In lab (allThingsBelow (top_prin inf)) /\
       regs_spec inf regs /\
       (0 <= ptr_r <= (Z.of_nat (no_regs inf) - 1))%Z /\
       let 'PAtm addr lab' := ptr_a in
       (0 <= addr <= ((code_len inf) - 1))%Z /\
       g l1 l2 lab').
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


Lemma allThingsBelow_isLow : 
  forall l l', 
    In l (allThingsBelow l') -> l <: l'.
Proof.
  move=> l l' /in_map_iff H. rewrite /allThingsBelow /allBelow  in H.  
  apply Zset.incl_spec.  
  move=> a HIn. subst.  
  remember (Zset.elements l) as lst.
  remember (Zset.elements l') as lst'. 
  move : H => [x [Heq HIn']]. 
  
  
Lemma elements__label_of_list: 
  forall lst, Zset.elements (fold_left (fun a b => Zset.add b a) lst Zset.empty) = lst.
Proof.
  elim => [| x xs IHxs]. 
  + by rewrite /label_of_list /= Zset.elements_empty. 
  + rewrite /label_of_list //= in IHxs *. Search _ (Zset.elements _). a`rewrite IHxs.
Lemma elements_of_list:
  forall (l : Label) lst, In l (map label_of_list lst) <-> In (Zset.elements l) lst.
Proof.
  move => l lst. split.
  move/in_map_iff => [zs [Heq HIn]]. 
  have: 
H. 
apply in_map in H.
  
  have H: In l 

  remember (l <: l'). case: b Heqb => // Heqb.
  symmetry in Heqb. apply In_split in H.
  move : H => [l1 [l2 Heq]]. 
  rewrite /flows /ZsetLat in Heqb. Search _ (map _ _). 
  
  rewrite /label_of_list in H.
  
  move : (Heqb) => joinl. move : (Heqb) => joinr.
  
  eapply not_flows_not_join_flows_left in joinl.
  eapply not_flows_not_join_flows_right in joinr.
  rewrite /flows /join /ZsetLat in joinl joinr.
  Search _ (incl _ _).
  apply in_map_iff in H.
  
  apply Zset.incl_spec.  
  remember (Zset.elements l') as lst. 
  case: lst  l l' Heqlst H => //= [| x xs]  l l' Heqlst H .
  + case: H => [H | H] //=; subst. by rewrite Zset.elements_empty.
  + rewrite map_app /= in H. 
    apply in_app_or in H. 
    remember (Zset.elements l) as lst'.
    elim : lst' Heqlst' => //= [|y ys IHys] Heqlst'. 
    by apply/incl_tl.
    
    
    Search _ (incl _ _).

    move: H => [/in_map_iff H | /in_map_iff H]. 
    
      in H. Search _ map.
    Search _ (In _ _). _ (map _ _) (cons _).
    Search _ (incl _ _). 
    apply incl_tl. eapply IHxs.
  move : H => /in_map_iff H.
  Search _ (In _ (map _ _)).
  remember (powerset (Zset.elements l')) as lst.
  case: lst Heqlst H => [| x xs] Heqlst H.
  by move: (powerset_nonempty (Zset.elements l')); contradiction.
  simpl in H. move : H => [H | H].
  elim : x Heqlst H => //= [|z zs] Heqlst H. 
  simpl in H. Search _ Zset.empty.
  
  apply IHxs.
  Search _ (In (map _).

Lemma gen_label_between_lax_correct :
  forall l1 l2,
    (gen_label_between_lax l1 l2) <--> (fun l => l1 <: l /\ l <: l2).
Proof.
  move=> l1 l2 l. rewrite /gen_label_between_lax. split.
  + move /elements_equiv => [/filter_In [HIn Ht] | [Hempty Heq]]; subst.
   rewrite /allThingsBelow /allBelow in HIn.
   rewrite /isLow in Ht. rewrite Ht. 
   compute in HIn. Search _ (label_of_list _).
    Search _ allThingsBelow.
       
(* Main theorem *)
Require Import Indist.

Axiom trace_axiom: forall {A} x (y : A), Property.trace x y = y.
Lemma MemEqDec : forall fp, Mem.EqDec_block fp fp.
Proof. admit. Qed.


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
  admit. (*Arrrrg *)
  by rewrite /Z_eq; case: (Z.eq_dec i i).
  (by rewrite /Z_eq; move => n ; case (Z.eq_dec n n)).
  move => L; apply/andP; split; apply incl_same.
Qed.

Lemma gen_variation_state_correct :
  gen_variation_state <--> (fun b =>
                              let '(Var L s1 s2) := b in
                              indist L s1 s2 = true).
Proof. 
  case => Lab s1 s2. split. rewrite /gen_variation_state. 
  rewrite bindGen_def. 
  move => [l1 [Htop H]]. 
  rewrite bindGen_def in H. 
  move: H => [[mem mframes] [Hinit H]]. 
  case: mframes Hinit H => [ | mframe1 mframes] Hinit H.
  - rewrite returnGen_def /= in H. 
    move : H => [Heq1 Heq2 Heq3]. subst. 
    rewrite /indist /indistState /failed_state !trace_axiom //=.
    rewrite /label_eq /isHigh /isLow /flows. simpl. 
    have Ht: Zset.incl Zset.empty Zset.empty = true by
        apply/Zset.incl_spec; rewrite Zset.elements_empty. 
    rewrite Ht -beq_nat_refl /indistMemHelper. 
    simpl. by rewrite forallb_indist.
  - case : mframe1 Hinit H => mf1 Z1 Hinit H1.
    rewrite bindGen_def in H1.
    move:  H1 => [ptr_a [sgen H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [regset [sgen2 H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [st [sgen3 H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [memg [sgen4 H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [instr [sgen5 H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [lab [sgen6 H1]]. 
    rewrite bindGen_def in H1.
    move:  H1 => [ST' [sgen7 H1]].     
    rewrite returnGen_def in H1.
    move : H1 => [Heq1 Heq2 Heq3]; subst.
    rewrite /smart_gen in sgen, sgen2, sgen3, sgen4, sgen5, sgen6, sgen7 .
    
    simpl in sgen3.
 
rewrite /label
  
  
Print "_ <: _".
  Search _ (Property.trace _ _). compute .

  rewrite /gen_init_mem bindGen_def in Hinit.
  
  
  


  exists Lab. exists Lab. simpl .

  Search _  (Variation).
Lemma gen_ptr_correct : forall inf,
  peq (gen_Pointer inf) (fun ptr => 
