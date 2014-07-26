Require Import QuickChick.
Require Import Common.

Require Import Machine.

Require Import List.
Require Import ZArith.

(* ------------------------------------------------------ *)
(* ---------------- Constants --------------------------- *)
(* ------------------------------------------------------ *)

Module C.

(* Currently constant frames/sizes - no need for more *)
(* But we *could* generate arbitrary stuff now ! :D  *)
Definition min_no_frames := 2.
Definition max_no_frames := 2. 
Definition min_frame_size := 2%Z.
Definition max_frame_size := 2%Z.

(* Could also vary this - but no need *)
Definition code_len := 2.

Definition min_no_prins := 2.
Definition max_no_prins := 4.

Definition no_registers := 10.
End C.


Section CustomGens.
  Context {Gen : Type -> Type}
          {H: GenMonad Gen}.
  
(* Helpers to generate a Z within range (0, x) *)
Definition gen_from_length (len : Z) :=
  choose (0, len - 1)%Z.

Definition gen_from_nat_length (len : nat) :=
  choose (0, Z.of_nat len - 1)%Z.

(* ------------------------------------------------------ *)
(* ----- Generation of primitives ----------------------- *)
(* ------------------------------------------------------ *)

Record Info := MkInfo 
  { def_block : mframe            (* Default Block (sad)               *)
  ; code_len  : Z                 (* Length of instruction list        *)
  ; data_len  : list (mframe * Z) (* Existing frames and their lengths *)
  ; top_prin  : Label             (* Top label                         *)
  ; no_regs   : nat               (* Number of Registers               *)
  }.

Class SmartGen (A : Type) := {
  smart_gen : Info -> Gen A
}.

Definition gen_BinOpT := oneof (pure BAdd) [pure BAdd; pure BMult].

(* Labels *)

Definition gen_label (prins : Label) : Gen Label :=
  elements bot (allThingsBelow prins).

Definition gen_label_between_lax (l1 l2 : Label) : Gen Label :=
  elements l2 (filter (fun l => isLow l1 l) (allThingsBelow l2)).

Definition gen_label_between_strict (l1 l2 : Label) : Gen Label :=
  elements l2 (filter (fun l => isLow l1 l && negb (label_eq l l1)) (allThingsBelow l2)).

Definition gen_label_inf (inf : Info) : Gen Label :=
  gen_label (top_prin inf).

Instance smart_gen_label : SmartGen Label :=
{|
  smart_gen := gen_label_inf
|}.

(* Pointers *) 
Definition gen_Pointer (inf : Info) : Gen Pointer :=
    let '(MkInfo def _ dfs _ _) := inf in
    bindGen (elements (def, Z0) dfs) (fun mfl =>
    let (mf, len) := mfl in 
    bindGen (gen_from_length len) (fun addr =>
    returnGen (Ptr mf addr))).


Instance smart_gen_pointer : SmartGen Pointer :=
  {|
    smart_gen := gen_Pointer
  |}. 

(* Values *)
 
Definition gen_Value (inf : Info) : Gen Value := 
  let '(MkInfo def cl dfs prins _) := inf in
    frequency' (liftGen Vint arbitrary)
              [(1, liftGen Vint  (frequency' (pure Z0)
                                    [(10,arbitrary); (1,pure Z0)]));
                      (* prefering 0 over other integers (because of BNZ);
                         an alt would be to use sized here
                         (AFAIK numeric generators in Haskell QC
                          are sized by default) *)
               (1, liftGen Vcptr (gen_from_length cl));
               (1, liftGen Vptr  (smart_gen inf));
               (1, liftGen Vlab  (smart_gen inf))].

Instance smart_gen_value : SmartGen Value :=
  {|
    smart_gen := gen_Value
  |}.

(* Atoms *)

Definition gen_atom (inf : Info) : Gen Atom := 
  liftGen2 Atm (smart_gen inf) (smart_gen inf).

Instance smart_gen_atom : SmartGen Atom :=
  {|
    smart_gen := gen_atom
  |}.

(* PC *)

Definition gen_PC (inf : Info) : Gen Ptr_atom := 
  bindGen (smart_gen inf) (fun pcLab =>
  bindGen (gen_from_length (code_len inf)) (fun pcPtr =>
  returnGen (PAtm pcPtr pcLab))).

Instance smart_gen_pc : SmartGen Ptr_atom :=
  {|
    smart_gen := gen_PC
  |}.

(* ------------------------------------------------------ *)
(* --- Generation of groups of primitives --------------- *)
(* ------------------------------------------------------ *)

(* Generate a correct register file *)

Definition gen_registers (inf : Info) : Gen regSet := 
  vectorOf (no_regs inf) (smart_gen inf).

Instance smart_gen_registers : SmartGen regSet :=
  {|
    smart_gen := gen_registers
  |}.

(* Helper for well-formed stacks *)
Definition get_stack_label (s : Stack) : Label :=
  match s with
    | Mty => bot
    | RetCons (PAtm _ l, _ , _ , _) _ => l
  end.

(*
Definition meet_stack_label (s : Stack) (l : Label) : Stack :=
  match s with
    | Mty => Mty
    | RetCons (PAtm i l', rl, rs, r) s' => 
      RetCons (PAtm i (label_meet l l'), rl, rs, r) s'
  end.
*)
                                
Definition smart_gen_stack_loc (f : Label -> Label -> Gen Label) 
           (below_pc above_pc : Label) inf 
: Gen (Ptr_atom * Label * regSet * regPtr) :=
    bindGen (smart_gen inf) (fun regs =>
    bindGen (smart_gen inf) (fun pc   =>
    bindGen (gen_from_nat_length (no_regs inf)) (fun target =>
    bindGen (smart_gen inf) (fun retLab =>
    bindGen (f below_pc above_pc) (fun l' =>
    let '(PAtm addr _) := pc in
    returnGen (PAtm addr l', retLab, regs, target)))))).
  
(* Creates the stack. For SSNI just one is needed *)
(* Make sure the stack invariant is preserved 
 - no need since we only create one *)
Definition smart_gen_stack (pc : Ptr_atom) inf : Gen Stack :=
  frequency' (pure Mty)
            [(1, pure Mty);
             (9, bindGen (smart_gen_stack_loc gen_label_between_lax bot ∂pc inf) (fun sl =>
                 returnGen (RetCons sl Mty)))].
  
(* ------------------------------------------------------ *)
(* ---------- Instruction generation -------------------- *)
(* ------------------------------------------------------ *)

(* Groups registers into 4 groups, based on their content
   (data pointers, code pointers, numeric and labels)
*)
Fixpoint groupRegisters (st : State) (rs : regSet) 
         (dptr cptr num lab : list regPtr) (n : Z) :=
  match rs with
    | nil => (dptr, cptr, num, lab)
    | (Vint _ @ _) :: rs' =>
      groupRegisters st rs' dptr cptr (n :: num) lab (Zsucc n)
    | (Vptr p @ _ ) :: rs' =>
      groupRegisters st rs' (n :: dptr) cptr num lab (Zsucc n)
    | (Vcptr _ @ _) :: rs' =>                     
        groupRegisters st rs' dptr (n :: cptr) num lab (Zsucc n)
    | (Vlab _ @ _) :: rs' =>
      groupRegisters st rs' dptr cptr num (n :: lab) (Zsucc n)
  end.

Definition onNonEmpty {A : Type} (l : list A) (n : nat) :=
  match l with
    | nil => 0
    | _   => n
  end.

(* CH: TODO: Look at the large weights and try to lower them
   while preserving a near to uniform distribution;
   currently boosting BCalls, Alloc, and Store  *)

Definition ainstrSSNI (st : State) : Gen Instruction :=
  let '(St im m pr stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [] [] [] [] Z0 in
  let genRegPtr := gen_from_length (Zlength regs) in 
  frequency' (pure Nop) [
    (* Nop *)
    (1, pure Nop);
    (* Halt *)
    (0, pure Halt);
    (* PcLab *)
    (10, liftGen PcLab genRegPtr);
    (* Lab *)
    (10, liftGen2 Lab genRegPtr genRegPtr);
    (* MLab *)
    (onNonEmpty dptr 10, liftGen2 MLab (elements Z0 dptr) genRegPtr);
    (* FlowsTo *)
    (onNonEmpty lab 10,
     liftGen3 FlowsTo (elements Z0 lab) 
              (elements Z0 lab) genRegPtr);
    (* LJoin *)
    (onNonEmpty lab 10, liftGen3 LJoin (elements Z0 lab) 
                                (elements Z0 lab) genRegPtr);
    (* PutBot *)
    (10, liftGen PutBot genRegPtr);
    (* BCall *)
    (10 * onNonEmpty cptr 1 * onNonEmpty lab 1, 
     liftGen3 BCall (elements Z0 cptr) (elements Z0 lab) genRegPtr);
    (* BRet *)
    (if containsRet stk then 50 else 0, pure BRet);
    (* Alloc *)
    (200 * onNonEmpty num 1 * onNonEmpty lab 1, 
     liftGen3 Alloc (elements Z0 num) (elements Z0 lab) genRegPtr);
    (* Load *)
    (onNonEmpty dptr 10, liftGen2 Load (elements Z0 dptr) genRegPtr);
    (* Store *)
    (onNonEmpty dptr 100, liftGen2 Store (elements Z0 dptr) genRegPtr);
    (* Jump *)
    (onNonEmpty cptr 10, liftGen Jump (elements Z0 cptr));
    (* BNZ *)
    (onNonEmpty num 10,
      liftGen2 BNZ (choose (Zminus (0%Z) (1%Z), 2%Z))
                   (elements Z0 num));
    (* PSetOff *) 
    (10 * onNonEmpty dptr 1 * onNonEmpty num 1, 
     liftGen3 PSetOff (elements Z0 dptr) (elements Z0 num) genRegPtr);
    (* Output *)
    (onNonEmpty num 10,
     liftGen Output (elements Z0 num));
    (* Put *)
    (10, liftGen2 Put arbitrary genRegPtr);
    (* BinOp *)
    (onNonEmpty num 10,
     liftGen4 BinOp gen_BinOpT (elements Z0 num) 
              (elements Z0 num) genRegPtr);
    (* MSize *)
    (onNonEmpty dptr 10, liftGen2 MSize (elements Z0 dptr) genRegPtr);
    (* PGetOff *)
    (onNonEmpty dptr 10, liftGen2 PGetOff (elements Z0 dptr) genRegPtr)
].

Definition instantiate_instructions st : Gen State :=
  let '(St im m p s r pc) := st in
  bindGen (ainstrSSNI st) (fun instr =>
  let im' := replicate (length im) instr in
  returnGen (St im' m p s r pc)).

(* ------------------------------------------------------ *)
(* -------- Variations ----- ---------------------------- *)
(* ------------------------------------------------------ *)

Class SmartVary (A : Type) := {
  smart_vary : Label -> Info -> A -> Gen A
}.

(* This generator assumes that even if the label of the 
   Atoms is higher that the observablility level then their values 
   have to be of the same constructor. However this is not implied
   by indistAtom *)
(* Definition gen_vary_atom (obs: Label) (inf : Info) (a : Atom)  *)
(* : Gen Atom :=  *)
(*   let '(v @ l) := a in *)
(*   if flows l obs then returnGen a *)
(*   else  *)
(*     match v with *)
(*       | Vint  _ => liftGen2 Atm (liftGen Vint  arbitrary) (pure l) *)
(*       | Vptr  p =>  *)
(*         liftGen2 Atm (liftGen Vptr (smart_gen inf)) (pure l) *)
(*       | Vcptr c =>  *)
(*         liftGen2 Atm (liftGen Vcptr (gen_from_length (code_len inf))) (pure l) *)
(*       | Vlab  _ => *)
(*         liftGen2 Atm (liftGen Vlab (smart_gen inf)) (pure l) *)
(*     end. *)

Definition gen_vary_atom (obs: Label) (inf : Info) (a : Atom) 
: Gen Atom := 
  let '(v @ l) := a in
  if flows l obs then returnGen a
  else 
    bindGen (gen_Value inf) (fun v => 
    returnGen (v @ l)).  
           
Instance smart_vary_atom : SmartVary Atom :=
{|
  smart_vary := gen_vary_atom
|}.

(* Vary a pc. If the pc is high, then it can vary - but stay high! *)
(* LL: This doesn't result in uniform distribution of the higher pcs! *)

Definition gen_vary_pc (obs: Label) (inf : Info) (pc : Ptr_atom)
: Gen Ptr_atom :=
  let '(PAtm addr lpc) := pc in
  if isLow lpc obs then pure pc
  else
    bindGen (smart_gen inf) (fun pc' =>
    let '(PAtm addr' lpc') := pc' in
    if (isHigh lpc' obs) then returnGen pc' 
    else returnGen (PAtm addr' (lpc' ∪ lpc))).

(* This generator fails to generate PCs with label higher that the observability 
   level and lower than pc's label *)  
   
(* Definition gen_vary_pc (obs: Label) (inf : Info) (pc : Ptr_atom) *)
(* : Gen Ptr_atom := *)
(*   let '(PAtm addr lpc) := pc in *)
(*   if isLow lpc obs then pure pc *)
(*   else *)
(*     bindGen (smart_gen inf) (fun pc' => *)
(*     let '(PAtm addr' lpc') := pc' in *)
(*     returnGen (PAtm addr' (lpc' ∪ lpc))). *)

Instance smart_vary_pc : SmartVary Ptr_atom :=
{|
  smart_vary := gen_vary_pc
|}.


(* Vary a single memory frame : 
   - stamp is high -> vary the label and arbitrary data
   - stamp is low 
      + stamp join label is high -> arbitrary data
      + stamp join label is low -> vary data

  @Catalin: Should we ever vary stamps? 
*)

Definition gen_var_frame (obs: Label) (inf : Info) (f : frame) 
: Gen frame :=
    let '(Fr stamp lab data) := f in
    let gen_length := 
        choose (List.length data, S (List.length data)) in
    let gen_data := 
        bindGen gen_length (fun len => vectorOf len (smart_gen inf)) in
    if isHigh stamp obs then
      bindGen (smart_gen inf) (fun lab' =>
      bindGen gen_data (fun data' =>
      returnGen (Fr stamp lab' data')))
                    (* CH: above indistFrame allows different stamp *)
    else if isHigh (stamp ∪ lab) obs then
      (* CH: Can't understand the need for this case *)
      bindGen gen_data (fun data' =>
      returnGen (Fr stamp lab data'))
    else
      bindGen (sequenceGen (map (smart_vary obs inf) data))
              (fun data' =>
      returnGen (Fr stamp lab data')).
                    (* CH: above indistFrame allows different High stamp *)

 
Instance smart_vary_frame : SmartVary frame :=
{|
  smart_vary := gen_var_frame
|}.

(* Helper. Takes a single mframe pointer and a memory, and varies the 
   corresponding frame *)
Definition handle_single_mframe obs inf (m : memory) (mf : mframe) 
: Gen memory :=
  match Mem.get_frame m mf with
    | Some f => 
      bindGen (smart_vary obs inf f) (fun f' =>
      match Mem.upd_frame m mf f' with
        | Some m' => returnGen m'
        | None    => returnGen m
      end)
    | None => returnGen m
  end.

Definition gen_vary_memory  obs inf (m : memory)
: Gen memory := 
  let all_mframes := Mem.get_all_blocks (top_prin inf) m in
  foldGen (handle_single_mframe obs inf) all_mframes m.


(* Vary memory *)
Instance smart_vary_memory : SmartVary memory :=
{|
  smart_vary := gen_vary_memory
|}.
 
(* A variation of gen_vary_stack_loc where pc, lab and r vary
   when pc is high *)

(*  Definition gen_vary_stack_loc (obs: Label) (inf : Info)  *)
(*            (s : Ptr_atom * Label * regSet * regPtr)  *)
(* : Gen  (Ptr_atom * Label * regSet * regPtr) := *)
(*     let '(pc, lab, rs, r) := s in *)
(*     (* If the return label is low just vary the registers (a bit) *) *)
(*     if isLow ∂pc obs then  *)
(*       bindGen (sequenceGen (map (smart_vary obs inf) rs)) (fun rs' => *)
(*       returnGen (pc, lab, rs', r)) *)
(*     else  *)
(*     (* Return label is high, create new register file *) *)
(*     (* ZP: Why not vary pc, lab and r? *) *)
(*       bindGen (vectorOf (no_regs inf) (smart_gen inf)) (fun rs' => *)
(*       bindGen (smart_vary obs inf pc) (fun pc' => *)
(*       bindGen (smart_gen inf) (fun lab' => *)
(*       bindGen (gen_from_nat_length (no_regs inf)) (fun r' => *)
(*       returnGen (pc', lab', rs', r'))))). *)

  
Definition gen_vary_stack_loc (obs: Label) (inf : Info)
           (s : Ptr_atom * Label * regSet * regPtr)
: Gen  (Ptr_atom * Label * regSet * regPtr) :=
    let '(pc, lab, rs, r) := s in
    (* If the return label is low just vary the registers (a bit) *)
    if isLow ∂pc obs then
      bindGen (sequenceGen (map (smart_vary obs inf) rs)) (fun rs' =>
      returnGen (pc, lab, rs', r))
    else
    (* Return label is high, create new register file *)
    (* ZP: Why not generate new pc, lab and r? *)
      bindGen (vectorOf (no_regs inf) (smart_gen inf)) (fun rs' =>
      returnGen (pc, lab, rs', r)).

(* Just vary a single stack location *)
Instance smart_vary_stack_loc : SmartVary (Ptr_atom * Label * regSet * regPtr) :=
{|
  smart_vary := gen_vary_stack_loc
|}.

Definition gen_vary_stack (obs: Label) (inf : Info) (s: Stack) : Gen Stack :=
  let fix aux (s : Stack) := 
      match s with
        | Mty => pure Mty 
        | RetCons sl s' => 
          bindGen (smart_vary obs inf sl) (fun sl' =>
            bindGen (aux s') (fun s'' => 
            returnGen (RetCons sl' s'')))
        end in
    aux s.

  
(* In here I don't have information if the pc is high - 
   create extra "high" stack locations in vary state *)
Instance smart_vary_stack : SmartVary Stack :=
{|
  smart_vary := gen_vary_stack
|}.

Definition gen_vary_state (obs: Label) (inf : Info) (st: State) : Gen State :=
    let '(St im μ π s r pc) := st in
    if isLow ∂pc obs then 
      (* PC is low *)
      bindGen (sequenceGen (map (smart_vary obs inf) r)) (fun r' =>
      bindGen (smart_vary obs inf μ) (fun μ' =>
      bindGen (smart_vary obs inf s) (fun s' =>
      returnGen (St im μ' π s' r' pc))))
    else 
      (* PC is high *)
      bindGen (smart_vary obs inf pc) (fun pc' =>
      (* Memory varies the same way *)                                        
      bindGen (smart_vary obs inf μ) (fun μ' =>
      (* Stack varies the same way at first *)
      bindGen (smart_vary obs inf s) (fun s_imm =>
      (* LL: Revisit this. Add arbitrary stack locations? 
         For now make sure it is high *)
(* CH: this is broken (no H->L cases); and way too complicated
      let low_limit := join_label obs (get_stack_label s_imm) in
      let gen_l_fun := if isHigh low_limit obs then gen_label_between_lax 
                       else gen_label_between_strict in
      bindGen (smart_gen_stack_loc gen_l_fun low_limit ∂pc inf) (fun sl =>
(* This doesn't work better! *)                                                    
                
(*       bindGen (smart_gen_stack_loc gen_label_between_strict obs ∂pc inf) (fun sl => *)

      let s' := RetCons sl s_imm in 
*)

(* CH: this expedient fix (probably still broken) already finds Mutant 9 *)
      let s' := s_imm in

      (* Recreate registers *)
      bindGen (vectorOf (no_regs inf) (smart_gen inf)) (fun r' =>
      returnGen (St im μ' π s' r' pc'))))).


(* Make sure you create an extra stack loc if pc is high *)
Instance smart_vary_state : SmartVary State :=
  {| 
    smart_vary := gen_vary_state
  |}.

(* ------------------------------------------------------ *)
(* -------- Final generation ---------------------------- *)
(* ------------------------------------------------------ *)

(* Generation and population of memory. Doesn't need to use the constants? *)
(*
Instance smart_gen_memory : SmartGen memory :=
{|
  smart_gen inf :=
    let '(MkInfo _ cl _ prins) := inf in
    

    if Z_eq df1 1%Z && Z_eq df2 2%Z then
    let (_, mI) := extend empty (CFR (replicate cfrSize Nop)) in
    bindGen (genLabel prins) (fun dfrLab1 =>
    bindGen (vectorOf dfrSize1 (genAtom prins cfs dfs)) (fun data1 =>
    let (_, mM) := extend mI (DFR data1 dfrLab1) in
    bindGen (genLabel prins) (fun dfrLab2 =>
    bindGen (vectorOf dfrSize2 (genAtom prins cfs dfs)) (fun data2 =>
    let (_, m) := extend mM (DFR data2 dfrLab2) in
    returnGen m))))
  else Property.trace "Fix Constants" (returnGen empty).
*)


Definition gen_top : Gen Label :=
  bindGen (choose (C.min_no_prins, 
                      C.max_no_prins)) (fun no_prins =>
  returnGen (label_of_list (map Z.of_nat (seq 1 no_prins)))).


(* Generates a memory adhering to the above constants *)
(* Stamps are bottom everywhere - to be created later *)

Fixpoint gen_init_mem_helper top (n : nat) (ml : memory * list (mframe * Z)) :=
  match n with
    | O    => returnGen ml
    | S n' => 
      let (m, l) := ml in
      bindGen (choose (C.min_frame_size,
                       C.max_frame_size)) (fun frame_size =>
      bindGen (gen_label top) (fun lab =>
         match (alloc frame_size lab bot (Vint Z0 @ bot) m) with
           | Some (mf, m') => 
             gen_init_mem_helper top n' (m', (mf,frame_size) :: l)
           | None => gen_init_mem_helper top n' ml
         end))
  end.

Definition gen_init_mem (top : Label) : Gen (memory * list (mframe * Z)):=
  bindGen (choose (C.min_no_frames,
                      C.max_no_frames)) (fun no_frames =>
  gen_init_mem_helper top no_frames (Mem.empty Atom Label, [])).

Definition failed_state : State :=
  Property.trace "Failed State!" 
                 (St [] (Mem.empty Atom Label) bot Mty [] (PAtm Z0 bot)).


Definition populate_frame inf (m : memory) (mf : mframe) : Gen memory :=
  match Mem.get_frame m mf with
    | Some (Fr stamp lab data) =>
      bindGen (vectorOf (length data) (smart_gen inf)) (fun data' =>
      match Mem.upd_frame m mf (Fr stamp lab data') with
        | Some m' => returnGen m'
        | _ => pure m
      end)
    | _ => pure m
  end.

Definition populate_memory inf (m : memory) : Gen memory :=
  (* Isn't this supposed to be exactly what is store in Info's data_len field?*)
  (* let all_frames := Mem.get_all_blocks (top_prin inf) m in *)
  let all_frames := map fst (data_len inf) in 
  foldGen (populate_frame inf) all_frames m.


(* FIX this to instantiate stamps to a non-trivially well-formed state *)
Definition instantiate_stamps (st : State) : State := st.

Definition get_blocks_and_sizes (top : Label) (m : memory) :=
  map 
    (fun b => 
    let length := 
        match Mem.get_frame m b with
          | Some fr => 
            let 'Fr _ _ data := fr in length data 
          | _ => 0 
        end in (b, Z.of_nat length)) (Mem.get_all_blocks top m).


(* Generate an initial state.
   TODO : Currently stamps are trivially well formed (all bottom) *)
Definition gen_variation_state : Gen (@Variation State) :=
  (* Generate basic machine *)
  bindGen gen_top (fun prins =>            
  (* Generate initial memory and dfs *)
  bindGen (gen_init_mem prins) (fun init_mem_info =>
  let (init_mem, dfs) := init_mem_info in
  (* Generate initial instruction list *)
  let imem := replicate (C.code_len) Nop in
  (* Create initial info - if this fails, fail the generation *)
  match dfs with
    | (def, _) :: _ =>
      let inf := MkInfo def (Z.of_nat C.code_len) dfs prins C.no_registers in
      (* Generate pc, registers and stack - all pointer stamps are bottom *)
      bindGen (smart_gen inf) (fun pc =>
      bindGen (smart_gen inf) (fun regs =>
      bindGen (smart_gen_stack pc inf) (fun stk =>
      (* Populate the memory - still all stamps are bottom *)
      bindGen (populate_memory inf init_mem) (fun m =>
      (* Instantiate instructions *)
      let st := St imem m prins stk regs pc in 
      bindGen (instantiate_instructions st) (fun st =>
      (* Instantiate stamps *)
      let st := instantiate_stamps st in
      (* Create Variation *)
      (* bindGen (gen_label_between_lax (get_stack_label stk) prins) (fun obs => *)
      bindGen (gen_label_between_lax bot prins) (fun obs =>      
      bindGen (smart_vary obs inf st) (fun st' =>
      returnGen (Var obs st st'))))))))
    | _ => returnGen (Var bot failed_state failed_state)
  end)).

End CustomGens. 

Instance arbBinOpT : Arbitrary BinOpT :=
{| 
  arbitrary := @gen_BinOpT;
  shrink o  := match o with
               | BAdd => nil
               | BMult => [BAdd]
               end
|}.
