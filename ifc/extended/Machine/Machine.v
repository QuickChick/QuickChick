Require Import ZArith.
Require Export Instructions.
Require Import List.
Require Import Rules.

Require Export Lattices.
Require Export Memory.
Require Export Primitives.
Require Import EquivDec.

Open Scope Z_scope.
Open Scope bool_scope.

Record State := St {
  st_imem: imem;   (* instruction memory *)                  
  st_mem: memory;  (* memory *)
  st_pr: Label;     (* prins *)
  st_stack: Stack; (* operand stack *)
  st_regs: regSet; (* register set *)
  st_pc: Ptr_atom  (* program counter *)
}.
(* No longer need to carry the principals without dynamic principal allocation,
   however it helps with reachability and generation. Is it necessary to find
   an alternative? *)

(* List manipulation helpers *)
Definition nth {A:Type} (l:list A) (n:Z) : option A :=
  if Z_lt_dec n 0 then None
  else nth_error l (Z.to_nat n).

Fixpoint upd_nat {A:Type} (l:list A) (n:nat) (a:A) : option (list A) :=
  match l with
    | nil => None
    | x::q =>
      match n with
        | O => Some (a::q)
        | S p => 
          match upd_nat q p a with
            | None => None
            | Some q' => Some (x::q')
          end
      end
  end.

Definition upd {A:Type} (l:list A) (n:Z) (a:A) : option (list A) :=
  if Z_lt_dec n 0 then None
  else upd_nat l (Z.to_nat n) a.

Definition registerUpdate (rs : regSet) (r : regPtr) (a : Atom) :=
  upd rs r a.
Definition registerContent (rs : regSet) (r : regPtr) :=
  nth rs r.

(** Rule Table *)

Local Open Scope nat.
Definition labelCount (c:OpCode) : nat :=
  match c with
  | OpLab     => 0
  | OpMLab    => 2
  | OpPcLab   => 0
  | OpBCall   => 2
  | OpBRet    => 3 
  | OpFlowsTo => 2
  | OpLJoin   => 2
  | OpPutBot  => 0
  | OpNop     => 0
  | OpPut     => 0
  | OpBinOp   => 2
  | OpJump    => 1
  | OpBNZ     => 1
  | OpLoad    => 3
  | OpStore   => 3
  | OpAlloc   => 3
  | OpPSetOff => 2
  | OpOutput  => 1
  | OpPGetOff => 1
  | OpMSize   => 2
end.

Definition table := forall op, AllowModify (labelCount op).

Definition default_table : table := fun op =>
  match op with
  | OpLab     =>  ≪ TRUE , BOT , LabPC ≫ 
  | OpMLab    =>  ≪ TRUE , Lab1 , LabPC ≫ 
  | OpPcLab   =>  ≪ TRUE , BOT , LabPC ≫ 
  | OpBCall   =>  ≪ TRUE , JOIN Lab2 LabPC , JOIN Lab1 LabPC
                    (* CH: No counterexample justifying joining Lab2 to PC;
                           we did that in all calculi so far, but why?
                           (I vaguely remember this was discussed before) *) ≫
  | OpBRet    =>  ≪ LE (JOIN Lab1 LabPC) (JOIN Lab2 Lab3) , Lab2 , Lab3 ≫ 
  | OpFlowsTo =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫ 
  | OpLJoin   =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫ 
  | OpPutBot  =>  ≪ TRUE , BOT , LabPC ≫ 
  | OpNop     =>  ≪ TRUE , __ , LabPC ≫ 
  | OpPut     =>  ≪ TRUE , BOT , LabPC ≫ 
  | OpBinOp   =>  ≪ TRUE , JOIN Lab1 Lab2, LabPC ≫ 
  | OpJump    =>  ≪ TRUE , __ , JOIN LabPC Lab1 ≫ 
  | OpBNZ     =>  ≪ TRUE , __ , JOIN Lab1 LabPC ≫ 
  | OpLoad    =>  ≪ TRUE , Lab3 , JOIN LabPC (JOIN Lab1 Lab2) ≫ 
  | OpStore   =>  ≪ LE (JOIN Lab1 LabPC) Lab2 , Lab3 , LabPC ≫ 
  | OpAlloc   =>  ≪ TRUE (* AND (AND (LE Lab2 LabPC)
                              (LE Lab1 Lab3))
                              (LE LabPC Lab3)*),
          (* CH: more restrictive check than I was expecting;
                 why LE Lab2 LabPC? (falsifiable!)
                 why LE Lab2 Lab3? (no counter! DROPPED!)
                 why LE Lab1 Lab3? (ott had it, but why? falsifiable!)
                 why LE LabPC Lab3? (ott had it, but why? no counter!)
                 why join Lab1 to reslult value? no counter! DROPPED! *)
                    JOIN Lab1 Lab2 , LabPC ≫
  | OpPSetOff =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫ 
  | OpOutput  =>  ≪ TRUE , JOIN Lab1 LabPC , LabPC ≫
  | OpPGetOff =>  ≪ TRUE , Lab1 , LabPC ≫
  | OpMSize   =>  ≪ TRUE , Lab2 , JOIN LabPC Lab1 ≫
end.


Definition run_tmr (t : table) (op: OpCode)
  (labs:Vector.t Label (labelCount op)) (pc: Label)
   : option (option Label * Label) :=  
  let r := t op in
  apply_rule r labs pc.

(** Relational semantics *)

Local Open Scope Z_scope.
(* TODO : reimplement relational semantics 
Inductive step (t : table) : State -> trace -> State -> Prop :=
 | step_lab: forall im μ σ v K pc r r' r1 r2 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Lab r1 r2))
     (REG1: registerContent r r1 = Some (v @ K))
     (TMU: run_tmr t OpLab <||> LPC = Some (Some rl, rpcl))
     (UPD: registerUpdate r r2 (Vlab K @ rl) = Some r'),
     step t
          (St im μ σ r  pc) 
          nil
          (St im μ σ r' (PAtm (j+1) rpcl))
 | step_pclab: forall μ π σ pc r r' r1 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (PcLab r1))
     (TMU: run_tmr t OpPcLab <||> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r1 (Vlab (∂ pc) @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
(* | step_memlab: forall μ π σ pc p K C r r' r1 r2 fp j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (MLab r1 r2))
     (MEMLAB: mlab μ p = Some C)
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (TMU: run_tmr t OpMLab <|K; C|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (Vlab C @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
*)
 | step_mlab: forall μ π σ pc r r1 r2 p K j LPC rpcl
     (CODE: μ[pc] = Some (MLab r1 r2))
     (PC: pc = PAtm j LPC)
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (TMU : run_tmr t OpMLab <|K; K|> LPC = Some (None, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r (PAtm (Zsucc j) rpcl))

  | step_flowsto: forall μ π σ pc L1 K1 L2 K2 r r' r1 r2 r3 res j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (FlowsTo r1 r2 r3))
     (MEMLAB: res = flows_to L1 L2)
     (OP1 : registerContent r r1 = Some (Vlab L1 @ K1))
     (OP2 : registerContent r r2 = Some (Vlab L2 @ K2))
     (TMU : run_tmr t OpFlowsTo <|K1; K2|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r3 (Vint res @ rl) = Some r'),
     step t
       (St μ π σ r pc) 
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_ljoin: forall μ π σ pc L1 K1 L2 K2 r r' r1 r2 r3 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (LJoin r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vlab L1 @ K1))
     (OP2 : registerContent r r2 = Some (Vlab L2 @ K2))
     (TMU : run_tmr t OpLJoin <|K1; K2|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r3 (Vlab (L1 ∪ L2) @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_pushbot: forall μ π σ pc r r' r1 j LPC rl rpcl
     (CODE: μ[pc] = Some (PutBot r1))
     (TMU : run_tmr t OpPutBot <||> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r1 (Vlab bot @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_bcall: forall μ π σ pc (pc':Ptr_atom) B K r r1 r2 r3 fp j L jpc Lpc rl rpcl
     (PC: pc = PAtm jpc Lpc)
     (CODE: μ[pc] = Some (BCall r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp j) @ L))
     (OP2 : registerContent r r2 = Some (Vlab B @ K))
     (TMU : run_tmr t OpBCall <|L; K|> Lpc = Some (Some rl, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π (((PAtm (jpc+1) rl), B, r, r3 ) ::: σ) 
           r (PAtm j rpcl))
 | step_bret: forall μ π σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl
     (PC: pc  = PAtm j  LPC)
     (PC: pc' = PAtm j' LPC')
     (CODE: μ[pc] = Some BRet)
     (STAYS : registerContent r r1 = Some (a @ R))
     (TMU : run_tmr t OpBRet <|R; B; LPC'|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r' r1 (a @ rl) = Some r''),
     step t
       (St μ π ((pc',B,r',r1) ::: σ) r pc)
       nil
       (St μ π σ r'' (PAtm j' rpcl))
 | step_alloc: forall μ σ pc mem mem' r r' r1 r2 r3 msize K L K' rl rpcl jpc LPC fp
     (PC: pc = PAtm jpc LPC)
     (CODE: μ[pc] = Some (Alloc r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vint msize @ K))
     (OP2 : registerContent r r2 = Some (Vlab L @ K'))
     (TMU : run_tmr t OpAlloc <|K; K'; L|> LPC = Some (Some rl, rpcl))
     (ALLOC: alloc msize L rl (Vint 0 @ ⊥) mem = Some (fp, mem'))
     (* LL: Using label L directly as the label of the mframe,
        also using rl for both the pointer label and the stamp *)
     (RES : registerUpdate r r3 (Vptr (Ptr fp 0) @ rl) = Some r'),
     step t
       (St μ mem σ r pc)
       nil
       (St μ mem' σ r' (PAtm (jpc+1) rpcl))
 | step_load: forall μ π σ pc C p K r r' r1 r2 fp j LPC v L rl rpcl
     (PC  : pc = PAtm j LPC)
     (CODE: μ[pc] = Some (Load r1 r2))
     (READ: read μ p = Some (v @ L))
     (MLAB: mlab μ p = Some C)
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (TMU : run_tmr t OpLoad <|K; C; L|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (v @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_store: forall μ π σ pc v L C p K μ' r r1 r2 fp j LPC rpcl rl
     (PC  : pc = PAtm j LPC)
     (CODE: μ[pc] = Some (Store r1 r2))
     (WRITE: store μ p (v @ L) = Some μ')
     (MLAB: mlab μ p = Some C) 
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (OP2 : registerContent r r2  = Some (v @ L))
     (TMU : run_tmr t OpStore <|K; C; L|> LPC = Some (Some rl, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ' π σ r (PAtm (j+1) rpcl))
 | step_jump: forall μ π σ pc (pc':Ptr_atom) fp j L r r1 fpc jpc LPC rpcl
     (PC: pc = PAtmc jpc LPC)
     (CODE: μ[pc] = Some (Jump r1))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp j) @ L))
     (TMU: run_tmr t OpJump <|L|> LPC = Some (None, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r (PAtm j rpcl))
 | step_bnz_yes: forall μ π σ pc n m K r r1 fp j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (BNZ n r1))
     (TEST: m <> 0)
     (OP1 : registerContent r r1 = Some (Vint m @ K))
     (TMU: run_tmr t OpBNZ <|K|> LPC = Some (None, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r (PAtm (j + n) rpcl))
 | step_bnz_no: forall μ π σ pc n m K r r1 fp j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (BNZ n r1))
     (TEST: m = 0)
     (OP1 : registerContent r r1 = Some (Vint m @ K))
     (TMU: run_tmr t OpBNZ <|K|> LPC = Some (None, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r (PAtm (j + 1) rpcl))
 | step_psetoff: forall μ π σ pc fp j K1 n K2 r r' r1 r2 r3 fpc jpc LPC rl rpcl
     (PC: pc = PAtmc jpc LPC)
     (CODE: μ[pc] = Some (PSetOff r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp j) @ K1))
     (OP2 : registerContent r r2 = Some (Vint n @ K2))
     (TMU: run_tmr t OpPSetOff <|K1; K2|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r3 (Vptr (Ptr fp n) @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtmc (jpc + 1) rpcl))
 | step_output: forall μ π σ pc (ov:Obs_value) v K r r1 fp j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (Output r1))
     (CONV: obs_value_to_value ov = v)
     (OP1 : registerContent r r1 = Some (v @ K))
     (TMU : run_tmr t OpOutput <| K |> LPC = Some (Some rl, rpcl)),
     step t
       (St μ π σ r pc)
       ((ov,rl) :: nil)%list
       (St μ π σ r (PAtm (j+1) rpcl))
 | step_push: forall μ π σ pc x r r' r1 fp j LPC rl rpcl
     (PC: pc = PAtm j LPC)                     
     (CODE: μ[pc] = Some (Put x r1))
     (TMU : run_tmr t OpPut <||> LPC = Some (Some rl, rpcl))
     (OP1 : registerUpdate r r1 (Vint x @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_binop: forall μ π σ pc o n1 L1 n2 L2 n r r1 r2 r3 r' fp j LPC rl rpcl
     (PC: pc = PAtm j LPC)                     
     (CODE: μ[pc] = Some (BinOp o r1 r2 r3 ))
     (BINOP: eval_binop o n1 n2 = Some n)
     (OP1 : registerContent r r1 = Some (Vint n1 @ L1))
     (OP2 : registerContent r r2 = Some (Vint n2 @ L2))
     (TMU : run_tmr t OpBinOp <|L1; L2|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r3 (Vint n @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_nop: forall μ π σ pc r fp j LPC rpcl
     (CODE: μ[pc] = Some Nop)
     (PC: pc = PAtm j LPC)
     (TMU : run_tmr t OpNop <||> LPC = Some (None, rpcl)),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r (PAtm (Zsucc j) rpcl))
 | step_msize: forall μ π σ pc p K C r r' r1 r2 fp j LPC rl rpcl n
     (PC: pc = PAtm j LPC)
     (CODE: μ[pc] = Some (MSize r1 r2))
     (MLAB: mlab μ p = Some C)
     (MSIZE: msize μ p = Some n)
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (TMU: run_tmr t OpMSize <|K; C|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (Vint (Z.of_nat n) @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtm (j+1) rpcl))
 | step_pgetoff: forall μ π σ pc fp j K r r' r1 r2 fpc jpc LPC rl rpcl
     (PC: pc = PAtmc jpc LPC)
     (CODE: μ[pc] = Some (PGetOff r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp j) @ K))
     (TMU: run_tmr t OpPGetOff <|K|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (Vint j @ rl) = Some r'),
     step t
       (St μ π σ r pc)
       nil
       (St μ π σ r' (PAtmc (jpc + 1) rpcl))
.
*)

(** * Executable semantics *)

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a 
    end.
Notation "'do' X <- A ; B" :=
  (bind _ _ (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' X : T <- A ; B" :=
  (bind _ _ (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Definition state_instr_lookup (st:State) : option Instruction :=
  let (μ,_,_,_,_,pc) := st in μ[pc].

Definition exec t (st:State) : option (trace * State) :=
  do instr <- state_instr_lookup st;
  let '(St imem μ π σ r pc) := st in
  let '(PAtm j LPC) := pc in
  match instr with
    | Lab r1 r2 =>
      match registerContent r r1 with
        | Some (_ @ K) =>
          match run_tmr t OpLab <||> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r2 (Vlab K @ rl);
                Some (nil, St imem μ π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | None => None
      end
    | PcLab r1 =>
      match run_tmr t OpPcLab <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vlab (∂ pc) @ rl);
            Some (nil,
                  St imem μ π σ r' (PAtm (j+1) rpcl))
        | _ => None
      end
    | MLab r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do C <- mlab μ p;
            match run_tmr t OpMLab <|K; C|> LPC with
              | Some (Some rl, rpcl) =>
                do r' <- registerUpdate r r2 (Vlab C @ rl);
                Some (nil,
                  St imem μ π σ r' (PAtm (j+1) rpcl))
              | _ => None
            end
        | _ => None
      end
    | FlowsTo r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vlab L1 @ K1), Some (Vlab L2 @ K2) =>
          let res := flows_to L1 L2 in
          match run_tmr t OpFlowsTo <|K1; K2|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r3 (Vint res @ rl);
              Some (nil,
                  St imem μ π σ r' (PAtm (j+1) rpcl))
              | _ => None
            end
        | _, _ => None
      end
    | LJoin r1 r2 r3 => 
      match registerContent r r1, registerContent r r2 with
        | Some (Vlab L1 @ K1), Some (Vlab L2 @ K2) =>
          match run_tmr t OpLJoin <|K1; K2|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r3 (Vlab (L1 ∪ L2) @ rl);
              Some (nil,
                    St imem μ π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | PutBot r1 =>
      match run_tmr t OpPutBot <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vlab bot @ rl);
          Some (nil,
                St imem μ π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
    | BCall r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vcptr addr @ L), Some (Vlab B @ K) =>
          match run_tmr t OpBCall <|L; K|> LPC with
            | Some (Some rl, rpcl) =>
              Some (nil, 
                    St imem μ π (((PAtm (j+1) rl), B, r, r3) ::: σ) r 
                       (PAtm addr rpcl))
            | _ => None 
          end
        | _, _ => None
      end
    | BRet =>
      match σ with
        | (PAtm jp' LPC', B, savedRegs, r1) ::: σ' =>
          do r1Cont <- registerContent r r1;
          let '(a @ R) := r1Cont in
          match run_tmr t OpBRet <|R; B; LPC'|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate savedRegs r1 (a @ rl);
              Some (nil,
                    St imem μ π σ' r' (PAtm jp' rpcl))
            | _ => None
          end
        | _ => None
      end
    | Alloc r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vint i @ K), Some (Vlab L @ K') =>
          match run_tmr t OpAlloc <|K; K'; L|> LPC with
            | Some (Some rl, rpcl) =>
              let stmp := K ∪ K' ∪ LPC in
                 (* this stamp is just instrumentation;
                    and it doesn't go via the rule table *)
              do alloc_res : (mframe * memory) <- alloc i L stmp (Vint 0 @ ⊥) μ;
              let (dfp, μ') := alloc_res in
              do r' <- registerUpdate r r3 (Vptr (Ptr dfp 0) @ rl);
              Some (nil,
                    St imem μ' π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Load r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do a <- load μ p;
            let '(v @ L) := a in
            do C <- mlab μ p;
            match run_tmr t OpLoad <|K; C; L|> LPC with
              | Some (Some rl (* L *), rpcl (* LPC ∪ K ∪ C *)) =>
                do r' <- registerUpdate r r2 (v @ rl);
                Some (nil,
                      St imem μ π σ r' (PAtm (j+1) (rpcl)))
              | _ => None
            end
        | _ => None
      end
    | Store r1 r2 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vptr p @ K), Some (v @ L) =>
          do C <- mlab μ p;
          match run_tmr t OpStore <|K; C; L|> LPC with
            (* check: K ∪ LPC <: C *)
            | Some (Some rl (* L *), rpcl (* LPC *)) =>
              do μ' <- store μ p (v @ rl);
              Some (nil,
                    St imem μ' π σ r (PAtm (j+1) rpcl))
            | _ => None 
          end
        | _, _ => None
      end
    | Jump r1 =>
      match registerContent r r1 with
        | Some (Vcptr addr @ L) =>
          match run_tmr t OpJump <|L|> LPC with
            | Some (None, rpcl) =>
              Some (nil,
                St imem μ π σ r (PAtm addr rpcl))
            | _ => None 
          end
        | _ => None 
      end
    | BNZ n r1 =>
      match registerContent r r1 with
        | Some (Vint m @ K) =>
          match run_tmr t OpBNZ <|K|> LPC with 
            | Some (None, rpcl) =>
              let new_pc := (if Z_eq_dec m 0 then j+1 else j+n) in
                Some (nil, 
                      St imem μ π σ r (PAtm new_pc rpcl))
            | _ => None
          end
        | _ => None
      end
    | PSetOff r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vptr (Ptr fp' j') @ K1), Some (Vint n @ K2) =>
          match run_tmr t OpPSetOff <|K1; K2|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r3 (Vptr (Ptr fp' n) @ rl);
              Some (nil,
                    St imem μ π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Output r1 =>
      match registerContent r r1 with
        | Some (Vint n @ K) =>
          match run_tmr t OpOutput <| K |> LPC with
            | Some (Some rl, rpcl) =>
              Some (((OVint n, rl) :: nil)%list,
                    St imem μ π σ r (PAtm (j+1) rpcl))
            | _ => None 
          end
        | _ => None
      end
    | Put x r1 =>
      match run_tmr t OpPut <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vint x @ rl);
            Some (nil,
                    St imem μ π σ r' (PAtm (j+1) rpcl))
        | _ => None 
      end
     | BinOp o r1 r2 r3 =>
       match registerContent r r1, registerContent r r2 with
         | Some (Vint n1 @ L1), Some (Vint n2 @ L2) =>
           do n <- eval_binop o n1 n2;
           match run_tmr t OpBinOp <|L1; L2|> LPC with
             | Some (Some rl, rpcl) =>
               do r' <- registerUpdate r r3 (Vint n @ rl);
               Some (nil,
                     St imem μ π σ r' (PAtm (j+1) rpcl))
             | _ => None 
           end
         | _, _ => None 
       end
     | Nop =>
       match run_tmr t OpNop <||> LPC with
         | Some (None, rpcl) =>
           Some (nil,
               St imem μ π σ r (PAtm (j+1) rpcl))
         | _ => None
       end
    | MSize r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do C <- mlab μ p;
            do n <- msize μ p;
            match run_tmr t OpMSize <|K; C|> LPC with
              | Some (Some rl, rpcl) =>
                do r' <- registerUpdate r r2 (Vint (Z.of_nat n) @ rl);
                Some (nil,
                  St imem μ π σ r' (PAtm (j+1) rpcl))
              | _ => None
            end
        | _ => None
      end
    | PGetOff r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr (Ptr fp' j') @ K) =>
          match run_tmr t OpPGetOff <|K|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r2 (Vint j' @ rl);
              Some (nil,
                    St imem μ π σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end.

Ltac exec_solver :=
  repeat (simpl; match goal with
            | |- context[registerContent ?rs ?reg] =>
              remember (registerContent rs reg) as Hyp; destruct Hyp
            | |- context[do _ <- Some ?x; _] => 
              case_eq x; [simpl; intro; intro|simpl; congruence]  
            | |- context[do _ <- ?x; _] => 
              case_eq x; [simpl; intro; intro|simpl; congruence]  
            | |- context[match ?s with | (_,_) => _ end] => 
              case_eq s; intro; intro; intro
            | |- context[match ?s with | _ => _ end] => 
              destruct s
            | |- context[match ?s with | Some _ => _ | None => _ end] =>
              destruct s
(*            | |- context[Atm (Vptr (Ptr ?fp ?i)) ?l] => 
              replace (Vptr (Ptr fp i) @ l) with (ptr_atom_to_atom (PAtm i l)) by auto
*)
            | |- Some _ = None -> _ => intros contra; inversion contra
            | |- None = Some _ -> _ => intros contra; inversion contra
            | |- context[cons (OVint ?n, _) nil] => 
              replace (Vint n) with (obs_value_to_value (OVint n)) by auto
          end); try congruence;
  try match goal with
    | |- Some _ = Some _ -> _ => 
      intros T; inversion T; clear T; subst; try (econstructor (solve[eauto]))
  end.

(*
Hint Unfold run_tmr.
Hint Unfold apply_rule.
Hint Unfold default_table.
Hint Resolve Ptr_atom_inhabited.
Theorem exec_make_a_step : forall t st1 st2 tr,
  exec t st1 = Some (tr, st2) ->
  step t st1 tr st2.
Proof.
  destruct st1 as (μ,π,σ,regs,pc).
  unfold exec; simpl.
  case_eq (μ[pc]); simpl bind; [|simpl bind; congruence].
  intros ins Hins.
  intros st2 tr.
  destruct ins; 
  exec_solver;
  try solve [econstructor; eauto; auto].
Admitted.
(*
  (* TODO: Figure out how to choose the correct econstructor *)
  eapply step_memlab; eauto; auto.
  eapply step_pclab; eauto; auto.
  eapply step_bret; eauto; auto. admit. (* FIX RET! *)
  eapply step_flowsto; eauto; auto.
  eapply step_ljoin; eauto; auto.
  eapply step_pushbot; eauto; auto.
    instantiate (1 := l); auto.
  eapply step_push; eauto; auto. 
  eapply step_binop; eauto; auto.
  eapply step_jump; eauto; auto. admit.
  eapply step_load; eauto; auto.
  eapply step_store; eauto; auto. admit. (* WHY!? *)
  eapply step_alloc; eauto; auto. admit.
  eapply step_psetoff; eauto; auto.
Qed.
*)
*)
Fixpoint execN t (n : nat) (s : State) : trace * list State :=
  match n with
    | O => (nil, s :: nil)
    | S n' =>
      match exec t s with
        | Some (tr, s') =>
          let res := execN t n' s' in
          (app tr (fst res), s :: snd res)
        | None => (nil, s :: nil)
      end
  end%list.

Fixpoint observe (l : Label) (t : trace) : list Obs_value :=
  match t with
    | (v, l') :: t' =>
      if flows l' l then
        v :: observe l t'
      else observe l t'
    | nil => nil
  end%list.

Fixpoint observe_comp (t1 t2 : list Obs_value) : bool :=
  match t1, t2 with
    | o1 :: t1', o2 :: t2' =>
      Obs_value_eq o1 o2 && observe_comp t1' t2'
    | _, _ => true
  end%list.
