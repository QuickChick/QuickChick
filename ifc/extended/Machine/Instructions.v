(* Instructions of the micro machine *)
Require Import ZArith.
Require Import List. Import ListNotations.

Definition regPtr := Z.

Inductive BinOpT : Type :=
| BAdd
| BMult.

Inductive Instruction : Type :=
  | Lab      : regPtr -> regPtr -> Instruction
  | MLab     : regPtr -> regPtr -> Instruction
  | PcLab    : regPtr -> Instruction
  | BCall    : regPtr -> regPtr -> regPtr -> Instruction
  | BRet     : Instruction
  | FlowsTo  : regPtr -> regPtr -> regPtr -> Instruction
  | LJoin    : regPtr -> regPtr -> regPtr -> Instruction
  | PutBot   : regPtr -> Instruction
  | Nop      : Instruction
  | Put (n : Z) : regPtr -> Instruction
  | BinOp (o : BinOpT) : regPtr -> regPtr -> regPtr -> Instruction
  | Jump     : regPtr -> Instruction
  | BNZ (n : Z) : regPtr -> Instruction
  | Load     : regPtr -> regPtr -> Instruction
  | Store    : regPtr -> regPtr -> Instruction
  | Alloc    : regPtr -> regPtr -> regPtr -> Instruction
  | PSetOff  : regPtr -> regPtr -> regPtr -> Instruction
  | Output   : regPtr -> Instruction
  | Halt     : Instruction
  | PGetOff  : regPtr -> regPtr -> Instruction
  | MSize    : regPtr -> regPtr -> Instruction.

Inductive OpCode : Type :=
  | OpLab
  | OpMLab
  | OpPcLab
  | OpBCall
  | OpBRet
  | OpFlowsTo
  | OpLJoin
  | OpPutBot
  | OpNop
  | OpPut
  | OpBinOp
  | OpJump
  | OpBNZ
  | OpLoad
  | OpStore
  | OpAlloc
  | OpPSetOff
  | OpOutput
  | OpPGetOff
  | OpMSize.

Definition opCodes :=
  [ OpLab
  ; OpMLab
  ; OpPcLab
  ; OpBCall
  ; OpBRet
  ; OpFlowsTo
  ; OpLJoin
  ; OpPutBot
  ; OpNop
  ; OpPut
  ; OpBinOp
  ; OpJump
  ; OpBNZ
  ; OpLoad
  ; OpStore
  ; OpAlloc
  ; OpPSetOff
  ; OpOutput
  ; OpPGetOff
  ; OpMSize ].

Lemma opCodes_correct : forall o : OpCode, In o opCodes.
Proof. intro o; simpl; destruct o; tauto. Qed.

Definition opCode_eq_dec : forall o1 o2 : OpCode,
  {o1 = o2} + {o1 <> o2}.
Proof. decide equality. Defined.

Definition opcode_of_instr (i : Instruction) : option OpCode :=
  match i with
  | Lab _ _       => Some OpLab
  | MLab _ _      => Some OpMLab
  | PcLab _       => Some OpPcLab
  | BCall _ _ _   => Some OpBCall
  | BRet          => Some OpBRet
  | FlowsTo _ _ _ => Some OpFlowsTo
  | LJoin _ _ _   => Some OpLJoin
  | PutBot _      => Some OpPutBot
  | Nop           => Some OpNop
  | Put _ _       => Some OpPut
  | BinOp _ _ _ _ => Some OpBinOp
  | Jump _        => Some OpJump
  | BNZ _ _       => Some OpBNZ
  | Load _ _      => Some OpLoad
  | Store _ _     => Some OpStore
  | Alloc _ _ _   => Some OpAlloc
  | PSetOff _ _ _ => Some OpPSetOff
  | Output _      => Some OpOutput
  | PGetOff _ _   => Some OpPGetOff
  | MSize _ _     => Some OpMSize
  | _             => None (* CH: halt has no opcode? why? *)
end.
