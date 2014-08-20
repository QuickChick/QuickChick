(* Machine instructions *)

Require Import ZArith.
Require Import List. Import ListNotations.

Definition regId := Z.

Inductive BinOpT : Type :=
| BAdd
| BMult.

Definition eval_binop (b : BinOpT) : Z -> Z -> option Z :=
  match b with
    | BAdd => fun z1 z2 => Some (z1 + z2)%Z
    | BMult => fun z1 z2 => Some (z1 * z2)%Z
  end.

Section Instr.

Context {Label : Type}.

Inductive Instr : Type :=
  | Lab      : regId -> regId -> Instr
  | MLab     : regId -> regId -> Instr
  | PcLab    : regId -> Instr
  | BCall    : regId -> regId -> regId -> Instr
  | BRet     : Instr
  | FlowsTo  : regId -> regId -> regId -> Instr
  | LJoin    : regId -> regId -> regId -> Instr
  | PutLab   : Label -> regId -> Instr
  | Nop      : Instr
  | Put (n : Z) : regId -> Instr
  | BinOp (o : BinOpT) : regId -> regId -> regId -> Instr
  | Jump     : regId -> Instr
  | BNZ (n : Z) : regId -> Instr
  | Load     : regId -> regId -> Instr
  | Store    : regId -> regId -> Instr
  | Alloc    : regId -> regId -> regId -> Instr
  | PSetOff  : regId -> regId -> regId -> Instr
  | Output   : regId -> Instr
  | Halt     : Instr
  | PGetOff  : regId -> regId -> Instr
  | MSize    : regId -> regId -> Instr.

Inductive OpCode : Type :=
  | OpLab
  | OpMLab
  | OpPcLab
  | OpBCall
  | OpBRet
  | OpFlowsTo
  | OpLJoin
  | OpPutLab
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
  ; OpPutLab
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

Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
  | Lab _ _       => Some OpLab
  | MLab _ _      => Some OpMLab
  | PcLab _       => Some OpPcLab
  | BCall _ _ _   => Some OpBCall
  | BRet          => Some OpBRet
  | FlowsTo _ _ _ => Some OpFlowsTo
  | LJoin _ _ _   => Some OpLJoin
  | PutLab _ _    => Some OpPutLab
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
  | Halt          => None (* CH: halt has no opcode? why? *)
end.

End Instr.
