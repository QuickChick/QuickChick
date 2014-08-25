(* Machine instructions *)

Require Import ZArith.
Require Import List. Import ListNotations.

Definition regId := Z.

Inductive BinOpT : Type :=
| BAdd
| BMult
| BJoin
| BFlowsTo.

Section Instr.

Context {Label : Type}.

Inductive Instr : Type :=
  (* basic instructions *)
  | Put (n : Z) : regId -> Instr
  | Mov      : regId -> regId -> Instr
  | Load     : regId -> regId -> Instr
  | Store    : regId -> regId -> Instr
  | Write    : regId -> regId -> Instr
  | BinOp (o : BinOpT) : regId -> regId -> regId -> Instr
  | Nop      : Instr
  | Halt     : Instr
  | Jump     : regId -> Instr
  | BNZ (n : Z) : regId -> Instr
  | BCall    : regId -> regId -> regId -> Instr
  | BRet     : Instr

  (* public first-class labels *)
  | Lab      : regId -> regId -> Instr
  | PcLab    : regId -> Instr
  | PutLab   : Label -> regId -> Instr

  (* dynamic memory allocation *)
  | Alloc    : regId -> regId -> regId -> Instr
  | PGetOff  : regId -> regId -> Instr
  | PSetOff  : regId -> regId -> regId -> Instr
  | MSize    : regId -> regId -> Instr
  | MLab     : regId -> regId -> Instr.

Inductive OpCode : Type :=
  | OpPut
  | OpMov
  | OpLoad
  | OpStore
  | OpWrite
  | OpBinOp
  | OpNop
  | OpJump
  | OpBNZ
  | OpBCall
  | OpBRet
(* missing for Halt *)
  | OpLab
  | OpPcLab
  | OpPutLab
  | OpAlloc
  | OpPGetOff
  | OpPSetOff
  | OpMSize
  | OpMLab.

Definition opCodes :=
  [ OpPut
  ; OpMov
  ; OpLoad
  ; OpStore
  ; OpWrite
  ; OpBinOp
  ; OpNop
  ; OpJump
  ; OpBNZ
  ; OpBCall
  ; OpBRet
  ; OpLab
  ; OpPcLab
  ; OpPutLab
  ; OpAlloc
  ; OpPGetOff
  ; OpPSetOff
  ; OpMSize
  ; OpMLab ].

Lemma opCodes_correct : forall o : OpCode, In o opCodes.
Proof. intro o; simpl; destruct o; tauto. Qed.

Definition opCode_eq_dec : forall o1 o2 : OpCode,
  {o1 = o2} + {o1 <> o2}.
Proof. decide equality. Defined.

Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
  | Put _ _       => Some OpPut
  | Mov _ _       => Some OpMov
  | Load _ _      => Some OpLoad
  | Store _ _     => Some OpStore
  | Write _ _     => Some OpWrite
  | BinOp _ _ _ _ => Some OpBinOp
  | Nop           => Some OpNop
  | Halt          => None (* CH: halt has no opcode? why? *)
  | Jump _        => Some OpJump
  | BNZ _ _       => Some OpBNZ
  | BCall _ _ _   => Some OpBCall
  | BRet          => Some OpBRet

  | Lab _ _       => Some OpLab
  | PcLab _       => Some OpPcLab
  | PutLab _ _    => Some OpPutLab

  | Alloc _ _ _   => Some OpAlloc
  | PGetOff _ _   => Some OpPGetOff
  | PSetOff _ _ _ => Some OpPSetOff
  | MSize _ _     => Some OpMSize
  | MLab _ _      => Some OpMLab
end.

End Instr.
