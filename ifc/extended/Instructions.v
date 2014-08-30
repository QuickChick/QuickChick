(* Machine instructions *)

Require Import ZArith.
Require Import List. Import ListNotations.

Definition regId := Z.

Inductive BinOpT : Type :=
| BAdd
| BMult
| BJoin
| BFlowsTo
| BEq.

Scheme Equality for BinOpT.

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

Require Import ssreflect ssrbool eqtype.
Require Import Utils.

Lemma BinOpT_beqP : Equality.axiom BinOpT_beq.
Proof. admit. Qed.

Definition BinOpT_eqMixin := EqMixin BinOpT_beqP.
Canonical BinOpT_eqType := Eval hnf in EqType _ BinOpT_eqMixin.

Definition instr_eqb (T : eqType) (i1 i2 : @Instr T) : bool :=
  match i1, i2 with
  | Put n1 r1, Put n2 r2 => [&& n1 == n2 & r1 == r2]
  | Mov r11 r12, Mov r21 r22 => [&& r11 == r21 & r12 == r22]
  | Load r11 r12, Load r21 r22 => [&& r11 == r21 & r12 == r22]
  | Store r11 r12, Store r21 r22 => [&& r11 == r21 & r12 == r22]
  | Write r11 r12, Write r21 r22 => [&& r11 == r21 & r12 == r22]
  | BinOp o1 r11 r12 r13, BinOp o2 r21 r22 r23 => [&& o1 == o2, r11 == r21, r12 == r22 & r13 == r23]
  | Nop, Nop => true
  | Halt, Halt => true
  | Jump r1, Jump r2 => r1 == r2
  | BNZ o1 r1, BNZ o2 r2 => [&& o1 == o2 & r1 == r2]
  | BCall r11 r12 r13, BCall r21 r22 r23 => [&& r11 == r21, r12 == r22 & r13 == r23]
  | BRet, BRet => true
  | Lab r11 r12, Lab r21 r22 => [&& r11 == r21 & r12 == r22]
  | PcLab r1, PcLab r2 => r1 == r2
  | PutLab l1 r1, PutLab l2 r2 => [&& l1 == l2 & r1 == r2]
  | Alloc r11 r12 r13, Alloc r21 r22 r23 => [&& r11 == r21, r12 == r22 & r13 == r23]
  | PGetOff r11 r12, PGetOff r21 r22 => [&& r11 == r21 & r12 == r22]
  | PSetOff r11 r12 r13, PSetOff r21 r22 r23 => [&& r11 == r21, r12 == r22 & r13 == r23]
  | MSize r11 r12, MSize r21 r22 => [&& r11 == r21 & r12 == r22]
  | MLab r11 r12, MLab r21 r22 => [&& r11 == r21 & r12 == r22]
  | _, _ => false
  end.

Lemma instr_eqbP T : Equality.axiom (instr_eqb T).
Proof. admit. Qed.

Definition instr_eqMixin T := EqMixin (instr_eqbP T).
Canonical instr_eqType T := Eval hnf in EqType _ (instr_eqMixin T).
