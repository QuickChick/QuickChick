Require Import ZArith List.

Require Export Lattices.
Require Export Instructions.
Require Import Rules.

Context{T : Type}.
Context{Latt : JoinSemiLattice T}.

Definition none := bot.

Record MVec := MkMVec {
  mop : OpCode;
  ml1 : T;
  ml2 : T;
  ml3 : T;
  mpc : T
}.

Record RVec := MkRVec {
  rlab : T;
  rpc  : T
}.

Inductive table : MVec -> RVec -> Prop :=
| TLab : forall pc l1 l2 l3,
  table (MkMVec OpLab l1 l2 l3 pc) (MkRVec bot pc)
| TMLab : forall pc l1 l2 l3,
  table (MkMVec OpMLab l1 l2 l3 pc) (MkRVec l1 pc)
| TPcLab : forall pc l1 l2 l3,
  table (MkMVec OpPcLab l1 l2 l3 pc) (MkRVec bot pc)
| TBCall : forall pc l1 l2 l3,
  table (MkMVec OpBCall l1 l2 l3 pc) (MkRVec (join l2 pc) (join l1 pc))
| TBRet : forall pc l1 l2 l3,
  flows (join l1 pc) (join l2 l3) = true ->
  table (MkMVec OpBRet l1 l2 l3 pc) (MkRVec l2 l3)
| TFlowsTo : forall pc l1 l2 l3,
  table (MkMVec OpFlowsTo l1 l2 l3 pc) (MkRVec (join l1 l2) pc)
| TLJoin : forall pc l1 l2 l3,
  table (MkMVec OpLJoin l1 l2 l3 pc) (MkRVec (join l1 l2) pc)
| TPutBot : forall pc l1 l2 l3,
  table (MkMVec OpPutBot l1 l2 l3 pc) (MkRVec bot pc)
| TNop : forall pc l1 l2 l3,
  table (MkMVec OpNop l1 l2 l3 pc) (MkRVec none pc)
| TPut : forall pc l1 l2 l3,
  table (MkMVec OpPut l1 l2 l3 pc) (MkRVec bot pc)
| TBinOp : forall pc l1 l2 l3,
  table (MkMVec OpBinOp l1 l2 l3 pc) (MkRVec (join l1 l2) pc)
| TJump : forall pc l1 l2 l3,
  table (MkMVec OpJump l1 l2 l3 pc) (MkRVec none (join pc l1))
| TBNZ : forall pc l1 l2 l3,
  table (MkMVec OpBNZ l1 l2 l3 pc) (MkRVec none (join pc l1))
| TLoad : forall pc l1 l2 l3,
  table (MkMVec OpLoad l1 l2 l3 pc) (MkRVec l3 (join pc (join l1 l2)))
| TStore : forall pc l1 l2 l3,
  flows (join l1 pc) l2 = true ->
  table (MkMVec OpStore l1 l2 l3 pc) (MkRVec l3 pc)
| TAlloc : forall pc l1 l2 l3,
  table (MkMVec OpAlloc l1 l2 l3 pc) (MkRVec (join l1 l2) pc)
| TPSetOff : forall pc l1 l2 l3,
  table (MkMVec OpPSetOff l1 l2 l3 pc) (MkRVec (join l1 l2) pc)
| TPGetOff : forall pc l1 l2 l3,
  table (MkMVec OpPGetOff l1 l2 l3 pc) (MkRVec l1 pc)
| TMSize : forall pc l1 l2 l3,
  table (MkMVec OpMSize l1 l2 l3 pc) (MkRVec l2 (join pc l1))
| TOutput : forall pc l1 l2 l3,
  table (MkMVec OpOutput l1 l2 l3 pc) (MkRVec (join l1 pc) pc)
.

Declare ML Module "relation_extraction_plugin".

Extraction Relation table [1].

(* This produces:
let rec table1 p1 =
  match p1 with
  | MkMVec (OpLab, l1, l2, l3, pc) -> MkRVec (bot, pc)
  | MkMVec (OpMLab, l1, l2, l3, pc) -> MkRVec (l1, pc)
  | MkMVec (OpPcLab, l1, l2, l3, pc) -> MkRVec (bot, pc)
  | MkMVec (OpBCall, l1, l2, l3, pc) -> MkRVec ((join l2 pc), (join l1 pc))
  | MkMVec (OpBRet, l1, l2, l3, pc) ->
    (match flows (join l1 pc) (join l2 l3) with
     | true -> MkRVec (l2, l3)
     | _ -> assert false (*  *))
  | MkMVec (OpFlowsTo, l1, l2, l3, pc) -> MkRVec ((join l1 l2), pc)
  | MkMVec (OpLJoin, l1, l2, l3, pc) -> MkRVec ((join l1 l2), pc)
  | MkMVec (OpPutBot, l1, l2, l3, pc) -> MkRVec (bot, pc)
  | MkMVec (OpNop, l1, l2, l3, pc) -> MkRVec (none, pc)
  | MkMVec (OpPut, l1, l2, l3, pc) -> MkRVec (bot, pc)
  | MkMVec (OpBinOp, l1, l2, l3, pc) -> MkRVec ((join l1 l2), pc)
  | MkMVec (OpJump, l1, l2, l3, pc) -> MkRVec (none, (join pc l1))
  | MkMVec (OpBNZ, l1, l2, l3, pc) -> MkRVec (none, (join pc l1))
  | MkMVec (OpLoad, l1, l2, l3, pc) -> MkRVec (l3, (join pc (join l1 l2)))
  | MkMVec (OpStore, l1, l2, l3, pc) ->
    (match flows (join l1 pc) l2 with
     | true -> MkRVec (l3, pc)
     | _ -> assert false (*  *))
  | MkMVec (OpAlloc, l1, l2, l3, pc) -> MkRVec ((join l1 l2), pc)
  | MkMVec (OpPSetOff, l1, l2, l3, pc) -> MkRVec ((join l1 l2), pc)
  | MkMVec (OpPGetOff, l1, l2, l3, pc) -> MkRVec (l1, pc)
  | MkMVec (OpMSize, l1, l2, l3, pc) -> MkRVec (l2, (join pc l1))
  | MkMVec (OpOutput, l1, l2, l3, pc) -> MkRVec ((join l1 pc), pc)
  | _ -> assert false (*  *)
*)
