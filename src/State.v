Set Implicit Arguments.

Require Import RandomQC.
Require Import Coq.Strings.String.

Require Import StringOT.
Require Import FSets.FMapAVL.

Module Map := FMapAVL.Make(StringOT).

Require Import ZArith.

Record State := MkState
  { maxSuccessTests   : nat
  ; maxDiscardedTests : nat
  ; maxShrinkNo       : nat
  ; computeSize       : nat -> nat -> nat

  ; numSuccessTests   : nat
  ; numDiscardedTests : nat

  ; labels            : Map.t nat

  ; expectedFailure   : bool
  ; randomSeed        : RandomSeed

  ; numSuccessShrinks : nat
  ; numTryShrinks     : nat
  ; stDoAnalysis      : bool

  ; start_time : Z                          
  }.

Definition updTryShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts ana stime =>
      MkState mst mdt ms cs nst ndt ls e r nss (f nts) ana stime
  end.

Definition updSuccessShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts ana stime =>
      MkState mst mdt ms cs nst ndt ls e r (f nss) nts ana stime
  end.

Definition updSuccTests st f :=
  match st with
    | MkState mst mdt ms cs nst     ndt ls e r nss nts ana stime =>
      MkState mst mdt ms cs (f nst) ndt ls e r nss nts ana stime
  end.

Definition updDiscTests st f :=
  match st with
    | MkState mst mdt ms cs nst ndt     ls e r nss nts ana stime =>
      MkState mst mdt ms cs nst (f ndt) ls e r nss nts ana stime
  end.
