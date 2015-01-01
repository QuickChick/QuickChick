Set Implicit Arguments.

Require Import ModuleGen.
Require Import Axioms.
Require Import String.

Record State := MkState
  { maxSuccessTests   : nat
  ; maxDiscardedTests : nat
  ; maxShrinkNo       : nat
  ; computeSize       : nat -> nat -> nat

  ; numSuccessTests   : nat
  ; numDiscardedTests : nat
  ; collected         : list (list (string * nat))
  ; expectedFailure   : bool
  ; randomSeed        : RandomGen

  ; numSuccessShrinks : nat
  ; numTryShrinks     : nat
  }.

Definition updTryShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt c e r nss nts =>
      MkState mst mdt ms cs nst ndt c e r nss (f nts)
  end.

Definition updSuccessShrinks (st : State) (f : nat -> nat) : State :=
  match st with
    | MkState mst mdt ms cs nst ndt c e r nss nts =>
      MkState mst mdt ms cs nst ndt c e r (f nss) nts
  end.