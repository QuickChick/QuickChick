Require Import QuickChick.

Require Import Machine.

Require Import ZArith.
Require Import List.

Require Import TestingCommon.
Require Import Indist.
Require Import Generation.
Require Import Shrinking.
Require Import Printing.

(* Leverage the pair/V functions and making everything observable,
   create (inefficient) instances for a single machine *)

(* Generates an SSNI-oriented single machine state *)
Definition genState {Gen : Type -> Type} `{GenMonad Gen} : Gen State :=
  bindGen gen_variation_state (fun v =>
  let '(Var _ st _) := v in
  returnGen st).

Instance arbState : Arbitrary State :=
{|
  arbitrary := @genState ;
  shrink x :=
    let all := shrinkVState (Var top x x) in
    let state_of_var v := let '(Var _ x _) := v in x in
    filter (indist top x) (map state_of_var all)
|}.

Instance showState : Show State :=
{|
  show x := show_pair top x x
|}.
