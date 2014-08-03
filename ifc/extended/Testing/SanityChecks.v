Require Import QuickChick.

Require Import Reachability.
Require Import Printing.
Require Import SingleStateArb.
Require Import Indist.  
Require Import Shrinking.
Require Import Generation.

Require Import Machine.
Import Mem.

Require Import List.
Require Import Common.
Require Import String.

Local Open Scope string.
(* Sanity check for stamp generation *)

Definition Property := Property Gen.Gen. 

Definition prop_stamp_generation (st : State) :=
  whenFail (show st) (well_formed st).

(*
Definition propStampGeneration (st : State) := 
  let stamps := generateStamps st in
  whenFail (Property.trace ("Generated: " ++ nl ++ 
                           (showStamps (allocated (st_mem st)) stamps)))
           (wellFormed st stamps).
*)

Definition prop_exec_preserves_well_formed (t : table) 
: Property :=
  forAllShrink show arbitrary (fun _ => []) (fun st =>
  if well_formed st then
    match exec t st with
    | Some (_, st') =>
      whenFail ("Initial: " ++ show st ++ nl ++
                "Step to: " ++ show st' ++ nl)
               (well_formed st')
    | _ => property rejected
    end
  else property false).
  
Definition prop_generate_indist
: Property :=
  forAllShrink show gen_variation_state (fun _ => []) (* shrinkVState *)
               (fun v => let '(Var lab st1 st2) := v in
                property (indist lab st1 st2)).
