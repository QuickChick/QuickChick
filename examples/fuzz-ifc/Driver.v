From QuickChick Require Import QuickChick.
Import GenLow GenHigh.

Require Import List. Import ListNotations.

From QuickChick.ifcbasic Require Import Machine Printing Generation Indist DerivedGen Rules.
From QuickChick.ifcbasic Require GenExec.

Require Import Coq.Strings.String.
Local Open Scope string.

From QuickChick Require Import Mutate MutateCheck.
Require Import ZArith.

(*
Definition prop_sanity :=
  forAll Generation.gen_variation_state (fun v =>
  let '(V s s') := v in                                      
  whenFail (show_pair s s') (indist s s')).
QuickChick prop_sanity.
 *)

Record exp_result := MkExpResult { exp_success : Checker
                                 ; exp_fail    : Checker
                                 ; exp_reject  : Checker
                                 ; exp_check   : bool -> Checker
                                 }.

(* HACK: To get statistics on successful runs/discards/avg test failures, we can 
   assume everything succeeds and collect the result. *)
Definition exp_result_random : exp_result :=
  {| exp_success := collect true  true
   ; exp_fail    := collect false true
   ; exp_reject  := collect "()"  true
   ; exp_check   := (fun b => collect b true)
  |}.

(* For fuzzing, we let afl-fuzz gather the statistics (and hack afl-fuzz instead :) *)
Definition exp_result_fuzz : exp_result :=
  {| exp_success := collect true  true
   ; exp_fail    := collect false false
   ; exp_reject  := collect "()"  tt
   ; exp_check   := (fun b => collect b b)
  |}.

Definition registerSeedCallback {prop : Type} `{Checkable prop} : prop -> Checker :=
  callback (PostTest NotCounterexample (fun _st r rs =>
              let '(MkSmallResult _ _ _ _ ss _) := rs in
              if ss = ["true"] ? then registerSeed r else 0)).

Definition SSNI (t : table) (v : @Variation State) (res : exp_result) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match lookupInstr st1 with
  | Some i => 
    if indist st1 st2 then
      match l1, l2 with
        | L,L  =>
          match exec t st1, exec t st2 with
            | Some st1', Some st2' =>
              exp_check res (indist st1' st2')
            | _, _ => collect "Not both step" (exp_reject res)
          end
        | H, H =>
          match exec t st1, exec t st2 with
            | Some st1', Some st2' =>
              if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
                exp_check res (indist st1' st2')
              else if is_atom_low (st_pc st1') then
                exp_check res (indist st2 st2')
              else
                exp_check res (indist st1 st1')
            | _, _ => collect "Both don't step H" (exp_reject res)
          end
        | H,_ =>
          match exec t st1 with
            | Some st1' =>
              exp_check res (indist st1 st1')
            | _ => collect ("High 1 doesn't step") (exp_reject res)
          end
        | _,H =>
          match exec t st2 with
            | Some st2' =>
              exp_check res (indist st2 st2')
            | _ => collect "High 2 doesn't step" (exp_reject res)
          end
      end
    else collect "Not indist" (exp_reject res)
  | _ => collect "Out-of-range" (exp_reject res)
  end.


Fixpoint MSNI_aux (fuel : nat) (t : table) (v : @Variation State) : option bool :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match fuel with
  | O => Some true
  | S fuel' => 
  match lookupInstr st1 with
  | Some i => 
    if indist st1 st2 then
      match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
        | Some st1', Some st2' =>
          if indist st1' st2' then
            MSNI_aux fuel' t (V st1' st2')
          else
            Some false
        | _, _ => Some true
        end
      | H, H =>
        match exec t st1, exec t st2 with
        | Some st1', Some st2' =>
          if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
            if indist st1' st2' then
              MSNI_aux fuel' t (V st1' st2')
            else
              Some false
          else if is_atom_low (st_pc st1') then
                 if indist st2 st2' then
                   (* Ensure still a variation by not executing st1 *)
                   MSNI_aux fuel' t (V st1 st2') 
                 else Some false
          else if is_atom_low (st_pc st2') then 
                 if indist st1 st1' then
                   MSNI_aux fuel' t (V st1' st2)
                 else Some false
          else (* Both high, check pairwise, continue *)
            if indist st1 st1' && indist st2 st2' then
              MSNI_aux fuel' t (V st1' st2')
            else Some false
        | _, _ => Some true
        end
      | H,_ =>
        match exec t st1 with
        | Some st1' =>
          if indist st1 st1' then
            MSNI_aux fuel' t (V st1' st2)
          else
            Some false
        | _ => Some true
        end
      | _,H =>
        match exec t st2 with
        | Some st2' =>
          if indist st2 st2' then
            MSNI_aux fuel' t (V st1 st2')
          else Some false
        | _ => Some true
        end
      end
    else None
  | _ => Some true
  end
  end.

Definition isLow (st : State) :=
  label_eq ∂(st_pc st) L.

(* EENI *)
Fixpoint EENI (fuel : nat) (t : table) (v : @Variation State) res : Checker  :=
  let '(V st1 st2) := v in
  let st1' := execN t fuel st1 in
  let st2' := execN t fuel st2 in
  if indist st1 st2 then 
    match lookupInstr st1', lookupInstr st2' with
    (* run to completion *)
    | Some Halt, Some Halt =>
      if isLow st1' && isLow st2' then
        exp_check res (indist st1' st2') 
      else (exp_reject res)
    | _, _ => (exp_reject res)
    end
  else (exp_reject res).

(* Generic property *)
Definition prop p (gen : G (option Variation)) (t : table) (r : exp_result) : Checker :=
  forAllShrink gen (fun _ => nil)
               (fun mv =>
                  match mv with
                  | Some v => p t v r
                  | _ => exp_reject r
                  end).

(* Some more gen stuff *)

Definition gen_variation_naive : G (option Variation) :=
  bindGen GenExec.gen_state' (fun st1 =>
  bindGen GenExec.gen_state' (fun st2 =>
  if indist st1 st2 then
    returnGen (Some (V st1 st2))
  else
    returnGen None)).

Definition gen_variation_medium : G (option Variation) :=
  bindGen GenExec.gen_state' (fun st1 =>
  bindGen (Generation.vary st1) (fun st2 =>
  if indist st1 st2 then
    returnGen (Some (V st1 st2))
  else
    returnGen None)).

Definition testMutantX prop r n :=
  match nth (mutate_table default_table) n with
    | Some t => prop t r
    | _ => exp_reject r
  end.

Definition prop_SSNI_naive t r :=
  prop SSNI gen_variation_naive t r.

Definition prop_SSNI_medium t r :=
  prop SSNI gen_variation_medium t r.

Definition prop_SSNI_smart t r :=
  registerSeedCallback (prop SSNI (liftGen Some gen_variation_state) t r).

Definition ieq (i1 i2 : Instruction) : {i1 = i2} + {i1 <> i2}.
repeat decide equality.
Defined.

Derive Show for OpCode.

Definition count_instrs i im :=
  List.count_occ opCode_eq_dec im i.

Fixpoint collect_instrs_imem (im : list Instruction) x :=
  let ops := List.map opcode_of_instr im in 
  let cnts := List.map (fun oc : OpCode => (oc, count_instrs oc ops)) opCodes in
  collect (cnts) x.

Definition collect_instrs v x :=
  let '(V (St i _ _ _) _) := v in
  collect_instrs_imem i x.

(* QuickChick (prop_SSNI_smart default_table exp_result_random). *)
Definition MSNI fuel t v res :=
(*  collect_instrs v *) (
  match MSNI_aux fuel t v with
  | Some b => exp_check res b
  | None => exp_reject res
  end).

Definition prop_MSNI_naive t r :=
  prop (MSNI 42) (gen_variation_naive) t r.

Definition prop_MSNI_medium t r :=
  prop (MSNI 42) (gen_variation_medium) t r.

Definition prop_MSNI_smart t r :=
  prop (MSNI 42) (liftGen Some GenExec.gen_variation_state') t r.

(*
QuickChick (prop_MSNI_smart default_table exp_result_random).
QuickCheck (testMutantX prop_MSNI_smart exp_result_random 9).
*)

Definition prop_EENI_naive t r : Checker :=
  prop (EENI 42) (gen_variation_naive) t r.

Definition prop_EENI_medium t r : Checker :=
  prop (EENI 42) (gen_variation_medium) t r.

Definition prop_EENI_smart t r : Checker :=
  prop (EENI 42) (liftGen Some GenExec.gen_variation_state') t r.

Eval lazy -[labelCount helper] in
  nth (mutate_table default_table) 1.

Extract Constant defNumTests => "10".

QuickChick (testMutantX prop_SSNI_smart exp_result_random 0).
FuzzChick (testMutantX prop_SSNI_smart exp_result_fuzz 0).

(*
QuickChick (testMutantX prop_MSNI_smart exp_result_random 1).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 2).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 3).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 4).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 5).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 6).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 7).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 8).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 9).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 10).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 11).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 12).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 13).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 14).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 15).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 16).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 17).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 18).
QuickChick (testMutantX prop_MSNI_smart exp_result_random 19).
*)