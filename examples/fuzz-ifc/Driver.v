From QuickChick Require Import QuickChick.
Import GenLow GenHigh.

Require Import List. Import ListNotations.

From QuickChick.ifcbasic Require Import Machine Printing Generation Indist DerivedGen Rules.
From QuickChick.ifcbasic Require GenExec.

Require Import Coq.Strings.String.
Local Open Scope string.

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
            | _, _ => exp_reject res
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
            | _, _ => exp_reject res
          end
        | H,_ =>
          match exec t st1 with
            | Some st1' =>
              exp_check res (indist st1 st1')
            | _ => exp_reject res
          end
        | _,H =>
          match exec t st2 with
            | Some st2' =>
              exp_check res (indist st2 st2')
            | _ => exp_reject res
          end
      end
    else exp_reject res
  | _ => exp_reject res
  end.

Definition gen__MaybeGen {A} (g : G A) : G (option A) :=
  liftGen Some g.

Definition prop_SSNI (gen : G (option Variation)) (t : table) (r : exp_result) : Checker :=
  forAllShrink gen (fun _ => nil)
               (fun mv =>
                  match mv with
                  | Some v => SSNI t v r
                  | _ => exp_reject r
                  end).

Definition gen_variation_naive : G (option Variation) :=
  bindGen GenExec.gen_state' (fun st1 =>
  bindGen GenExec.gen_state' (fun st2 =>
  if indist st1 st2 then
    returnGen (Some (V st1 st2))
  else
    returnGen None)).

Extract Constant defNumTests => "100000".

Definition prop_SSNI_naive t r :=
  prop_SSNI gen_variation_naive t r.

Definition prop_SSNI_smart t r :=
  prop_SSNI (liftGen Some gen_variation_state) t r.


Extract Constant defNumDiscards => "30000".

From QuickChick Require Import Mutate MutateCheck.
Require Import ZArith.

Definition testMutantX prop r n :=
  match nth (mutate_table default_table) n with
    | Some t => prop t r
    | _ => exp_reject r
  end.

(* QuickChick (prop_SSNI_smart default_table exp_result_random). *)

Fixpoint MSNI (fuel : nat) (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match fuel with
  | O => checker true
  | S fuel' => 
  match lookupInstr st1 with
    | Some i =>     (* collect (show i)*) (  
  if indist st1 st2 then
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            whenFail ("LL" ++ nl ++ "Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++ nl ++ show st1' ++ nl ++ show st2' ++ nl)
            (* collect ("L -> L")*)
            (if indist st1' st2' then
              MSNI fuel' t (V st1' st2')
            else
              checker false)
          | _, _ => (* collect "L,L,FAIL" true *) checker true
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl) 
              (* collect ("H -> L")*)
              (if indist st1' st2' then
                MSNI fuel' t (V st1' st2')
              else
                checker false)
            else if is_atom_low (st_pc st1') then
                   (* whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
                   (* collect ("H -> H")*)
              if indist st2 st2' then
                (* Ensure still a variation by not executing st1 *)
                MSNI fuel' t (V st1 st2') 
              else checker false
            else
              if indist st1 st1' then
                MSNI fuel' t (V st1' st2)
              else 
                           whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )
                           (checker false)
              (* collect ("H -> H")*) 
          | _, _ => checker true
        end
      | H,_ =>
        match exec t st1 with
        | Some st1' =>
          if indist st1 st1' then
            MSNI fuel' t (V st1' st2)
          else
            checker false
          | _ => (*collect "H,_,FAIL" true *) checker true
        end
      | _,H =>
        match exec t st2 with
        | Some st2' =>
          if indist st2 st2' then
            MSNI fuel' t (V st1 st2')
          else checker false
        | _ => (*collect "L,H,FAIL" true *) checker true
        end
    end
  else checker rejected
(*    whenFail ("Indist with states: " ++ nl ++ show_pair st1 st2 ++ nl ++ " after steps: " ++ show fuel ++ nl) (checker false) *)
    )         
    | _ => checker rejected
  end
  end.

Definition prop_MSNI t : Checker :=
  forAllShrink GenExec.gen_variation_state' (fun _ => nil)
   (MSNI 20 t : Variation -> G QProp).


Definition prop_MSNI_naive t : Checker :=
  forAllShrink gen_variation_naive (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some v => MSNI 20 t v
                  | _ => checker rejected 
                  end).

Definition testMutantX_ c n :=
  match nth (mutate_table default_table) n with
    | Some t => c t
    | _ => checker tt 
  end.

(* FuzzChick (prop_MSNI_naive default_table). *)
(* QuickCheck (prop_MSNI default_table). *)

(* 
QuickCheck (testMutantX_ prop_MSNI 9).
QuickCheck (testMutantX_ prop_MSNI_naive 9).

FuzzChick (testMutantX_ prop_MSNI_naive 9).
 *)

Definition isLow (st : State) :=
  label_eq ∂(st_pc st) L.

(* EENI *)
Fixpoint EENI (fuel : nat) (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let st1' := execN t fuel st1 in
  let st2' := execN t fuel st2 in
  if indist st1 st2 then 
    match lookupInstr st1', lookupInstr st2' with
    (* run to completion *)
    | Some Halt, Some Halt =>
      whenFail (show_pair st1' st2' ++ nl) 
               (if isLow st1' && isLow st2' then checker (indist st1' st2')
                else checker rejected)
    | _, _ => checker rejected
    end
  else checker rejected.    

Definition prop_EENI t : Checker :=
  forAllShrink GenExec.gen_variation_state' (fun _ => nil)
   (EENI 20 t : Variation -> G QProp).

(*
QuickChick (prop_EENI default_table). 
FuzzChick (prop_EENI default_table).
 *)
Definition gen_variation_less_naive : G (option Variation) :=
  bindGen GenExec.gen_state' (fun st1 =>
  bindGen (Generation.vary st1) (fun st2 =>
  if indist st1 st2 then
    returnGen (Some (V st1 st2))
  else
    returnGen None)).

Definition prop_EENI_g g t : Checker :=
  forAllShrink g (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some v => EENI 20 t v
                  | _ => checker rejected 
                  end).

FuzzChick (testMutantX_ (prop_EENI_g gen_variation_less_naive) 9).

  
(*
Definition prop_SSNI_derived t : Checker :=
  forAllShrink gen_variation_state_derived (fun _ => nil)
               (fun mv => 
                  match mv with 
                  | Some v => SSNI t v
                  | _ => checker tt
                  end).
*)

(*
Definition myArgs : Args :=
  let '(MkArgs rp mSuc md mSh mSz c) := stdArgs in
  MkArgs rp numTests md mSh mSz c.

From QuickChick Require Import Mutate MutateCheck.

Instance mutateable_table : Mutateable table :=
{|
  mutate := mutate_table
|}.

Require Import ZArith.




Definition testMutantX n :=
  match nth (mutate_table default_table) n with
    | Some t => prop_SSNI t
    | _ => checker tt 
  end.

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      gen_variation_state (fun _ => nil) (fun _ => "")
      (SSNI t ))).

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      GenExec.gen_variation_state' (fun _ => nil) (fun _ => "")
      (MSNI 20 t ))).

MutateCheckWith myArgs default_table
    (fun t => (forAllShrinkShow
      (gen_variation_state_derived) (fun _ => nil) (fun _ => "")
      (fun mv => 
         match mv with 
         | Some v => SSNI t v 
         | None => checker tt
         end
    ))).
*)

(*
Eval lazy -[labelCount helper] in
  nth (mutate_table default_table) 2. *)

(*
Definition st1 :=
  St [Store; Store] [0 @ L] (0 @ L :: 0 @ H :: Mty) (0 @ L).
Definition st2 :=
  St [Store; Store] [0 @ L] (0 @ L :: 1 @ H :: Mty) (0 @ L).
Definition ex_indist : indist st1 st2 = true. auto. Qed.

Definition st1' :=
  St [Add; Add] [0 @ L] (0 @ L :: 0 @ H :: Mty) (0 @ L).
Definition st2' :=
  St [Add; Add] [0 @ L] (0 @ L :: 1 @ H :: Mty) (0 @ L).
Definition ex_indist' : indist st1' st2' = true. auto. Qed.

Definition ex_test :=
  match nth (mutate_table default_table) 8 with
    | Some t => SSNI t (V st1' st2')
    | _ => checker tt
  end.

Eval compute in exec default_table st1'.
QuickCheck ex_test.
QuickCheck (testMutantX 18).
*)