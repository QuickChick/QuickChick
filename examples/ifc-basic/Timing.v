From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.

From QuickChick.ifcbasic Require Import Machine Printing Generation Indist DerivedGen.
From QuickChick.ifcbasic Require GenExec.

Require Import Coq.Strings.String.
Local Open Scope string.

Definition SSNI_manual (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  if indist st1 st2 then
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            checker (indist st1' st2')
          | _, _ => checker rejected
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              checker (indist st1' st2') 
            else if is_atom_low (st_pc st1') then
              (checker (indist st2 st2'))
            else
              (checker (indist st1 st1'))
          | _, _ => checker rejected
        end
      | H,_ =>
        match exec t st1 with
          | Some st1' =>
            checker (indist st1 st1')
          | _ => checker rejected
        end
      | _,H =>
        match exec t st2 with
          | Some st2' =>
            checker  (indist st2 st2')
          | _ => checker rejected
        end
    end
  else checker rejected.

Instance CheckableOptBool : Checkable (option bool) :=
  { checker x :=
      match x with
      | Some true  => checker true
      | Some false => checker false
      | None => checker rejected
      end }.

Definition SSNI_derived (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  match @decOpt (IndistState st1 st2) _ 5 with
  | Some true =>
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
        | Some st1', Some st2' =>
(*          whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                                       ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl)*)
            (checker (@decOpt (IndistState st1' st2') _ 5))
          | _, _ => checker rejected
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
            whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl) 
              
            (checker (@decOpt (IndistState st1' st2') _ 5))
            else if is_atom_low (st_pc st1') then
                   whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )
                   
                   (checker (@decOpt (IndistState st2 st2') _ 5))
                 else
                    whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )
            (checker (@decOpt (IndistState st1 st1') _ 5))
          | _, _ => checker rejected
        end
      | H,_ =>
        match exec t st1 with
        | Some st1' =>
          whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )
          
            (checker (@decOpt (IndistState st1 st1') _ 5))
          | _ => checker rejected
        end
      | _,H =>
        match exec t st2 with
        | Some st2' =>
          whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )
          
            (checker (@decOpt (IndistState st2 st2') _ 5))
          | _ => checker rejected
        end
    end
  | _ => checker rejected
  end.

Axiom withTime : Checker -> Checker.
Extract Constant withTime =>
  "(fun c -> Printf.printf ""%.8f\n"" (Sys.time ()); c)".

Definition prop_manual : Checker :=
  forAllShrink gen_variation_state (fun _ => nil)
               (fun v => SSNI_manual default_table v).

Definition prop_derived : Checker :=
  forAllShrink gen_variation_state (fun _ => nil)
               (fun v => SSNI_derived default_table v).

Extract Constant defNumTests => "20000".
QuickChick prop_manual.
QuickChick prop_derived.
(*
Definition prop_test : Checker :=
  forAllShrink gen_variation_state (fun _ => nil)
               (fun v =>
                  let r0 := trace ("Next" ++ nl) (checker true) in
                  let r2 := withTime (SSNI_derived default_table v) in
                  let r1 := withTime (SSNI_manual default_table v) in
                  withTime (conjoin [r0;r2;r1])).

QuickChick prop_test.
*)
