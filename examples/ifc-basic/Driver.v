Require Import QuickChick.
Import Gen GenComb.

Require Import List. Import ListNotations.

Require Import Machine.
Require Import Printing.
Require Import Generation.
Require Import Indist.

Require Import String.
Local Open Scope string.
Definition SSNI (t : table) (v : @Variation State) : Checker  :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
(*   match lookupInstr st1 with
    | Some i =>     collect (show i) (  *)
  if indist st1 st2 then
    match l1, l2 with
      | L,L  =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
(*
            whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl)
*)
            (* collect ("L -> L")*) (checker (indist st1' st2'))
          | _, _ => (* collect "L,L,FAIL" true *) checker rejected
        end
      | H, H =>
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              (* whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl) *)
              (* collect ("H -> L")*) (checker (indist st1' st2') )
            else if is_atom_low (st_pc st1') then
                   (* whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
              (* collect ("H -> H")*) (checker (indist st2 st2'))
            else
(*            whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )*)
              (* collect ("H -> H")*) (checker (indist st1 st1'))
          | _, _ => checker rejected
        end
      | H,_ =>
        match exec t st1 with
          | Some st1' =>
(*             whenFail ("States: " ++ nl ++ show_pair st1 st1' ++ nl )*)
                      (* collect "H -> H"*) (checker (indist st1 st1'))
          | _ => (*collect "H,_,FAIL" true *) checker rejected
        end
      | _,H =>
        match exec t st2 with
          | Some st2' =>
(*             whenFail ("States: " ++ nl ++ show_pair st2 st2' ++ nl )*)
                      (* collect "H -> H"*) (checker (indist st2 st2'))
          | _ => (*collect "L,H,FAIL" true *) checker rejected
        end
    end
  else (* collect "Not indist!" true*)  checker rejected
              (* )
    | _ => checker rejected
  end*).

Definition prop_SSNI t : Checker :=
  forAllShrink gen_variation_state (fun _ => nil)
   (SSNI t : Variation -> G QProp).

Definition prop_gen_indist :=
  forAllShrink gen_variation_state (fun _ => nil)
               (fun v => let '(V st1 st2) := v in indist st1 st2).

Definition runSSNIdefaultTable := showResult (quickCheck (prop_SSNI default_table)).

QuickCheck runSSNIdefaultTable.

Axiom numTests : nat.
Extract Constant numTests => "20000".
Definition myArgs : Args :=
  let '(MkArgs rp mSuc md mSh mSz c) := stdArgs in
  MkArgs rp numTests md mSh mSz c.

Require Import Mutate.
Require Import MutateCheck.

Instance mutateable_table : Mutateable table :=
{|
  mutate := mutate_table
|}.

Require Import ZArith.
(*
Eval lazy -[labelCount helper] in
  nth (mutate_table default_table) 18.
*)

Definition testMutantX n :=
  match nth (mutate_table default_table) n with
    | Some t => showResult (quickCheckWith myArgs (prop_SSNI t))
    | _ => ""
  end.

Definition testMutants :=
  mutateCheckArgs myArgs default_table
    (fun t => (forAllShrinkShow
      gen_variation_state (fun _ => nil) (fun _ => "")
      (SSNI t ))).

Definition runTestMutants := show testMutants.

QuickCheck runTestMutants.

Definition st1 :=
  St [Store; Store] [0 @ L] (0 @ L :: 0 @ H :: Mty) (0 @ L).
Definition st2 :=
  St [Store; Store] [0 @ L] (0 @ L :: 1 @ H :: Mty) (0 @ L).
Definition ex_indist : indist st1 st2 = true. auto. Qed.

Definition ex_test :=
  match nth (mutate_table default_table) 18 with
    | Some t => showResult (quickCheck (SSNI t (V st1 st2)))
    | _ => ""
  end.

Definition main :=
  (* ex_test.*)
  testMutantX 18.
(* show testMutants. *)
  (* showResult (quickCheck (prop_SSNI default_table)). *)

(* QuickCheck main. *)
