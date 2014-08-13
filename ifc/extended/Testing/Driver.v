Require Import Machine.
Require Import Rules.
Require Import SSNI.
Require Import String.

Require Import QuickChick.
Require Import Common.

Require Import Show.
Require Import Test.
Require Import ZArith.
Require Import List.

Require Import Generation.
Require Import Shrinking.

Require Import Reachability.
Require Import SingleStateArb.

Require Import SanityChecks.

Definition testTMU :=
  let H1 := lab_of_list [Z.of_nat 1] in
  let H2 := lab_of_list [Z.of_nat 2] in
  let TOP := join H1 H2 in
  show (run_tmr default_table OpAlloc <|bot; TOP; H2|> bot).

Definition testSSNI t := quickCheck (propSSNI t : Gen.Gen QProp).

(* Testing default table *)

Definition testSSNIdefaultTable := showResult (testSSNI default_table).

QuickCheck testSSNIdefaultTable.

(* Testing mutants *)

Require Import Mutate.
Require Import MutateCheck.

Instance mutateable_table : Mutateable table :=
{|
  mutate := mutate_table
|}.

Definition testMutants :=
  mutateCheckMany default_table (fun t => [propSSNI t;
    prop_exec_preserves_well_formed t] : list (Gen.Gen QProp)
).

Definition runTestMutants := show testMutants.

QuickCheck runTestMutants.

(* The rest of this file is mostly garbage *)

(*
Eval lazy -[labelCount helper] in
  nth 26 (mutate_table default_table) default_table.
*)

Definition testMutantX x y :=
  let mutant := fun o' =>
    (helper x y o' (default_table o'))  in
  testSSNI mutant.

Definition testMutant7 := testMutantX
  OpBCall (≪TRUE, JOIN Lab2 LabPC, Lab1 ≫).
(* CH: most often we catch this one; but sometimes it escapes *)

Definition testMutant9 := testMutantX
  OpBRet (≪LE Lab1 (JOIN Lab2 Lab3), Lab2, Lab3 ≫).
(* Problem: we weren't generating _any_ HIGH -> LOW cases;
            doing a very bad job at generating stacks!
("Some OpBRet, Failed",484),
("Some OpBRet, HIGH -> HIGH",206),
("Some OpBRet, LOW -> *",224),
("Some OpBRet, Second failed H",28),
("Some OpBRet, Second not low",83),
   After expedient fix this finds the bug and looks like this:
("Some OpBRet, Failed",85),
("Some OpBRet, HIGH -> HIGH",23),
("Some OpBRet, LOW -> *",40),
("Some OpBRet, Second failed H",6),
("Some OpBRet, HIGH -> LOW",7), <---- this case was missing
*)

Definition testMutant26 := testMutantX
  OpBNZ (≪TRUE, __ , LabPC ≫).
(* This was found, just not often enough (once in 20000-30000 tests)
   We weren't generating zeroes often enough (1 in 200)
   Changed to 1 in 10 and we're finding this just fine. *)

Definition testMutant29 := testMutantX
  OpLoad (≪TRUE, Lab3, JOIN Lab1 Lab2 ≫).
(* CH: this one is at the limit (with 10000 tests sometimes we catch
       it and sometimes we don't)*)

Definition testMutant36 := testMutantX
  OpAlloc (≪TRUE, Lab2, LabPC ≫).
(* XXX: this and the next mutants break well-formedness;
   but we don't test that as a precondition to SSNI
   DONE: for each mutant we should also test well-formedness
   and if that fails the mutant is also killed *)

Definition testMutantWF x y :=
  let mutant := fun o' =>
    (helper x y o' (default_table o'))  in
  quickCheck (prop_exec_preserves_well_formed mutant : Gen.Gen QProp).

Definition testMutant36wf := testMutantWF
  OpAlloc (≪TRUE, Lab2, LabPC ≫).
(* XXX: this sometimes fails, and otherwise gives stack overflow
   during shrinking (probably an infinite loop of some sort) *)

Definition testMutant37 := testMutantX
  OpAlloc (≪TRUE, Lab1, LabPC ≫).

Definition testMutant37wf := testMutantWF
  OpAlloc (≪TRUE, Lab1, LabPC ≫).
(* XXX: this sometimes fails, and otherwise gives stack overflow
   during shrinking (probably an infinite loop of some sort) *)

(* Definition testNI := testMutant37wf. *)

(* QuickCheck testMutants.*)
(* Definition testNI := testMutant9.*)
(* Definition testNI := testSSNI default_table. *)
(* Definition testNI := quickCheck prop_stamp_generation. *)
(* Definition testNI :=
  quickCheck (prop_preserves_well_formed default_table). *)
(* Definition testNI := quickCheck prop_generate_indist. *)
(*(forAllShrink (fun _ => "implement me!")
                           genSingleExecState
                           (fun _ => nil)
                           (propWellFormednessPreserved default_table)).*)

(*Definition testNI :=
  let l := lab_of_list [Pos.of_nat 1] in
  let h := lab_of_list [Pos.of_nat 1; Pos.of_nat 2] in
  match alloc 2%Z l bot (Vint Z0 @ bot) (Mem.empty Atom Label) with
    | Some (mf, m') =>
      map (Mem.get_frame m') (Mem.get_all_blocks h m')
    | _ => []
  end.
*)