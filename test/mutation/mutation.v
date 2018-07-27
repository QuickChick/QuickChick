From QuickChick Require Import QuickChick.
Require Import String.
Require Import ExtrOcamlNatInt.

Definition prop_example :=
  let x := mutant! 10 20 in
  let y := mutants! 1 (2,3,4) in
  whenFail (show x ++ " + " ++ show y ++ " <> 11")%string
           (x + y = 11 ?).

Definition main :=
  print_extracted_coq_string
    (show (quickCheck prop_example)).

Extraction "mutation.ml" main.
