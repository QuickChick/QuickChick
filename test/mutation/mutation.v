From QuickChick Require Import QuickChick.
From Coq Require Import List String ExtrOcamlNatInt.
Import ListNotations.

Definition prop_example :=
  let x := mutant! 10 20 in
  let y := mutants! 1 (2,3,4) in
  whenFail (show x ++ " + " ++ show y ++ " <> 11")%string
           (x + y = 11 ?).

Definition main := runTests [
  qc "example" prop_example
].

Extraction "mutation.ml" main.
