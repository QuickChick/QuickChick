From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* forAllShrinkNonDet retests a discarding shrink candidate with fresh
   seeds, so shrinking a property that discards half of the time still
   reaches the minimal counterexample 0 (issue #372). *)
QuickChick (forAllShrinkNonDet 100 (returnGen 100) shrink (fun (n : nat) =>
  forAll (elems_ true [true; false]) (fun b => implication b false))).
