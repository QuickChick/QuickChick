Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Random RoseTrees Test Show Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List.

Extract Constant show_nat =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_int i))".
Extract Constant show_bool =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_bool i))".
Extract Constant show_int =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_int i))".

Extract Constant RandomSeed   => "Random.State.t".
Extract Constant randomNext   => "(fun r -> Random.State.bits r, r)".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant randomSplit  => "(fun x -> (x,x))".
Extract Constant mkRandomSeed => "(fun x -> Random.init x; Random.get_state())".
Extract Constant randomRNat  =>
  "(fun (x,y) r -> (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  =>
  "(fun (x,y) r -> (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant newRandomSeed => "(Random.State.make_self_init ())".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

(* Extract Constant Test.ltAscii => "(<=)". *)
(* Extract Constant Test.strEq   => "(=)". *)
Extract Constant Coq.Numbers.Natural.Peano.NPeano.div => "(/)".
Extract Constant Coq.Numbers.Natural.Peano.NPeano.modulo => "(fun x y -> x mod y)".
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace => "(fun x -> print_string (QuickChickLib.string_of_coqstring x); flush stdout; fun y -> y)".

Set Extraction AccessOpaque.

Extract Constant Show.nl => "['\n']".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.
Extract Constant divn => "(/)".
Extract Constant modn => "(fun x y -> x mod y)".
Extract Constant eqn => "(==)".
