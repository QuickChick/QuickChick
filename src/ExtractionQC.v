Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import RandomQC RoseTrees Test Show Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List Nat.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> ())".

Extract Constant show_nat =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".
Extract Constant show_bool =>
  "(fun i ->
  let s = string_of_bool i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Extract Constant show_Z =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".
Extract Constant show_N =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Extract Constant RandomSeed    => "QuickChickLib.randomSeed".
Extract Constant randomNext    => "QuickChickLib.randomNext".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant randomSplit   => "QuickChickLib.randomSplit".
Extract Constant mkRandomSeed  => "QuickChickLib.mkRandomSeed".
Extract Constant randomRNat    => "QuickChickLib.randomRNat".
Extract Constant randomRBool   => "QuickChickLib.randomRBool".  
Extract Constant randomRInt    => "QuickChickLib.randomRInt". 
Extract Constant randomRN      => "QuickChickLib.randomRN".
Extract Constant newRandomSeed => "QuickChickLib.newRandomSeed".
Extract Constant copySeed      => "QuickChickLib.copySeed".
Extract Constant registerSeed  => "QuickChickLib.registerSeed".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

(* Extract Constant Test.ltAscii => "(<=)". *)
(* Extract Constant Test.strEq   => "(=)". *)
Extract Constant Nat.div => "(/)".
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace =>
  "(fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l)); flush stdout; fun y -> y)".

Set Extraction AccessOpaque.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.
Extract Constant divn => "(/)".
Extract Constant modn => "(fun x y -> x mod y)".
Extract Constant eqn => "(==)".

Axiom print_extracted_coq_string : string -> unit.
Extract Constant print_extracted_coq_string =>
 "fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l))".
