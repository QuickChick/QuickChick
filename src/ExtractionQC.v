Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
From QuickChick Require Import
  RandomQC RoseTrees Test Show Checker ExtractionQCCompat.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List Nat.

(** Temporary fix for https://github.com/coq/coq/issues/7017. *)
(** Scott encoding of [Decimal.int] as [forall r. (uint -> r) -> (uint -> r) -> r]. *)
Extract Inductive Decimal.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Decimal.int *)"
  [ "(fun x pos _ -> pos (Obj.magic x))"
    "(fun y _ neg -> neg (Obj.magic y))"
  ] "(fun pos neg i -> Obj.magic i pos neg)".

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

Extract Constant RandomSeed   => "Random.State.t".
Extract Constant randomNext   => "(fun r -> Random.State.bits r, r)".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant randomSplit  => "(fun x -> (x,x))".
Extract Constant mkRandomSeed => "(fun x -> Random.init x; Random.get_state())".
Extract Constant randomRNat  =>
  "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  =>
  "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant randomRN =>
  "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant newRandomSeed => "(Random.State.make_self_init ())".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

(* Extract Constant Test.ltAscii => "(<=)". *)
(* Extract Constant Test.strEq   => "(=)". *)
Extract Constant Nat.div => "(fun m -> function 0 -> 0 | d -> m / d)".
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace =>
  "(fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> Bytes.set s i c; copy (i+1) l
   in Bytes.to_string (copy 0 l)); flush stdout; fun y -> y)".

Set Extraction AccessOpaque.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.
Extract Constant divn => "(fun m -> function 0 -> 0 | d -> m / d)".
Extract Constant modn => "(fun m -> function 0 -> m | d -> m mod d)".
Extract Constant eqn => "(==)".

Axiom print_extracted_coq_string : string -> unit.
Extract Constant print_extracted_coq_string =>
 "fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l))".
