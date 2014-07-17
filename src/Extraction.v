Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Axioms AbstractGen Gen Test Show Property.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List.

(*
Extract Inductive unit => "()" [ "()" ].

Extract Inductive positive => "int"
 [ "(fun x -> 2 * x + 1)" "(fun x -> 2 * x)" "1" ]
 "(fun f2p1 f2p f1 p -> 
   if p <= 1 then f1 () else
     let q = p / 2 in 
     if p mod 2 = 0 then f2p q else f2p1 q)".

Extract Constant Pos.compare => "compare".
Extract Constant Pos.succ => "succ".

Extract Constant Zplus => "(+)".
Extract Constant Zminus => "(-)".
Extract Constant Zmult => "(fun x y -> x * y)".
Extract Constant Z.pos_div_eucl => "/".
Extract Constant shift_nat => "lsl".
Extract Constant Z.eq_dec => "(=)".

Extract Inductive comparison => "int"
  [ "0" "(-1)" "1" ]
  "(fun feq flt fgt c -> 
      if c = 0 then feq ()
      else if c < 0 then flt ()
      else fgt ())".

Extract Inductive N => "int"
  [ "0" "" ]
  "(fun f0 fp n -> if n = 0 then f0 () else fp n )".

Extract Inductive Z => "int"
 [ "0" "" "(fun x -> (-x))" ]
 "(fun f0 fp fn z ->
    if z = 0 then f0 ()  
    else if z > 0 then fp z else fp (-z))".

Extract Inductive nat => "int"
  [ "0" "" ]
  "(fun f0 fs n ->
      if n = 0 then f0 () else fs (n-1))".

Extract Inductive bool => "bool"
  [ "true" "false" ]
  "(fun ft ff b -> if b then ft () else ff ())".

Extract Inductive sumbool => "bool"
  [ "true" "false" ]
  "(fun ft ff b -> if b then ft () else ff ())".
*)

(*
Extract Inductive list => "[]"
  [ "[]" "(:)" ]
  "(\ fnil fcons l -> case l of { [] -> fnil (); (a:as) -> fcons a as; })".

Extract Inductive option => "Prelude.Maybe"
  [ "Prelude.Just" "Prelude.Nothing" ]
  "(\ fj fn e -> case e of {
                   Prelude.Just a -> fj a;
                   Prelude.Nothing -> fn (); })".
*)
(*
Extract Inductive ascii => "Prelude.Char"
  [ "(\ b0 b1 b2 b3 b4 b5 b6 b7 -> let f b i = if b then DB.shiftL 1 i else 0 in DC.chr 
     (f b0 0 Prelude.+ f b1 1 Prelude.+ f b2 2 Prelude.+ f b3 3 Prelude.+ 
     f b4 4 Prelude.+ f b5 5 Prelude.+ f b6 6 Prelude.+ f b7 7))" ].

Extract Inductive string => "Prelude.String"
  [ "[]" "(\c s -> c : s)" ]
  "(\fe fs s -> case s of {
                  [] -> fe ();
                  c : s' -> fs c s'; })".
*)

Extract Constant show_nat =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_int i))".
Extract Constant show_bool =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_bool i))".
Extract Constant show_int =>
  "(fun i -> QuickChickLib.coqstring_of_string (string_of_int i))".

Extract Constant RandomGen   => "Random.State.t".
Extract Constant rndNext     => "(fun r -> Random.State.bits r, r)".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant rndSplit    => "(fun x -> (x,x))".
Extract Constant mkRandomGen => "(fun x -> Random.init x; Random.get_state())".
Extract Constant randomRNat  => 
  "(fun (x,y) r -> (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  => 
  "(fun (x,y) r -> (x + (Random.State.int r (y - x + 1)), r))".
Extract Constant newStdGen   => "(Random.State.make_self_init ())".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

Extract Constant Test.ltAscii => "(<=)".
Extract Constant Test.strEq   => "(=)".
(*
Extract Constant Coq.Numbers.Natural.Peano.NPeano.div => "(/)".
Extract Constant Coq.Numbers.Natural.Peano.NPeano.modulo => "(fun x y -> x mod y)".
*)
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace => "(fun x y -> print_string (QuickChickLib.string_of_coqstring x); y)".

Set Extraction AccessOpaque.

Extract Constant Show.nl => "['\n']".
Extract Constant Test.defNumTests => "10000".
Extract Constant Test.defNumDiscards => "(2 * defNumTests)".
(*Extract Constant Test.unsafeRandomSeed => "(unsafePerformIO (SR.randomIO :: GHC.Base.IO GHC.Base.Int))". *)
