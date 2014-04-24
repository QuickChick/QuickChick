Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Gen Test Show Property.

Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].

Extract Inductive positive => "Prelude.Int"
 [ "(\x->((Prelude.+) ((Prelude.*) 2 x) 1))" "((Prelude.*)2)" "1" ]
 "(\ f2p1 f2p f1 p ->
   if (Prelude.<=) p 1 then f1 () else
     let q = ((Prelude.div) p 2) in
       if ((Prelude.==) ((Prelude.mod) p 2) 0) then f2p q else f2p1 q)".

Extract Constant Pos.compare => "Prelude.compare".
Extract Constant Pos.succ => "Prelude.succ".

Extract Constant Zplus => "(Prelude.+)".
Extract Constant Zminus => "(Prelude.-)".
Extract Constant Zmult => "(Prelude.*)".
Extract Constant Z.pos_div_eucl => "Prelude.quotRem".
Extract Constant shift_nat => "(\n m -> 
  Data.Bits.shiftL m (Prelude.fromIntegral n))".
Extract Constant Z.eq_dec => "(Prelude.==)".

Extract Inductive comparison => "Prelude.Ordering"
  [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ]
  "(\ feq flt fgt c -> case c of {
      Prelude.EQ -> feq ();
      Prelude.LT -> flt ();
      Prelude.GT -> fgt () })".

Extract Inductive N => "Prelude.Int"
  [ "0" "" ]
  "(\ f0 fp n ->
      if (Prelude.==) n 0 then f0 () else fp n )".

Extract Inductive Z => "Prelude.Int"
 [ "0" "" "Prelude.negate" ]
 "(\ f0 fp fn z ->
    let s = Prelude.signum z in
      if (Prelude.==) s 0 then f0 () else
        if (Prelude.>) s 0 then fp z else fn (Prelude.negate z))".

Extract Inductive nat => "Prelude.Integer"
  [ "0" "Prelude.succ" ]
  "(\ f0 fs n ->
      if (Prelude.==) n 0 then f0 () else fs ((Prelude.-) n 1))".

Extract Inductive bool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ]
  "(\ ft ff b -> if b then ft () else ff ())".

Extract Inductive sumbool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ]
  "(\ ft ff b -> if b then ft () else ff ())".

Extract Inductive prod => "(,)"
  [ "(,)" ]
  "(\ f p -> f (Prelude.fst p) (Prelude.snd p))".

Extract Inductive list => "[]"
  [ "[]" "(:)" ]
  "(\ fnil fcons l -> case l of { [] -> fnil (); (a:as) -> fcons a as; })".

Extract Inductive option => "Prelude.Maybe"
  [ "Prelude.Just" "Prelude.Nothing" ]
  "(\ fj fn e -> case e of {
                   Prelude.Just a -> fj a;
                   Prelude.Nothing -> fn (); })".

Extract Inductive ascii => "Prelude.Char"
  [ "(\ b0 b1 b2 b3 b4 b5 b6 b7 -> let f b i = if b then DB.shiftL 1 i else 0 in DC.chr 
     (f b0 0 Prelude.+ f b1 1 Prelude.+ f b2 2 Prelude.+ f b3 3 Prelude.+ 
     f b4 4 Prelude.+ f b5 5 Prelude.+ f b6 6 Prelude.+ f b7 7))" ].

Extract Inductive string => "Prelude.String"
  [ "[]" "(\c s -> c : s)" ]
  "(\fe fs s -> case s of {
                  [] -> fe ();
                  c : s' -> fs c s'; })".

Extract Constant RandomGen   => "SR.StdGen".
Extract Constant rndNext     => "SR.next".
Extract Constant rndGenRange => "SR.genRange".
Extract Constant rndSplit    => "SR.split".
Extract Constant mkRandomGen => "SR.mkStdGen".
Extract Constant randomRNat  => "SR.randomR".
Extract Constant randomRBool => "SR.randomR".
Extract Constant randomRInt  => "SR.randomR".
Extract Constant newStdGen   => "SR.newStdGen".

Extract Constant Test.ltAscii => "(Prelude.<=)".
Extract Constant Test.strEq   => "(Prelude.==)".
Extract Constant Coq.Numbers.Natural.Peano.NPeano.div => "Prelude.div".
Extract Constant Coq.Numbers.Natural.Peano.NPeano.modulo => "Prelude.mod".
Extract Constant Test.gte => "(Prelude.>=)".
Extract Constant le_gt_dec => "(Prelude.<=)".
Extract Constant Show.show_nat => "Prelude.show".
Extract Constant Show.show_bool => "Prelude.show".
Extract Constant trace => "DT.trace".

Set Extraction AccessOpaque.

Extract Constant Show.nl => "[DC.chr 10]".
Extract Constant Test.defNumTests => "10000".
Extract Constant Test.defNumDiscards => "(Prelude.*) 2 defNumTests".
Extract Constant Test.unsafeRandomSeed => "(unsafePerformIO (SR.randomIO :: GHC.Base.IO GHC.Base.Int))".
