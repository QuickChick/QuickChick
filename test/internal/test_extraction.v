From Coq Require Import ZArith NArith String Int63 Extraction ExtrOcamlZBigInt.
From QuickChick Require Import QuickChick.

From SimpleIO Require Import SimpleIO.
Import IO.Notations.

Definition _assert_equal {A} `{Dec_Eq A} `{Show A} (x y : A) (_ : x = y) : IO unit :=
  if dec_eq x y then ret tt else print_endline ("Failed: " ++ show (x, y))%string.

Notation assert_equal x y := (_assert_equal x y eq_refl).

Definition test_div : IO unit :=
  ( assert_equal (1 / (-3)) (-1) ;;
    assert_equal ((-1) / (-3)) 0 ;;
    assert_equal ((-1) / 3) (-1)
  )%Z%io.

Definition test_mod : IO unit :=
  ( assert_equal (1 mod (-3)) (-2) ;;
    assert_equal ((-1) mod (-3)) (-1) ;;
    assert_equal ((-1) mod 3) 2
  )%Z%io.

Definition test_shiftr : IO unit :=
  ( assert_equal (Z.shiftr 3 1) 1 ;;
    assert_equal (Z.shiftr 3 (-1)) 6 ;;
    assert_equal (Z.shiftr (-3) 1) (-2) ;;
    assert_equal (Z.shiftr (-3) (-1)) (-6)
  )%Z%io.

Definition test_shiftl : IO unit :=
  ( assert_equal (Z.shiftl 3 1) 6 ;;
    assert_equal (Z.shiftl 3 (-1)) 1 ;;
    assert_equal (Z.shiftl (-3) 1) (-6) ;;
    assert_equal (Z.shiftl (-3) (-1)) (-2)
  )%Z%io.

Definition is_left {A B} (x : {A} + {B}) : bool :=
  match x with
  | left _ => true
  | right _ => false
  end.

Definition test_misc_Z : IO unit :=
  ( assert_equal (Z.eqb 0%Z 1%Z) false ;;
    assert_equal (is_left (Z.eq_dec 0%Z 1%Z)) false ;;
    assert_equal (Z.div_eucl 17 5) (3, 2)%Z ;;
    assert_equal (Z.div_eucl (-17) (-5)) (3, -2)%Z ;;
    assert_equal (Z.to_N 3%Z) 3%N ;;
    assert_equal (Z.to_N (-1)%Z) 0%N ;;
    assert_equal (Int63.to_Z (Int63.of_Z 0)) 0%Z
  )%io.

Definition test_misc_N : IO unit :=
  ( assert_equal (N.eqb 0%N 1%N) false ;;
    assert_equal (is_left (N.eq_dec 0%N 1%N)) false ;;
    assert_equal (N.div_eucl 17 5) (3, 2)%N ;;
    assert_equal (N.div 10 2) 5%N ;;
    assert_equal (N.modulo 17 5) 2%N ;;
    assert_equal (N.shiftl 10 1) 20%N ;;
    assert_equal (N.shiftr 10 1) 5%N
  )%io.

Definition test_all : IO unit :=
  ( test_div ;;
    test_mod ;;
    test_shiftr ;;
    test_shiftl ;;
    test_misc_Z ;;
    test_misc_N
  )%io.

RunIO test_all.
