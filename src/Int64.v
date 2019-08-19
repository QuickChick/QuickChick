(** * 64-bit unsigned integers *)

(* begin hide *)
From Coq Require Ascii String HexString.
From Coq Require Import
     ZArith Int63.

Set Primitive Projections.
(* end hide *)

(** 64-bit unsigned integers *)
Record int64 : Set := Int64 {
  ms63b : int; (* Most significant 63 bits *)
  lsb : bool;  (* Least significant bit *)
}.

Declare Scope int64_scope.
Bind Scope int64_scope with int64.
Delimit Scope int64_scope with int64.

Local Open Scope int63.

Definition size : nat := 64.

(** ** Arithmetic *)

Definition add '(Int64 m i) '(Int64 n j) : int64 :=
  match i, j with
  | true, true => Int64 (m + n + 1) false
  | false, i | i, false => Int64 (m + n) i
  end.

Definition sub '(Int64 m i) '(Int64 n j) : int64 :=
  match i, j with
  | true, true | false, false => Int64 (m - n) false
  | true, false => Int64 (m - n) true
  | false, true => Int64 (m - n - 1) true
  end.

Definition mul '(Int64 m i) '(Int64 n j) : int64 :=
  let mn := (m * n) * 2 in
  let mj := if j then m else 0 in
  let ni := if i then n else 0 in
  Int64 (mn + mj + ni) (andb i j).

Definition land_ '(Int64 m i) '(Int64 n j) : int64 :=
  Int64 (m land n) (andb i j).

Definition lor_  '(Int64 m i) '(Int64 n j) : int64 :=
  Int64 (m lor n) (orb i j).

Definition lxor_  '(Int64 m i) '(Int64 n j) : int64 :=
  Int64 (m lxor n) (xorb i j).

Definition lsr '(Int64 m i) (n : int) : int64 :=
  if (0 < n)%int63 then
    Int64 (m >> n) (get_digit m (n - 1))
  else
    Int64 m i.

Definition lsl '(Int64 m i) (n : int) : int64 :=
  if (0 < n)%int63 then
    Int64 ((m << n) lor (b2i i << (n - 1))) false
  else
    Int64 m i.

(** ** Comparison *)

Definition eqb '(Int64 m i) '(Int64 n j) : bool :=
  (Int63.eqb m n && bool_eq i j)%bool.

Definition compare_bool (i j : bool) : comparison :=
  match i, j with
  | true, true | false, false => Eq
  | true, false => Gt
  | false, true => Lt
  end.

Definition compare '(Int64 m i) '(Int64 n j) : comparison :=
  match Int63.compare m n with
  | Eq => compare_bool i j
  | Lt => Lt
  | Gt => Gt
  end.

Definition ltb (m n : int64) : bool :=
  match compare m n with
  | Lt => true
  | _ => false
  end.

(** ** Conversions *)

Import Ascii String HexString.

(* Auxiliary *)
Fixpoint filterhex (s : string) : string :=
  match s with
  | ""%string => ""
  | String x xs =>
    match x with
    | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
    | "a" | "b" | "c" | "d" | "e" | "f"
    | "A" | "B" | "C" | "D" | "E" | "F" => String x (filterhex xs)
    | _ => filterhex xs
    end%char
  end.

(** *** To [int64] *)

Definition of_int (n : int) : int64 :=
  Int64 (n >> 1) (bit n 0).

Definition of_Z (n : Z) : int64 :=
  Int64 (Int63.of_Z (Z.div2 n)) (Z.testbit n 0).

Definition of_N (n : N) : int64 :=
  Int64 (Int63.of_Z (Z.of_N (N.div2 n))) (N.testbit n 0).

Definition of_hex (s : string) : int64 :=
  of_N (HexString.Raw.to_N (filterhex s) 0).

(** *** From [int64] *)

(** Truncates *)
Definition to_int '(Int64 m i) : int :=
  (m << 1) + b2i i.

Definition to_Z (n : int64) : Z :=
  2 * Int63.to_Z (ms63b n) + Z.b2z (lsb n).

(** ** More arithmetic *)

Fixpoint slow_div (qmax : nat) (m n : int64) : int64 :=
  if ltb m n then Int64 0 false
  else
    match qmax with
    | O => Int64 0 true
    | S qmax => add (Int64 0 true) (slow_div qmax (sub m n) n)
    end.

Definition divmod '(Int64 m i) (n : int) : int64 * int :=
  let q := Int63.div m n in
  let r := Int63.mod m n in
  let q' := (Int63.ltb (n >> 1) r || (Int63.eqb (n >> 1) r && implb (bit n 0) i))%bool in
  (Int64 q q', if q' then (r << 1) + b2i i - n else (r << 1) + b2i i).

Definition div (m : int64) (n : int) : int64 := fst (divmod m n).
Definition mod_ (m : int64) (n : int) : int := snd (divmod m n).

(** ** Notations *)

Infix "+" := Int64.add : int64_scope.
Infix "-" := Int64.sub : int64_scope.
Infix "*" := Int64.mul : int64_scope.
Infix "<<" := Int64.lsl : int64_scope.
Infix ">>" := Int64.lsr : int64_scope.
Infix "land" := Int64.land_ : int64_scope.
Infix "lor" := Int64.lor_ : int64_scope.
Infix "lxor" := Int64.lxor_ : int64_scope.
Infix "mod" := Int64.mod_ : int64_scope.
Infix "=?" := Int64.eqb : int64_scope.
Infix "<?" := Int64.ltb : int64_scope.

(** *** Literals *)

(** NB: Literals are evaluated, as opposed to plain function applications. *)
Numeral Notation int64 Int64.of_Z Int64.to_Z
  : int64_scope.

Module Int64Notations.

Definition print_byte_fail : int64 -> option Byte.byte := fun _ => None.
Definition of_bytes (s : list Byte.byte) : int64 :=
  Int64.of_hex (string_of_list_byte s).

End Int64Notations.

Declare Scope int64_hex_scope.
Delimit Scope int64_hex_scope with int64_hex.

String Notation int64 Int64Notations.of_bytes Int64Notations.print_byte_fail
  : int64_hex_scope.

(* begin hide *)
Section UnitTest.

Local Open Scope int64.

Local Infix "=" := (@eq int64).

Let add_2_2 : 2 + 2 = 4 := eq_refl.
Let add_3_2 : 3 + 2 = 5 := eq_refl.
Let add_2_3 : 2 + 3 = 5 := eq_refl.
Let add_3_3 : 3 + 3 = 6 := eq_refl.

Let mul_2_2 : 2 * 2 = 4 := eq_refl.
Let mul_3_2 : 3 * 2 = 6 := eq_refl.
Let mul_2_3 : 2 * 3 = 6 := eq_refl.
Let mul_3_3 : 3 * 3 = 9 := eq_refl.

Let lsr_2_1 : 2 >> 1 = 1 := eq_refl.
Let lsr_3_1 : 3 >> 1 = 1 := eq_refl.
Let lsr_5_1 : 5 >> 1 = 2 := eq_refl.
Let lsr_5_2 : 5 >> 2 = 1 := eq_refl.

Let lsl_2_1 : 2 << 1 = 4 := eq_refl.
Let lsl_3_1 : 3 << 1 = 6 := eq_refl.

Let div_2_2 : divmod 2 2 = (1, 0%int63) := eq_refl.
Let div_2_3 : divmod 2 3 = (0, 2%int63) := eq_refl.
Let div_3_2 : divmod 3 2 = (1, 1%int63) := eq_refl.
Let div_4_2 : divmod 4 2 = (2, 0%int63) := eq_refl.
Let div_5_2 : divmod 5 2 = (2, 1%int63) := eq_refl.

Let of_hex_FF : "FF"%int64_hex = 255 := eq_refl.

End UnitTest.
(* end hide *)

(** ** Facts *)

Lemma add_assoc (a b c : int64) : (a + (b + c) = (a + b) + c)%int64.
Proof.
  intros. unfold Int64.add.
  destruct a as [ ? []], b as [ ? []], c as [ ? []]; f_equal.
  all: rewrite ! Int63.add_assoc, ? (Int63.add_comm _ 1), ? Int63.add_assoc.
  all: reflexivity.
Qed.
