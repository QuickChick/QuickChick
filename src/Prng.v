From Coq Require Import String Ascii ZArith NArith Int63.
From QuickChick Require Import Int64.

Local Open Scope int64.

Definition popcount (z : int64) : int64 :=
  let z : int64 := z - (z >> 1) land "5555_5555_5555_5555"%int64_hex in
  let z : int64 := (z land "3333_3333_3333_3333"%int64_hex) + ((z >> 2) land "3333_3333_3333_3333"%int64_hex) in
  let z := (z + (z >> 4)) land "0f0f_0f0f_0f0f_0f0f"%int64_hex in
  (z * "01010101_01010101"%int64_hex) >> 56.

Section PopcountUnitTests.

Let popcount_0 : popcount 0 = 0 := eq_refl.
Let popcount_1 : popcount 1 = 1 := eq_refl.
Let popcount_2 : popcount 2 = 1 := eq_refl.
Let popcount_3 : popcount 3 = 2 := eq_refl.
Let popcount_7 : popcount 7 = 3 := eq_refl.
Let popcount_15 : popcount 15 = 4 := eq_refl.
Let popcount_42 : popcount 42 = 3 := eq_refl.

End PopcountUnitTests.

(** * SplitMix constants *)

Definition golden_gamma : int64 := "9e3779b97f4a7c15"%int64_hex.
Definition x_ff51afd7ed558ccd : int64 := "ff51afd7ed558ccd"%int64_hex.
Definition x_c4ceb9fe1a85ec53 : int64 := "c4ceb9fe1a85ec53"%int64_hex.
Definition x_bf58476d1ce4e5b9 : int64 := "bf58476d1ce4e5b9"%int64_hex.
Definition x_94d049bb133111eb : int64 := "94d049bb133111eb"%int64_hex.
Definition x_aaaaaaaaaaaaaaaa : int64 := "aaaaaaaaaaaaaaaa"%int64_hex.

(** * Conversions *)

(* SplitMix implementation. *)

(* [z ^ (z >>> n)]*)
Definition shift_xor (z : int64) (n : int) :=
  (z lxor (z >> n))%int64.

Definition mix64 (z : int64) : int64 :=
  let z := mul x_ff51afd7ed558ccd (shift_xor z 33) in
  let z := mul x_c4ceb9fe1a85ec53 (shift_xor z 33) in
  shift_xor z 33.

Definition mix64variant13 (z : int64) : int64 :=
  let z := mul x_bf58476d1ce4e5b9 (shift_xor z 30) in
  let z := mul x_94d049bb133111eb (shift_xor z 27) in
  shift_xor z 31.

Definition mix_gamma (z : int64) : int64 :=
  let z := (mix64 z) land 1 in
  if popcount (shift_xor z 1) <? 24 then
    z lxor x_aaaaaaaaaaaaaaaa
  else
    z.

(* Invariant: c is even, 0 <= r < 64 *)
Record state := MkState {
  seed : int64;
  gamma : int64;
  counter : int;
  remaining : int;
}.

(* Extend a 63-bit path with [0] or [1].
   If the path is full (length 63), output it as [Some]
   64bit word to hash, and produce fresh paths.
   Invariant: c is even, 0 <= r < 64 *)
Definition split_path (c : int) (r : int) :
  option int * int * int * int :=
  if Int63.eqb r 0 then
    (Some c, 0, 1 << 62, 61)%int63
  else
    (None, c, c lor (1 << r), (r - 1))%int63.

Definition split '(MkState s0 g c r) : state * state :=
  let '(oc, c0, c1, r) := split_path c r in
  match oc with
  | None =>
    let new c := MkState s0 g c r in
    (new c0, new c1)
  | Some c' =>
    let s1 := s0 + (g * Int64.of_int c') in
    let s2 := s1 + g in
    let s' := mix64variant13 s1 in
    let g' := mix_gamma s2 in
    let new c := MkState s' g' c r in
    (new c0, new c1)
  end.

Definition of_seed (n : int64) : state :=
  {| seed := n;
     gamma := golden_gamma;
     counter := 0;
     remaining := 63; |}.

(* Get 64 random bits. *)
Definition bits '(MkState s0 g c r) : int64 :=
  let s1 := s0 + (g * Int64.of_int c) in
  mix64variant13 s1.

(* [bound > 0] *)
Fixpoint range_int_aux (retry : nat) (s : state) (bound : int) : int :=
  let (s, s1) := split s in
  let b := ms63b (bits s1) in (* N.B.: [s1] must be the one with a 1 bit at index (r + 1) so that it is different at every iteration. *)
  let v := Int63.mod b bound in
  if Int63.leb (b - v) (0 - bound) then v
  else
    match retry with
    | S retry => range_int_aux retry s bound
    | O => v
    end.

(* Note: only call at most one of [split], [random_int], [random_Z], [random_N]
   on a given seed. *)
Definition random_int : state -> int -> int := range_int_aux 5.

(* [0 < bound < 2^63] *)
Definition random_Z (s : state) (bound : Z) : Z :=
  Int63.to_Z (random_int s (Int63.of_Z bound)).

Definition random_N (s : state) (bound : N) : N :=
  Z.to_N (random_Z s (Z.of_N bound)).

Definition random_bool (s : state) : bool :=
  lsb (bits s).
