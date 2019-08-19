
From Coq Require Import Int63.
From QuickChick Require Import Int64 Prng.

Definition state0 : state := Prng.of_seed 42.

Definition next : state -> state * int * int :=
  fun s =>
    let (s, s') := split s in
    let n := bits s' in
    let i := Int64.to_int (n >> 32) in
    let j := Int64.to_int (n land "FFFF_FFFF"%int64_hex) in
    (s, i, j).

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOCamlInt63.

Extraction "rand.ml" state0 next.
