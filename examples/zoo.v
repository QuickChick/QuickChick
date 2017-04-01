From QuickChick Require Import QuickChick Tactics.
Require Import String List. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import Classes.
(* XXX this is required because there is a name clash with
 * size (seq A -> nat) and size of types *)

(* Example *)
Inductive Zoo (A : Type) {B : Type}: Type :=
| Zoo1 : A -> Zoo A
| Zoo2 : Zoo A -> Zoo A
| Zoo3 : nat -> A -> B -> Zoo A -> Zoo A -> Zoo A
| Zoo4 : Zoo A.


(** Generators for type  *)
Derive Arbitrary for Zoo.
(* 
genSZoo is defined
shrZoo is defined
*)

(** Size of type *)
Derive Sized for Zoo.
(*
SizedZoo is defined
*)

(** Size equations *)
Derive CanonicalSized for Zoo.
(*
CanonicalSizedZoo is defined
 *)

Derive SizeMonotonic for Zoo.

  as "ArbSizedMonZoo" using "ArbSizedZoo".
(** ArbitrarySize correct *)
(* kinda slow - Note that it's the type checking that takes time not the term generation *)
DeriveArbitrarySizedCorrect Zoo as "ArbCorrMonZoo" using "ArbSizedZoo" and "ArbSizedMonZoo".
(** Size monotonicity proof, to abstract away from sizes *)
(* even more slow *)
DeriveArbitrarySizedSizeMonotonic Zoo as "ArbSizedSMonZoo".

(** * Abstract away form size *)

(** Automatically derive generator... *)
Definition genZoo {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B}
           `{H1' : Sized A} `{H2' : Sized B} : G (@Zoo A B) := @arbitrary (@Zoo A B) _.

(** ... and correctness proof *)
Definition corrZoo {A B : Type} `{H1 : ArbitraryMonotonicCorrect A} `{H2 : ArbitraryMonotonicCorrect B}
  := @arbitraryCorrect (@Zoo A B) arbitrary.