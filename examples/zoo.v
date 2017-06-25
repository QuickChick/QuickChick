From QuickChick Require Import QuickChick Tactics.
Require Import String List. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import Classes QcDefaultNotation ListNotations.
(* XXX this is required because there is a name clash with
 * size (seq A -> nat) and size of types *)

(* Example *)
Inductive Zoo (A : Type) {B : Type}: Type :=
| Zoo1 : A -> Zoo A
| Zoo2 : Zoo A -> Zoo A
| Zoo3 : nat -> A -> B -> Zoo A -> Zoo A -> Zoo A
| Zoo4 : Zoo A.

Instance frequencySizeMonotonic_alt 
: forall {A : Type} (g0 : G A) (lg : seq (nat * G A)),
    SizeMonotonic g0 ->
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (frequency g0 lg).
Admitted.

Lemma semFreq :
  forall (A : Type) (ng : nat * G A) (l : seq (nat * G A)),
    semGen (freq ((fst ng, snd ng) ;; l)) <-->
    \bigcup_(x in (ng :: l)) semGen x.2.
Admitted.

Lemma semFreqSize :
  forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)) (size : nat),
    semGenSize (freq ((fst ng, snd ng) ;; l)) size <-->
    \bigcup_(x in (ng :: l)) semGenSize x.2 size.
Admitted.

Lemma oneOf_freq {A} (g : G A) (gs : list (G A)) size :
  semGenSize (oneOf (g ;; gs)) size <-->
  semGenSize (freq ((1, g) ;; map (fun x => (1, x)) gs)) size.  
Admitted.

Definition all (A : Type) (f : A -> Prop) : Prop := forall (x : A), f x.

Lemma nat_set_ind (A : Type) `{Hyp : CanonicalSized A} :
  forall (P : nat -> set A -> Prop),
    (P 0 zeroSized) ->
    (forall (n : nat) s, P n s -> P (n.+1) (succSized s)) ->
    (forall (n : nat), P n [ set x | size x <= n ]).
Proof.
Admitted.

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

Derive SizeMonotonic for Zoo using genSZoo.
(*
SizeMonotonicZoo is defined
*)

Derive SizedMonotonic for Zoo.
(*
SizedMonotonicZoo is defined
*)

Derive SizedCorrect for Zoo using genSZoo and SizeMonotonicZoo.
(*
SizedCorrectZoo is defined
*)

(** * Abstract away form size *)

(** Automatically derive generator... *)
Definition genZoo {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B}
           `{H1' : Sized A} `{H2' : Sized B} : G (@Zoo A B) := @arbitrary (@Zoo A B) _.

(* Program Instance LalaG {A B} : Gen (@Zoo A B). *)

(* Instance Lala  {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B} *)
(*          `{H1' : Sized A} `{H2' : Sized B} *)
(*          `{H1 : GenMonotonicCorrect A} `{H2 : GenMonotonicCorrect B}: *)
(*   Correct (@Zoo A B) arbitrary. *)
(* Proof. *)
(*   refine (@GenCorrectOfSized _ _ _ _ _ _ _ _ _). *)
(*   eauto with typeclass_instances. *)
(*   eauto with typeclass_instances. *)
  
(*   eauto with typeclass_instances. *)
  
(*   {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B}.z *)
(*   eapply  *)
 

(** ... and correctness proof *)

Definition corrZoo {A B : Type} `{GenMonotonicCorrect A} `{GenMonotonicCorrect B}
            `{CanonicalSized A} `{CanonicalSized B} := @arbitraryCorrect (@Zoo A B) arbitrary _.
