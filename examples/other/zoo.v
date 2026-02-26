From QuickChick Require Import QuickChick Tactics.
Require Import String List. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Import Classes QcDefaultNotation ListNotations.
(* XXX this is required because there is a name clash with
 * size (seq A -> nat) and size of types *)

(* Example *)
Inductive Zoo (A : Type) {B : Type}: Type :=
| Zoo1 : A -> Zoo A
| Zoo2 : Zoo A -> Zoo A
| Zoo3 : nat -> A -> B -> Zoo A -> Zoo A -> Zoo A
| Zoo4 : Zoo A.

(** Generators for type  *)
Derive Instance Arbitrary for Zoo.
(* 
genSZoo is defined
shrZoo is defined
*)

(** Size of type *)
Derive Instance Sized for Zoo.
(*
SizedZoo is defined
*)

(** Size equations *)
Derive Instance CanonicalSized for Zoo.
(*
CanonicalSizedZoo is defined
 *)

Derive Instance SizeMonotonic for Zoo using genSZoo.
(*
SizeMonotonicZoo is defined
 *)

Derive Instance SizedMonotonic for Zoo.

(*
SizedMonotonicZoo is defined
*)

Derive Instance SizedCorrect for Zoo using genSZoo and SizeMonotonicZoo.
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
