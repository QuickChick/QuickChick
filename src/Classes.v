Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat.
Require Import Sets GenLow.
Require Import Recdef.
Require Import List.

Require Import ZArith ZArith.Znat Arith.

Import GenLow.

Set Bullet Behavior "Strict Subproofs".

(** Instance Hierarchy  

   GenSized 
      |
      |
     Gen   Shrink
       \    /
        \  /
      Arbitrary
*)

(** * Generator-related classes *)

Class GenSized (A : Type) :=
  { arbitrarySized : nat -> G A }.

Class Gen (A : Type) := 
  { arbitrary : G A }.

(** Shrink class *)
Class Shrink (A : Type) :=
  { shrink : A -> list A }.

(** Arbitrary Class *)
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.

(** * Sizes of types *)
  
Class Sized (A : Type) :=
  {
    size : A -> nat
  }.

Class CanonicalSized (A : Type) `{Sized A} :=
  {
    zeroSized : set A;
    succSized : set A -> set A;

    zeroSized_spec : zeroSized <--> [ set x : A | size x = 0 ];
    succSized_spec :
      forall n, succSized [ set x : A | size x <= n ] <--> [ set x : A | size x <= S n ]
 
  }.

(** * Correctness classes *)

(** Correctness of sized generators *)
Class SizedCorrect {A : Type} `{Sized A} (g : nat -> G A) :=
  {
    arbitrarySizedCorrect : forall s, semGen (g s) <--> [set x : A | size x <= s ]
  }.

(** Correctness of generators *)
Class Correct (A : Type) (g : G A)  :=
  {
    arbitraryCorrect : semGen g <--> [set : A]
  }.

(** * Monotonic generators *)

(** Monotonicity of size parametric generators *)
Class GenSizedMonotonic (A : Type) `{GenSized A}
      `{forall s, SizeMonotonic (arbitrarySized s)}.

(** Monotonicity of size parametric generators v2 *)
Class GenSizedSizeMonotonic (A : Type) `{GenSized A} `{SizedMonotonic A arbitrarySized}.

Class GenMonotonic (A : Type) `{Gen A} `{SizeMonotonic A arbitrary}.

(** * Correct generators *)

Class GenSizedCorrect (A : Type) `{GenSized A} `{SizedCorrect A arbitrarySized}.

Class GenCorrect (A : Type) `{Gen A} `{Correct A arbitrary}.
 
(* Monotonic and Correct generators *)
Class GenMonotonicCorrect (A : Type)
      `{Gen A} `{SizeMonotonic A arbitrary} `{Correct A arbitrary}.

(** Coercions *)
  
Instance GenSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : forall s, @SizeMonotonic A (arbitrarySized s))
: @GenSizedMonotonic A Hgen Hmon.
  
Instance GenMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Gen A) (Hmon : @SizeMonotonic A arbitrary)
: @GenMonotonic A Hgen Hmon.

Instance GenSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : GenSized A) `{Hcor : SizedCorrect A arbitrarySized}
: @GenSizedCorrect A Hgen _ Hcor.

Instance GenCorrectOfCorrect
         (A : Type) (Hgen : Gen A) `{Hcor : Correct A arbitrary}
: @GenCorrect A Hgen Hcor.

Instance GenSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : @SizedMonotonic A arbitrarySized)
: @GenSizedSizeMonotonic A Hgen Hmon.

(* Zoe : Is global really needed here? *)
Global Instance GenOfGenSized {A} `{GenSized A} : Gen A :=
  {| arbitrary := sized arbitrarySized |}.

Global Instance ArbitraryOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A.

Generalizable Variables PSized PMon PSMon PCorr.

Instance GenMonotonicOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H PSMon}
: GenMonotonic A.

Instance GenCorrectOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H PSMon}
         `{@GenSizedCorrect A H PSized PCorr} : Correct A arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
    destruct PSMon. eauto.
  - setoid_rewrite arbitrarySizedCorrect.
    split. intros [n H3]. constructor; eauto.
    intros H4. eexists; split; eauto.
Qed.
