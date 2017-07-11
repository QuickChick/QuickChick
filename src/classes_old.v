Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat.
Require Import GenLow GenHigh Sets.
Require Import Recdef.
Require Import List.

Require Import ZArith ZArith.Znat Arith.
Import GenLow GenHigh.

(** Instance Hierarchy  

   GenSized 
      |
      |
     Gen   Shrink
       \    /
        \  /
      Arbitrary
*)

(** Generator-related classes *)
Class GenSized (A : Type) :=
  { arbitrarySized : nat -> G A }.

Class Gen (A : Type) := 
  { arbitrary : G A }.

(** Coercion from Sized to plain version *)
Global Instance GenSized__Gen {A} `{GenSized A} : Gen A :=
  {| arbitrary := sized arbitrarySized |}.

(** Shrink class *)
Class Shrink (A : Type) :=
  { shrink : A -> list A }.

(** Arbitrary Class *)
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.

Global Instance arb_gen {A} `{Gen A} `{Shrink A} : Arbitrary A.

(** Sizes of types *)
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

(** Correctness of sized generators *)
Class GenSizeCorrect {A : Type} `{Sized A} (g : nat -> G A) :=
  {
    genSizeCorrect : forall s, semGen (g s) <--> [set x : A | size x <= s ]
  }.

(** Monotonicity of size parametric generators *)
Class GenSizedMonotonic (A : Type) `{H1 : GenSized A}
      `{H2 : forall s, SizeMonotonic (arbitrarySized s)}.

(** Monotonicity of size parametric generators v2 *)
Class GenSizedSizeMotonic (A : Type) `{GenSized A} :=
  {
    sizeMonotonic :
      forall s s1 s2,
        s1 <= s2 ->
        semGenSize (arbitrarySized s1) s 
        \subset semGenSize (arbitrarySized s2) s
  }.

(* Correctness of size parametric generators *)
Class GenSizedCorrect (A : Type) `{Sized A} `{H1 : GenSized A}
      `{@GenSizeCorrect _ _ arbitrarySized}.

Class GenMonotonic (A : Type) `{Arbitrary A}
      `{H2 : @SizeMonotonic _ arbitrary}.

(** Correctness of generators *)
Class GenCorrect (A : Type) (g : G A)  :=
  {
    arbitraryCorrect : semGen g <--> [set : A]
  }.

(* Monotonic and Correct generators *)
Class GenMonotonicCorrect (A : Type)
      `{H1 : Gen A}
      `{GenMonotonic A} `{@GenCorrect A arbitrary}.

Instance GenMonotonicFromSized (A : Type)
         {H1 : GenSized A}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySized s)) }
         {H3 : @GenSizedSizeMotonic A H1} : @SizeMonotonic A arbitrary.
Proof.
  constructor. eapply sizedMonotonic.
  now intros n; eauto with typeclass_instances.
  intros. edestruct H3. eauto.
Qed.

Instance GenCorrectFromSized (A : Type)
         {H1 : GenSized A}
         {Hs : Sized A}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySized s)) }
         {H3 : @GenSizedSizeMotonic A H1}
         {H4 : GenSizeCorrect arbitrarySized} : GenCorrect A arbitrary.
Proof.
  constructor. unfold arbitrary. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
    destruct H3. eauto.
  - setoid_rewrite genSizeCorrect.
    split. intros [n H]. constructor; eauto.
    intros H. eexists; split; eauto.
Qed.

