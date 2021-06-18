Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Classes.Morphisms.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat.
Require Import Sets Tactics.
Require Import Recdef.
Require Import List.

Require Import ZArith ZArith.Znat Arith.

Require Import Producer Generators Enumerators.

Set Bullet Behavior "Strict Subproofs".

(** Apply a function n times *)
Fixpoint appn {A} (f : A -> A) (n : nat) : A ->  A :=
  fun x =>
    match n with
      | 0%nat => x
      | S n' => f (appn f n' x)
    end.

Infix "^" := appn (at level 30, right associativity) : fun_scope.


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

(* begin gen_sized_class *)
Class GenSized (A : Type) :=
  { arbitrarySized : nat -> G A }.
(* end gen_sized_class *)

(* begin gen_class *)
Class Gen (A : Type) := { arbitrary : G A }.
(* end gen_class *)

(** Shrink class *)
Class Shrink (A : Type) :=
  { shrink : A -> list A }.

(** Arbitrary Class *)
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.

Class EnumSized (A : Type) := { enumSized : nat -> E A }.
  
Class Enum (A : Type) := { enum : E A }.

(** * Sizes of types *)
  
Class Sized (A : Type) :=
  { size : A -> nat }.

Class CanonicalSized (A : Type) `{Sized A} :=
  {
    zeroSized : set A;
    succSized : set A -> set A;

    zeroSized_spec : zeroSized <--> [ set x : A | size x = 0 ];
    succSized_spec :
      forall n, succSized [ set x : A | size x <= n ] <--> [ set x : A | size x <= S n ]
 
  }.

Lemma size_ind (A : Type) `{Hyp : Sized A} :
  forall (P : A -> Prop), (forall y, (forall x, size x < size y -> P x) -> P y) -> (forall x, P x).
Proof.
  intros P H1.
  intros x.
  assert (Hin : [ set y :  A | size y <= size x] x); eauto.
  revert Hin.
  generalize (size x). intros n.
  revert x. induction n.
  - intros x Hl. apply H1. intros x1 Hlt. ssromega.
  - intros x Hleq. eapply H1. intros x1 Hlt.
    eapply IHn. ssromega.
Qed.

Lemma size_lfp (A : Type) `{Hyp : CanonicalSized A} :
  [set x : A | True ] <--> \bigcup_(s : nat) [set x : A | size x <= s ].
Proof.
  intros a; split; eauto. intros _.
  exists (size a). split; eauto. constructor.
Qed.

Lemma succ_lfp (A : Type) `{Hyp : CanonicalSized A}
      `{Proper _ (respectful set_eq set_eq) succSized} s :
  [set x : A | size x <= s ] <-->  (succSized ^ s) zeroSized.
Proof.
  induction s.
  simpl.
  - rewrite zeroSized_spec.
    split; intros; ssromega.
  - simpl. rewrite <- succSized_spec.
    rewrite IHs. reflexivity.
Qed.

(* Lemma succ_lfp' (A : Type) `{Hyp : CanonicalSized A} : *)
(*   \bigcup_(s : nat)  (succSized ^ s) zeroSized <--> [ set x : A | True ]. *)
(* Proof. *)
(*   intros. split; eauto. *)
(*   intros _. *)
(*   eapply set_eq_trans. *)
(*   Focus 2. symmetry. *)
(*   eapply succ_lfp. *)
(*   simpl.  *)
(*   rewrite succ_lfp at 2. *)
(* split. *)
(*     split. rewrite IHs. firstorder. *)
(*     IHs. *)
(*   firstorder. reflexivity. split; intros; eauto. *)
(*   exists (size a). *)
(*   remember (size a) as s. *)
(*   revert a Heqs. induction s; intros. *)
(*   - split. constructor. *)
(*     simpl. eapply zeroSized_spec. now eauto. *)
(*   - split. constructor. *)
(*     simpl. *)
(*     eapply (succSized_spec. *)
(*     eassumption. *)
(*   eapply size_ind. *)
  
(*   [set x : A | True ] <-->  . *)

(** * Correctness classes *)

(** Correctness of sized generators *)
Class SizedCorrect {A : Type} `{Sized A} {G} `{Producer G}
      (g : nat -> G A) :=
  {
    prodSizedCorrect : forall s, semProd (g s) <--> [set x : A | size x <= s ]
  }.

Class CorrectSized {A : Type} {G} `{Producer G} (g : nat -> G A)  :=
  { prodCorrectSized :
      [ set n | exists s, semProd (g s) n ] <--> [set : A]
  }.


(** Correctness of generators *)
Class Correct (A : Type) {G} `{Producer G} (g : G A)  :=
  {
    prodCorrect : semProd g <--> [set : A]
  }.

(** * Monotonic generators *)

(** Monotonicity of size parametric generators *)
Class GenSizedMonotonic (A : Type) `{GenSized A}
      `{forall s, SizeMonotonic (arbitrarySized s)}.

(** Monotonicity of size parametric generators v2 *)
Class GenSizedSizeMonotonic (A : Type) `{GenSized A}
        `{SizedMonotonic A G arbitrarySized}.

Class GenMonotonic (A : Type) `{Gen A} `{SizeMonotonic A G arbitrary}.

(** Monotonicity of size parametric generators *)
Class EnumSizedMonotonic (A : Type) `{EnumSized A}
      `{forall s, @SizeMonotonic A E ProducerEnum (enumSized s)}.

(** Monotonicity of size parametric generators v2 *)
Class EnumSizedSizeMonotonic (A : Type) `{EnumSized A}
        `{@SizedMonotonic A E ProducerEnum enumSized}.

Class EnumMonotonic (A : Type) `{Enum A}
        `{@SizeMonotonic A E ProducerEnum enum}.
  
(** * Correct generators *)

Class GenSizedCorrect (A : Type) `{Sized A} `{GenSized A}
      `{@SizedCorrect A _ G ProducerGen arbitrarySized}.

Class GenCorrect (A : Type) `{Gen A}
        `{@Correct A G ProducerGen arbitrary}.
 
(* Monotonic and Correct generators *)
Class GenMonotonicCorrect (A : Type)
      `{Gen A}
      `{@SizeMonotonic A G ProducerGen arbitrary}
      `{@Correct  A G ProducerGen arbitrary}.

Class EnumSizedCorrect (A : Type) `{Sized A}
        `{EnumSized A} `{@SizedCorrect A _ E ProducerEnum enumSized}.

Class EnumCorrect (A : Type) `{Enum A}
        `{@Correct A E ProducerEnum enum}.
 
(* Monotonic and Correct generators *)
Class EnumMonotonicCorrect (A : Type)
      `{Enum A}
      `{@SizeMonotonic A E ProducerEnum enum}
      `{@Correct A E ProducerEnum enum}.

  
(** Coercions *)
  
Instance GenSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : forall s, @SizeMonotonic A G ProducerGen (arbitrarySized s))
: @GenSizedMonotonic A Hgen Hmon := {}.
  
Instance GenMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Gen A) (Hmon : @SizeMonotonic A G ProducerGen arbitrary)
: @GenMonotonic A Hgen ProducerGen Hmon := {}.

Instance GenSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : GenSized A)
         {HS : Sized A}
         `{Hcor : @SizedCorrect A HS G ProducerGen arbitrarySized}
: @GenSizedCorrect A HS Hgen Hcor := {}.

Instance GenCorrectOfCorrect
         (A : Type) (Hgen : Gen A)
         `{Hcor : @Correct A G ProducerGen arbitrary}
: @GenCorrect A Hgen Hcor := {}.

Instance GenSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : @SizedMonotonic A G ProducerGen arbitrarySized)
: @GenSizedSizeMonotonic A Hgen ProducerGen Hmon := {}.

Global Instance GenOfGenSized {A} `{GenSized A} : Gen A :=
  {| arbitrary := sized arbitrarySized |}.

Global Instance ArbitraryOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A := {}.

Generalizable Variables PSized PMon PSMon PCorr.

Instance GenMonotonicOfSized (A : Type)
         `{H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H ProducerGen PSMon}
  : @GenMonotonic A
                  (@GenOfGenSized A H) ProducerGen 
                  (@sizedSizeMonotonic G ProducerGen _ A
                                       (@arbitrarySized A H)
                                       PMon PSMon) := {}.

Instance GenCorrectOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H ProducerGen PSMon}
         `{@GenSizedCorrect A PSized H PCorr} : Correct A arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
  - setoid_rewrite prodSizedCorrect.
    split. intros [n H3]. constructor; eauto.
    intros H4. eexists; split; eauto.
Qed.

Lemma nat_set_ind (A : Type) `{GenSized A} `{Hyp : CanonicalSized A} :
  (semProd (arbitrarySized 0) <--> zeroSized) ->
  (forall (s : nat) (elems : set A),
     semProd (arbitrarySized s) <--> elems ->
     semProd (arbitrarySized (s.+1)) <--> succSized elems) ->
  (forall s : nat, semProd (arbitrarySized s) <--> (fun x : A => size x <= s)).
Proof.
  intros HO IH. intros n; induction n.
  - eapply set_eq_trans with (B := (fun x : A => size x = 0)).
    rewrite -zeroSized_spec //=.
    intros s. destruct (size s). now firstorder.
    split; intros; ssromega.
  - rewrite -succSized_spec. eauto.
Qed.

Instance EnumSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : EnumSized A) (Hmon : forall s, @SizeMonotonic A E ProducerEnum (enumSized s))
: @EnumSizedMonotonic A Hgen Hmon := {}.
  
Instance EnumMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Enum A) (Hmon : @SizeMonotonic A E ProducerEnum enum)
: @EnumMonotonic A Hgen Hmon := {}.

Instance EnumSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : EnumSized A)
         {HS : Sized A}
         `{Hcor : @SizedCorrect A HS E ProducerEnum enumSized}
: @EnumSizedCorrect A HS Hgen Hcor := {}.

Instance EnumCorrectOfCorrect
         (A : Type) (Hgen : Enum A)
         `{Hcor : @Correct A E ProducerEnum enum}
: @EnumCorrect A Hgen Hcor := {}.

Instance EnumSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : EnumSized A) (Hmon : @SizedMonotonic A E ProducerEnum enumSized)
: @EnumSizedSizeMonotonic A Hgen Hmon := {}.

Global Instance EnumOfEnumSized {A} `{EnumSized A} : Enum A :=
  {| enum := sized enumSized |}.

(*
Global Instance EnumOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A := {}.
 *)

Instance EnumMonotonicOfSized (A : Type)
         `{H : EnumSized A}
         `{@EnumSizedMonotonic A H PMon}
         `{@EnumSizedSizeMonotonic A H PSMon}
  : @EnumMonotonic A
                  (@EnumOfEnumSized A H)
                  (@sizedSizeMonotonic E ProducerEnum _ A
                                       (@enumSized A H)
                                       PMon PSMon) := {}.

Instance EnumCorrectOfSized (A : Type)
         {H : EnumSized A}
         `{@EnumSizedMonotonic A H PMon}
         `{@EnumSizedSizeMonotonic A H PSMon}
         `{@EnumSizedCorrect A PSized H PCorr} : Correct A enum.
Proof.
  constructor. unfold arbitrary, EnumOfEnumSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
  - setoid_rewrite prodSizedCorrect.
    split. intros [n H3]. constructor; eauto.
    intros H4. eexists; split; eauto.
Qed.

Lemma nat_set_ind_enum (A : Type) `{EnumSized A} `{Hyp : CanonicalSized A} :
  (semProd (enumSized 0) <--> zeroSized) ->
  (forall (s : nat) (elems : set A),
     semProd (enumSized s) <--> elems ->
     semProd (enumSized (s.+1)) <--> succSized elems) ->
  (forall s : nat, semProd (enumSized s) <--> (fun x : A => size x <= s)).
Proof.
  intros HO IH. intros n; induction n.
  - eapply set_eq_trans with (B := (fun x : A => size x = 0)).
    rewrite -zeroSized_spec //=.
    intros s. destruct (size s). now firstorder.
    split; intros; ssromega.
  - rewrite -succSized_spec. eauto.
Qed.
