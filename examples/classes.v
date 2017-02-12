
From QuickChick Require Import QuickChick Tactics.

Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Open Scope string.

Set Bullet Behavior "Strict Subproofs".

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

Lemma size_ind' (A : Type) `{Hyp : CanonicalSized A} :
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

Lemma set_ind (A : Type) `{Hyp : CanonicalSized A} :
  forall (P : A -> Prop),
    (forall (x : A), zeroSized x -> P x) ->
    (forall (s : set A), (forall y, s y -> P y) -> (forall x, succSized s x -> P x)) ->
    (forall (x : A), P x).
Proof.
  intros P H0 HS. eapply size_ind'; eauto.
  intros y IH. destruct (size y) eqn:Heq.
  - eapply H0. eapply zeroSized_spec. ssromega.
  - eapply (HS [ set y : A | size y <= n]).
    intros y1 Hleq. apply IH. ssromega.
    eapply succSized_spec. ssromega.
Qed.

(** Size parametric generators *)
Class ArbitrarySized (A : Type) :=
  {
    arbitrarySize : nat -> G A;
    shrinkSize : A -> list A
  }.

(** Correctness of sized generators *)
Class GenSizeCorrect {A : Type} `{Sized A} (g : nat -> G A) :=
  {
    genSizeCorrect : forall s, semGen (g s) <--> [set x : A | size x <= s ]
  }.

(* Not used so far *)
Class ArbitrarySizedMonotonic (A : Type) `{H1 : ArbitrarySized A}
      `{H2 : forall s, SizeMonotonic (arbitrarySize s)}.

(* (** Monotonicity of size parametric generators *) *)
(* Class ArbitrarySizedMotonic (A : Type) `{ArbitrarySized A} := *)
(*   { *)
(*     monotonic : *)
(*       forall s s1 s2, *)
(*         s1 <= s2 -> *)
(*         semGenSize (arbitrarySize s1) s \subset semGenSize (arbitrarySize s2) s *)
(*   }. *)


(* Correctness of size parametric generators *)
Class ArbitrarySizedCorrect (A : Type) `{Sized A} `{H1 : ArbitrarySized A}
      `{@GenSizeCorrect _ _ arbitrarySize}.


Class ArbitraryMonotonic (A : Type) `{Arbitrary A}
      `{H2 : @SizeMonotonic _ arbitrary}.

(** Correctness of generators *)
Class GenCorrect (A : Type) (g : G A)  :=
  {
    arbitraryCorrect : semGen g <--> [set : A]
  }.

Class ArbitraryMonotonicCorrect (A : Type)
      `{H1 : Arbitrary A} `{ArbitraryMonotonic A}
      `{@GenCorrect _ arbitrary}.
  
(** Foo example *)

(* TODO : prove and move to the appropriate file *)
Instance frequencySizeMonotonic_alt 
: forall {A : Type} (g0 : G A) (lg : seq (nat * G A)),
    SizeMonotonic g0 ->
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (frequency g0 lg).
Admitted.


Definition monotonicGen {A} (gen : G A) :=
  forall s1 s2 : nat,
    s1 <= s2 ->
    semGenSize gen s1 \subset semGenSize gen s2.

Inductive Foo (A : Type) {B : Type}: Type :=
| Foo1 : A -> Foo A
| Foo2 : Foo A -> Foo A
| Foo3 : nat -> A -> B -> Foo A -> Foo A -> Foo A
| Foo4 : Foo A.

DeriveArbitrarySized Foo as "ArbSizedFoo".
DeriveSized Foo as "SizedFoo". (* Drop params maybe??? *)
DeriveCanonicalSized Foo as "CanonSizedFoo". (* Drop params maybe??? *)

(* Derives :

Instance arbFooArbitrarySizedGenMonotonic {A B : Type}
         `{H1 : ArbitraryMonotonic A}
         `{H2 : ArbitraryMonotonic B}
         (s : nat)
        : SizeMonotonic (@arbitrarySize (@Foo A B) arbSizedFoo s).

Needs the arbitrarySized instance to be specified.

*)

DeriveArbitrarySizedMonotonic Foo as "ArbSizedMonFoo" using "ArbSizedFoo".


Lemma nat_set_ind (A : Type) `{Hyp : CanonicalSized A} :
  forall (P : nat -> set A -> Prop),
    (P 0 zeroSized) ->
    (forall (n : nat) s, P n s -> P (n.+1) (succSized s)) ->
    (forall (n : nat), P n [ set x | size x <= n ]).
Proof.
Admitted.

Lemma singl_set_eq: forall (A : Type) (x : A), [ x ] <--> [ set x ].
Proof.
  intros A x x'; split; intros H.
  - inv H. reflexivity. now inv H0.
  - inv H. now constructor.
Qed.

Lemma semFreq :
  forall (A : Type) (ng : nat * G A) (l : seq (nat * G A)),
    semGen (freq ((fst ng, snd ng) ;; l)) <-->
    \bigcup_(x in (ng :: l)) semGen x.2.
Admitted.

Instance ArbNatGenCorrect : GenCorrect nat arbitrary.
Proof.
  constructor. now apply arbNat_correct.
Qed.

Typeclasses eauto := debug.


DeriveArbitrarySizedCorrect Foo as "ArbCorrMonFoo" using "ArbSizedFoo" and "ArbSizedMonFoo".


Instance FooArbitrarySizedCorrect {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B}
         `{H1' : Sized A} `{H2' : Sized B} : (@ArbitrarySizedCorrect (@Foo A B) _ _). 
Proof.
  constructor. exact arbFooCorrectSized.
Qed.

Instance ArbitraryFromSized (A : Type) `{ArbitrarySized A} : Arbitrary A.
Proof.
  constructor. exact (sized arbitrarySize).
  exact (shrinkSize).
Defined.

(* Instance ArbitraryMonotonicFromSized (A : Type) *)
(*          {H1 : ArbitrarySized A} *)
(*          {H2 : @ArbitrarySizedGenMonotonic A H1} *)
(*          {H3 : @ArbitrarySizedMotonic A H1} : @ArbitraryMotonic A _. *)
(* Proof. *)
(*   constructor. eapply sizedMonotonic. *)
(*   intros n; eauto with typeclass_instances. *)
(*   edestruct H3. eauto. *)
(* Qed. *)

(* Instance FooArbitrarySizedM {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B} *)
(*          `{H1' : Sized A} `{H2' : Sized B} : @ArbitrarySizedMotonic (@Foo A B) _. *)
(* Proof. *)
(*   constructor. intros. *)
(*   (* we need proof for that *) *)
(* Admitted. *)

(* Instance ArbitraryCorrectFromSized (A : Type) *)
(*          {H1 : ArbitrarySized A} *)
(*          {Hs : Sized A} *)
(*          {H2 : @ArbitrarySizedMotonic A H1} *)
(*          {H3 : @ArbitrarySizedGenMonotonic A H1} *)
(*          {H4 : @ArbitrarySizedCorrect A Hs H1} : @ArbitraryCorrect A _. *)
(* Proof. *)
(*   constructor. unfold arbitrary, ArbitraryFromSized. *)
(*   eapply set_eq_trans. *)
(*   - eapply semSized_alt; eauto with typeclass_instances. *)
(*     destruct H2. eauto. *)
(*   - setoid_rewrite arbitrarySizeCorrect. *)
(*     split. intros [n H]. constructor; eauto. *)
(*     intros H. eexists; split; eauto. *)
(* Qed. *)

(* Typeclasses eauto := debug. *)

(* Definition goodArbFoo {A B} `{H1 : Arbitrary A} `{H2 : Arbitrary B} *)
(*          `{H1' : Sized A} `{H2' : Sized B} : Arbitrary (@Foo A B) := @ArbitraryFromSized (@Foo A B) _. *)

(* Definition correct {A B} `{H1 : Arbitrary A} `{H2 : Arbitrary B} *)
(*            `{H1' : Sized A} `{H2' : Sized B} := *)
(*   @arbitraryCorrect (@Foo A B) goodArbFoo _. *)