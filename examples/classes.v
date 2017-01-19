
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

 
(** Correctness of size parametric generators *)
Class ArbitrarySizedCorrect (A : Type) `{Sized A} `{ArbitrarySized A} :=
  {
    arbitrarySizeCorrect :
      forall s, semGen (arbitrarySize s) <--> [ set x : A | size x <= s ] 
  }.


Class ArbitraryMonotonic (A : Type) `{H1 : Arbitrary A}
      `{H2 : @SizeMonotonic _ arbitrary}.


(** Correctness of generators *)
Class ArbitraryCorrect (A : Type) `{Arbitrary A}  :=
  {
    arbitraryCorrect : semGen arbitrary <--> [set : A]
  }.


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

DeriveArbitrarySized Foo as "arbSizedFoo".
DeriveSized Foo as "SizedFoo".
DeriveCanonicalSized Foo as "CanonSizedFoo".

Typeclasses eauto := debug.

(* Derives :

Instance arbFooArbitrarySizedGenMonotonic {A B : Type}
         `{H1 : ArbitraryMonotonic A}
         `{H2 : ArbitraryMonotonic B}
         (s : nat)
        : SizeMonotonic (@arbitrarySize (@Foo A B) arbSizedFoo s).

Needs the arbitrarySized instance to be specified.

*)

DeriveArbitrarySizedMonotonic Foo as "ArbSizedMonFoo" using "arbSizedFoo".


Lemma arbFooCorrectSized {A B : Type} `{H1 : Arbitrary A} `{H2 : Arbitrary B}
      `{H1' : Sized A} `{H2' : Sized B} s :
  semGen (arbitrarySize s) <--> [set foo : @Foo A B | size foo <= s].
Proof.
Admitted.
(*   revert size. *)
(*   specialize (@size_ind Foo _ (fun n s => semGen (arbFooSized n) <--> s)). *)
(*   intros Hyp. eapply Hyp; clear Hyp. *)
(*   - eapply (semReturn Foo1). *)
(*   - intros n s IH. *)
(*     (* Frequency and some normalization of the sets *) *)
(*     simpl. refine (set_eq_trans (semFrequency _ _) _). simpl. *)
(*     eapply set_eq_trans. *)
(*     + refine (set_eq_trans (eq_bigcupl _ _ (set_eq_trans (cons_set_eq _ _) *)
(*                                                          (setU_set_eq_compat (set_eq_refl [set (1, returnGen Foo1)]) *)
(*                                                                              (set_eq_trans (cons_set_eq _ _) *)
(*                                                                                            (setU_set_eq_compat (set_eq_refl _) *)
(*                                                                                                                (set_eq_trans *)
(*                                                                                                                   (cons_set_eq _ []) *)
(*                                                                                                                   (setU_set0_neut _))))))) *)
(*                            (set_eq_trans (bigcup_setU_l _ _ _) (setU_set_eq_compat (bigcup_set1 _ _) *)
(*                                                                                    (set_eq_trans (bigcup_setU_l _ _ _) (setU_set_eq_compat (bigcup_set1 _ _)  *)
(*                                                                                                                                            (bigcup_set1 _ _)))))). *)
(*     + refine (setU_set_eq_compat (semReturn Foo1) (setU_set_eq_compat _ _)). *)
(*       * refine *)
(*          (set_eq_trans (@semBindSizeMonotonic _ _ _ _ _ _) (set_eq_trans (eq_bigcupl _ _ IH) (eq_bigcupr _ (fun x => semReturn _)))). *)
(*         admit. (* It should be able to infer it *) *)
(*       * simpl. *)
(*         refine *)
(*           (set_eq_trans (@semBindSizeMonotonic _ _ _ _ _ _) _); eauto with typeclass_instances. *)
(*         admit. *)
(*         refine (set_eq_trans *)
(*                   (eq_bigcupl _ _ arbNat_correct) *)
(*                   (eq_bigcupr _ *)
(*                               (fun n => *)
(*                                  set_eq_trans (@semBindSizeMonotonic _ _ _ _ _ _) *)
(*                                               (set_eq_trans *)
(*                                                  (eq_bigcupl _ _ IH) *)
(*                                                  (eq_bigcupr _ *)
(*                                                              (fun x => set_eq_trans (@semBindSizeMonotonic _ _ _ _ _ _) *)
(*                                                                                  (set_eq_trans *)
(*                                                                                     (eq_bigcupl _ _ IH) *)
(*                                                                                     (eq_bigcupr _ (fun x => semReturn _))))))))). *)
(*         admit. *)
(*         admit. *)
(*         admit. *)
(* Admitted. *)

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