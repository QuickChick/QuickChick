
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

(** Monotonicity of size parametric generators *)
Class ArbitrarySizedMonotonic (A : Type) `{H1 : ArbitrarySized A}
      `{H2 : forall s, SizeMonotonic (arbitrarySize s)}.

(** Monotonicity of size parametric generators v2 *)
Class ArbitrarySizedSizeMotonic (A : Type) `{ArbitrarySized A} :=
  {
    sizeMonotonic :
      forall s s1 s2,
        s1 <= s2 ->
        semGenSize (arbitrarySize s1) s \subset semGenSize (arbitrarySize s2) s
  }.

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

(* Monotonic and Correct generators *)
Class ArbitraryMonotonicCorrect (A : Type)
      `{H1 : Arbitrary A}
      `{ArbitraryMonotonic A} `{@GenCorrect A arbitrary}.


(** Once we have instances for size parametric generator, we can derive the instances
    for the ones that abstract away from sizes *)

Instance ArbitraryFromSized (A : Type) `{ArbitrarySized A} : Arbitrary A.
Proof.
  constructor. exact (sized arbitrarySize).
  exact (shrinkSize).
Defined.

Instance ArbitraryMonotonicFromSized (A : Type)
         {H1 : ArbitrarySized A}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySize s)) }
         {H3 : @ArbitrarySizedSizeMotonic A H1} : @SizeMonotonic A arbitrary.
Proof.
  constructor. eapply sizedMonotonic.
  now intros n; eauto with typeclass_instances.
  intros. edestruct H3. eauto.
Qed.

Instance ArbitraryCorrectFromSized (A : Type)
         {H1 : ArbitrarySized A}
         {Hs : Sized A}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySize s)) }
         {H3 : @ArbitrarySizedSizeMotonic A H1}
         {H4 : GenSizeCorrect arbitrarySize} : GenCorrect A arbitrary.
Proof.
  constructor. unfold arbitrary, ArbitraryFromSized.
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
    destruct H3. eauto.
  - setoid_rewrite genSizeCorrect.
    split. intros [n H]. constructor; eauto.
    intros H. eexists; split; eauto.
Qed.

(** Foo example *)

(* TODO : prove and move to the appropriate file *)

Lemma nat_set_ind (A : Type) `{Hyp : CanonicalSized A} :
  forall (P : nat -> set A -> Prop),
    (P 0 zeroSized) ->
    (forall (n : nat) s, P n s -> P (n.+1) (succSized s)) ->
    (forall (n : nat), P n [ set x | size x <= n ]).
Proof.
Admitted.

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
  forall (A : Type) (ng : nat * G A) (l : seq (nat * G A)) (size : nat),
    semGenSize (freq ((fst ng, snd ng) ;; l)) size <-->
    \bigcup_(x in (ng :: l)) semGenSize x.2 size.
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

(* kinda slow *)
Lemma singl_set_eq: forall (A : Type) (x : A), [ x ] <--> [ set x ].
Proof.
  intros A x x'; split; intros H.
  - inv H. reflexivity. now inv H0.
  - inv H. now constructor.
Qed.


Instance ArbNatGenCorrect : GenCorrect nat arbitrary.
Proof.
  constructor. now apply arbNat_correct.
Qed.

DeriveArbitrarySized Foo as "ArbSizedFoo".
DeriveSized Foo as "SizedFoo".
DeriveCanonicalSized Foo as "CanonSizedFoo". (* Drop params maybe??? *)
DeriveArbitrarySizedMonotonic Foo as "ArbSizedMonFoo" using "ArbSizedFoo".
DeriveArbitrarySizedCorrect Foo as "ArbCorrMonFoo" using "ArbSizedFoo" and "ArbSizedMonFoo".

Require Import Omega.

Lemma set_incl_trans {A} (s1 s2 s3 : set A) :
  s1 \subset s2 -> s2 \subset s3 -> s1 \subset s3.
Proof.
  now firstorder.
Qed.

Lemma setU_set_incl_compat :
  forall (T : Type) (s1 s2 s1' s2' : set T),
    s1 \subset s1' -> s2 \subset s2' -> s1 :|: s2 \subset s1' :|: s2'.
Proof.
  now firstorder.
Qed.

Lemma incl_bigcupl :
  forall (T U : Type) (A B : set T) (F : T -> set U),
    A \subset B -> \bigcup_(x in A) F x \subset \bigcup_(x in B) F x.
Proof.
  now firstorder.
Qed.

Lemma incl_bigcupr :
  forall (T U : Type) (A : set T) (F G : T -> set U),
    (forall x : T, F x \subset G x) ->
    \bigcup_(x in A) F x \subset \bigcup_(x in A) G x.
Proof. 
  now firstorder. 
Qed.

Lemma incl_bigcup :
  forall (T U : Type) (A B : set T) (F G : T -> set U),
    A \subset B ->
    (forall x : T, F x \subset G x) ->
    \bigcup_(x in A) F x \subset \bigcup_(x in B) G x.
Proof. 
  now firstorder. 
Qed.

Instance ArbSizedSizeMotonicFoo {A B} `{Arbitrary A} `{Arbitrary B} : ArbitrarySizedSizeMotonic (@Foo A B).
Proof.
  constructor. intros s s1 s2.
  revert s1; induction s2; intros s1 Hleq; destruct s1; try ssromega.
  - simpl. firstorder. (* reflexivity for set_incl *)
  - unfold arbitrarySize, ArbSizedFoo.
    rewrite (semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0))))).
    admit. 
  - unfold arbitrarySize, ArbSizedFoo.
    rewrite !(semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0))))).
    rewrite !cons_set_eq.
    rewrite !bigcup_setU_l.
    rewrite !bigcup_set1.
    eapply setU_set_incl_compat.
    now firstorder.

    eapply setU_set_incl_compat.
    rewrite !semBindSize.
    eapply incl_bigcupl.
    now eauto.

    eapply setU_set_incl_compat.
    rewrite !semBindSize.
    eapply incl_bigcupr.
    intros x. rewrite !semBindSize.
    eapply incl_bigcupr.
    intros x1. rewrite !semBindSize.
    eapply incl_bigcupr.
    intros x2. rewrite !semBindSize.
    eapply incl_bigcup. eapply IHs2. eassumption.
    intros x3. rewrite !semBindSize.
    eapply incl_bigcup. eapply IHs2. eassumption.
    intros x4. firstorder. (* refl *)

    eapply setU_set_incl_compat.
    now firstorder.
    now firstorder.
Admitted. 

Typeclasses eauto := debug.

(* Typeclass resolution should be able to derive instances for unsized *)

Definition genFoo {A B : Type } `{H1 : Arbitrary A} `{H2 : Arbitrary B}
           `{H1' : Sized A} `{H2' : Sized B} : G (@Foo A B) := @arbitrary (@Foo A B) _.

Definition corrFoo {A B : Type } `{H1 : ArbitraryMonotonicCorrect A} `{H2 : ArbitraryMonotonicCorrect B}
  := @arbitraryCorrect (@Foo A B) arbitrary.