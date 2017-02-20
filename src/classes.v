
Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import GenLow GenHigh Tactics Sets Arbitrary.
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
(* BCP: Rename: ArbitraryOfSize? Sth else? *)
Class ArbitrarySized (A : Type) :=
  {
    arbitrarySize : nat -> G A;
    (* BCP: You might not want the same notion of size for generation and srhinking Load -> Noop *)
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
  forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)) (size : nat),
    semGenSize (freq ((fst ng, snd ng) ;; l)) size <-->
    \bigcup_(x in (ng :: l)) semGenSize x.2 size.
Admitted.

Definition monotonicGen {A} (gen : G A) :=
  forall s1 s2 : nat,
    s1 <= s2 ->
    semGenSize gen s1 \subset semGenSize gen s2.


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

Lemma oneOf_freq {A} (g : G A) (gs : list (G A)) size :
  semGenSize (oneOf (g ;; gs)) size <-->
  semGenSize (freq ((1, g) ;; map (fun x => (1, x)) gs)) size.  
Admitted.

Lemma incl_subset {A : Type} (l1 l2 : seq A) :
  incl l1 l2 -> l1 \subset l2.
Proof.
  intros Hi x; eapply Hi.
Qed.

Lemma incl_hd_same {A : Type} (a : A) (l1 l2 : seq A) :
  incl l1 l2 -> incl (a :: l1) (a :: l2).
Proof.
  intros Hin. firstorder.
Qed.

Lemma subset_respects_set_eq :
  forall {T : Type} {s1 s2 s1' s2' : set T},
    s1 <--> s1' ->
    s2 <--> s2' ->
    s1' \subset s2' ->
    s1 \subset s2.
Proof.
  firstorder.
Qed.

Definition impl (A B : Prop) : Prop := A -> B.
Definition all (A : Type) (f : A -> Prop) : Prop := forall (x : A), f x.
