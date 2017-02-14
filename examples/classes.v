
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

Instance ArbSizedSizeMotonicFoo {A B} `{Arbitrary A} `{Arbitrary B} : ArbitrarySizedSizeMotonic (@Foo A B).
Proof.
  constructor.
  refine
    (fun s =>
       nat_ind
         _
         (nat_ind
            _
            (fun Hleq => @subset_refl _ _)
            (fun s2 IHs2 Hleq => _))
         (fun s1 IHs2 =>
            (nat_ind
               _
               (fun Hleq =>
                  (False_ind _ (lt0_False Hleq)))
               (fun s2 IHs2 Hleq =>
                  _)
            )
         )
    ).
  - refine (subset_respects_set_eq_l
              (oneOf_freq _ _ _) _).
    refine (subset_respects_set_eq_l
                 (semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0)))) _ _)
                 (subset_respects_set_eq_r
                    (semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0)))) _ _)
                    (incl_bigcupl
                       (incl_subset
                          _ _ (incl_hd_same
                                 _ _ _ (incl_tl
                                          _ (incl_tl
                                               _ (incl_hd_same
                                                    _ _ _ (incl_refl _))))))))).
  - refine (subset_respects_set_eq_l
                 (semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0)))) _ _)
                 (subset_respects_set_eq_r
                    (semFreqSize _ ((1, bindGen arbitrary (fun p0 : A => returnGen (Foo1 A p0)))) _ _) _)).
    refine (subset_respects_set_eq_l
              (eq_bigcupl _ _ (cons_set_eq _ _))
              (subset_respects_set_eq_r
                 (eq_bigcupl _ _ (cons_set_eq _ _))
                 _)
           ).
    refine (subset_respects_set_eq_l
              (bigcup_setU_l _ _ _)
              (subset_respects_set_eq_r
                 (bigcup_setU_l _ _ _)
                 _)
           ).

    refine (setU_set_subset_compat (@subset_refl _ _) _).

    refine (subset_respects_set_eq_l
              (eq_bigcupl _ _ (cons_set_eq _ _))
              (subset_respects_set_eq_r
                 (eq_bigcupl _ _ (cons_set_eq _ _))
                 _)
           ).
    refine (subset_respects_set_eq_l
              (bigcup_setU_l _ _ _)
              (subset_respects_set_eq_r
                 (bigcup_setU_l _ _ _)
                 _)
           ).
    refine (setU_set_subset_compat _ _).


    refine (subset_respects_set_eq_l
              (bigcup_set1 _ _)
              (subset_respects_set_eq_r
                 (bigcup_set1 _ _) _)).
    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).

    refine (incl_bigcup_compat (IHs0 _ Hleq) (fun x => @subset_refl _ _)).


refine (subset_respects_set_eq_l
              (eq_bigcupl _ _ (cons_set_eq _ _))
              (subset_respects_set_eq_r
                 (eq_bigcupl _ _ (cons_set_eq _ _))
                 _)
           ).
    refine (subset_respects_set_eq_l
              (bigcup_setU_l _ _ _)
              (subset_respects_set_eq_r
                 (bigcup_setU_l _ _ _)
                 _)
           ).
    refine (setU_set_subset_compat _ _).


    refine (subset_respects_set_eq_l
              (bigcup_set1 _ _)
              (subset_respects_set_eq_r
                 (bigcup_set1 _ _) _)).
    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).

    refine (incl_bigcup_compat
              (@subset_refl _ _)
              (fun x1 => _)).

    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).

    refine (incl_bigcup_compat
              (@subset_refl _ _)
              (fun x2 => _)).

    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).
    
    refine (incl_bigcup_compat
              (@subset_refl _ _)
              (fun x2 => _)).

    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).
    
    refine (incl_bigcup_compat
              (IHs0 _ Hleq)
              (fun x3 => _)).

    refine (subset_respects_set_eq_l
              (semBindSize _ _ _)
              (subset_respects_set_eq_r
                 (semBindSize _ _ _) _)).
    
    refine (incl_bigcup_compat
              (IHs0 _ Hleq)
              (fun x4 => (@subset_refl _ _))).


    refine (@subset_refl _ _).
Qed. 

Typeclasses eauto := debug.

(* Typeclass resolution should be able to derive instances for unsized *)

Definition genFoo {A B : Type } `{H1 : Arbitrary A} `{H2 : Arbitrary B}
           `{H1' : Sized A} `{H2' : Sized B} : G (@Foo A B) := @arbitrary (@Foo A B) _.

Definition corrFoo {A B : Type } `{H1 : ArbitraryMonotonicCorrect A} `{H2 : ArbitraryMonotonicCorrect B}
  := @arbitraryCorrect (@Foo A B) arbitrary.