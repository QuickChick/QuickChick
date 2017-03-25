Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import GenLow GenHigh Tactics Sets Classes.
Import GenLow GenHigh.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Open Scope string.

Set Bullet Behavior "Strict Subproofs".

(** Precondition parametric size indexed generators *)
(* Should type indices should become parameters of the instance?
 * Cannot think of an other way to treat the uniformly *)
Class ArbitrarySizedSuchThat (A : Type) (P : A -> Prop) :=
  {
    (* Generation should be allowed to fail *)
    arbitrarySizeST : nat -> G (option A);
    (* Shrinking as before *)
(*     shrinkSizeST : A -> list A *)
  }.

(** Monotonicity of ArbitrarySizedSuchThat *)
Class ArbitrarySizedSuchThatMonotonic (A : Type)
      `{ArbitrarySizedSuchThat A} `{forall s, SizeMonotonic (arbitrarySizeST s)}.

(** Monotonicity v2 *)
Class ArbitrarySTSizedSizeMotonic (A : Type) `{ArbitrarySizedSuchThat A} :=
  {
    sizeMonotonicST :
      forall s s1 s2,
        s1 <= s2 ->
        semGenSize (arbitrarySizeST s1) s \subset semGenSize (arbitrarySizeST s2) s
  }.

(** Correctness of parametric gens *)
Class GenSizeSuchThatCorrect {A : Type} `{Sized A} (P : A -> Prop) (g : nat -> G (option A)) :=
  {
    genSizeSTCorrect :
      forall s,
        semGen (g s) <-->
        ((@Some A) @: [set x : A | Classes.size x <= s /\ P x ]) :|:
        ([set x : option A | x = None /\ forall y, ~ P y])
  }.

(** Correctness of ArbitrarySizedSuchThat *)
Class ArbitrarySizedSuchThatCorrect (A : Type) (P : A -> Prop)
      `{Sized A}
      `{ArbitrarySizedSuchThat A P}
      `{GenSizeSuchThatCorrect A P arbitrarySizeST}. 


(* TODO: Move in another file *)
(*
(** Leo's example from DependentTest.v *)

Print Foo.
Print goodFooNarrow.

DeriveSized Foo as "SizedFoo".

(*
Inductive Foo : Set :=
    Foo1 : Foo | Foo2 : Foo -> Foo | Foo3 : nat -> Foo -> Foo

Inductive goodFooNarrow : nat -> Foo -> Prop :=
    GoodNarrowBase : forall n : nat, goodFooNarrow n Foo1
  | GoodNarrow : forall (n : nat) (foo : Foo),
                 goodFooNarrow 0 foo ->
                 goodFooNarrow 1 foo -> goodFooNarrow n foo
 *)

(* Q : Can we but the size last so we don't have to eta expand?? *)
Print genGoodNarrow. 

(** For dependent gens we show generate this instance *)
Instance genGoodNarrow (n : nat) : ArbitrarySizedSuchThat Foo (goodFooNarrow n) :=
  {
    arbitrarySizeST := genGoodNarrow' n;
    shrinkSizeST x := []
  }.

(* For proofs we should generate this instances *)

Instance genGoodNarrowMon (n : nat) (s : nat) :
  SizeMonotonic (@arbitrarySizeST Foo (goodFooNarrow n) _ s).
Abort.

Instance genGoodNarrowSMon (n : nat) :
  @ArbitrarySTSizedSizeMotonic Foo (@goodFooNarrow n) _.
Abort.

Instance genGoodNarrowCorr (n : nat) :
  GenSizeSuchThatCorrect (goodFooNarrow n) (@arbitrarySizeST Foo (goodFooNarrow n) _).
Abort.
*)

(** We can now abstract away from sizes and get the generator and the proofs for free *)

Class ArbitrarySuchThat (A : Type) (P : A -> Prop) :=
  {
    arbitraryST : G (option A);
(*    shrinkST : A -> list A; *)
  }.


Class ArbitrarySuchThatMonotonic (A : Type) (P : A -> Prop) `{ArbitrarySuchThat A P}
      `{H2 : @SizeMonotonic _ arbitraryST}.
  
Class GenSuchThatCorrect {A : Type} (P : A -> Prop) (g : G (option A)) :=
  {
    genSTCorrect :
      semGen g <-->
      ((@Some A) @: [set x : A | P x ]) :|:
      ([set x : option A | x = None /\ forall y, ~ P y])
  }.

(* Monotonic and Correct generators *)
Class ArbitrarySTMonotonicCorrect (A : Type) (P : A -> Prop)
      `{H1 : ArbitrarySuchThat A P}
      `{ArbitrarySuchThatMonotonic A} `{@GenSuchThatCorrect A P arbitraryST}.

Instance ArbitrarySTFromSize (A : Type) (P : A -> Prop)
         `{ArbitrarySizedSuchThat A P}
: ArbitrarySuchThat A P :=
  {
    arbitraryST := sized arbitrarySizeST;
  }.

Instance ArbitraryMonotonicSTFromSized (A : Type) (P : A -> Prop)
         {H1 : ArbitrarySizedSuchThat A P}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySizeST s)) }
         {H3 : @ArbitrarySTSizedSizeMotonic A P H1} :
  @SizeMonotonic (option A) arbitraryST.
Proof.
  constructor. eapply sizedMonotonic.
  now intros n; eauto with typeclass_instances.
  intros. edestruct H3. eauto.
Qed.

Instance ArbitraryCorrectFromSized (A : Type) (P : A -> Prop)
         {H1 : ArbitrarySizedSuchThat A P}
         {H2 : (forall s : nat, SizeMonotonic (arbitrarySizeST s)) }
         {H3 : @ArbitrarySTSizedSizeMotonic A P H1}
         `{H4 : GenSizeSuchThatCorrect A P arbitrarySizeST} : GenSuchThatCorrect P arbitraryST.
Proof.
  constructor. unfold arbitraryST, ArbitrarySTFromSize.
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
    destruct H3. eauto.
  - setoid_rewrite genSizeSTCorrect.
    split.
    + intros [n [Hinn Hun]].
      inv Hun.
      * left. inv H0. inv H5. inv H6.
        econstructor; eauto.
      * right. eassumption.
    + intros Hyp. inv Hyp.
      * inv H0. inv H5.
        eexists; split; eauto. constructor; eauto.
        left. econstructor; eauto.
      * inv H0.
        exists 0; split; eauto. constructor; eauto.
        right. econstructor; eauto.
Qed.