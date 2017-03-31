Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import GenLow GenHigh Tactics Sets Classes.
Import GenLow GenHigh.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Open Scope string.

Set Bullet Behavior "Strict Subproofs".

(** * Correctness of dependent generators *)

Class SizedSuchThatCorrect {A : Type} `{Sized A} (P : A -> Prop) (g : nat -> G (option A)) :=
  {
    sizedSTCorrect :
      forall s,
        semGen (g s) <-->
        ((@Some A) @: [set x : A | Classes.size x <= s /\ P x ]) :|:
        ([set x : option A | x = None /\ forall y, ~ P y])
  }.

Class SuchThatCorrect {A : Type} (P : A -> Prop) (g : G (option A)) :=
  {
    STCorrect :
      semGen g <-->
      ((@Some A) @: [set x : A | P x ]) :|:
      ([set x : option A | x = None /\ forall y, ~ P y])
  }.

(** * Dependent sized generators *)

Class GenSizedSuchThat (A : Type) (P : A -> Prop) :=
  {
    arbitrarySizeST : nat -> G (option A);
  }.

(** * Monotonicity of denendent sized generators *)

Class GenSizedSuchThatMonotonic (A : Type)
      `{GenSizedSuchThat A} `{forall s, SizeMonotonic (arbitrarySizeST s)}.

Class GenSizedSuchThatSizeMonotonic (A : Type)
      `{GenSizedSuchThat A} `{SizedMonotonic _ arbitrarySizeST}.

(** * Correctness of denendent sized generators *)
  
Class GenSizedSuchThatCorrect (A : Type) (P : A -> Prop)
      `{GenSizedSuchThat A P}
      `{SizedSuchThatCorrect A P arbitrarySizeST}.

(** * Dependent generators *)

Class GenSuchThat (A : Type) (P : A -> Prop) :=
  {
    arbitraryST : G (option A);
  }.

(** * Monotonicity of denendent generators *)

Class GenSuchThatMonotonic (A : Type) (P : A -> Prop) `{GenSuchThat A P}
      `{@SizeMonotonic _ arbitraryST}.

(** * Correctness of dependent generators *)  

Class GenSuchThatCorrect {A : Type} (P : A -> Prop) 
      `{GenSuchThat A P}
      `{SuchThatCorrect A P arbitraryST}.

Class GenSuchThatMonotonicCorrect (A : Type) (P : A -> Prop)
      `{GenSuchThat A P}
      `{@SizeMonotonic _ arbitraryST}
      `{SuchThatCorrect A P arbitraryST}.

(** * Coercions from sized to unsized generators *)
  
Instance GenSuchThatOfSized (A : Type) (P : A -> Prop)
         `{GenSizedSuchThat A P} : GenSuchThat A P :=
  {
    arbitraryST := sized arbitrarySizeST;
  }.

Generalizable Variables PSized PMon PSMon PCorr.

Instance GenSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonic A P H PSMon}
: GenSuchThatMonotonic A P.

Instance ArbitraryCorrectFromSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonic A P H PSMon}
         `{@GenSizedSuchThatCorrect A P H PSized PCorr}
: SuchThatCorrect P arbitraryST.
Proof.
  constructor. unfold arbitraryST, GenSuchThatOfSized.
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
    (* TODO chanfe semSized_alt *)
    destruct PSMon. eauto.
  - setoid_rewrite sizedSTCorrect.
    split.
    + intros [n [Hinn Hun]].
      inv Hun.
      * left. inv H3. inv H4. inv H5. inv H6.
        econstructor; eauto.
      * right. eassumption.
    + intros Hyp. inv Hyp.
      * inv H0. inv H3. inv H4.
        eexists; split; eauto. constructor; eauto.
        left. econstructor; eauto.
      * inv H3.
        exists 0; split; eauto. constructor; eauto.
        right. econstructor; eauto.
Qed.
  
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