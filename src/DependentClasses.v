Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

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

Class SizedProofEqs {A : Type} (P : A -> Prop) :=
  {
    (* inhabitants for P whose derivation height is less or equal to n *)
    iter : nat -> set A;
    mon : forall n1 n2, n1 <= n2 -> iter n1 \subset iter n2;
    spec : \bigcup_(n : nat) iter n <--> P
  }.


(* Class SizedProofEqs' {A : Type} (P : A -> Prop) := *)
(*   { *)
(*     zero' : set (option A); *)
(*     succ' : set (option A) -> set (option A); *)
(*     spec1 : Some @: P \subset \bigcup_(n : nat) ((succ' ^ n) zero'); *)
(*     spec2 : \bigcup_(n : nat) ((succ' ^ n) zero') \subset  Some @: P :|: [ None ]; *)
(*   }. *)


(* Looks like Scott induction, although we have not proved that
   succ is continuous *)
(* Lemma fixed_point_ind {A} (Q P : A -> Prop) `{SizedProofEqs A P}: *)
(*   zero \subset Q -> *)
(*   (forall (s : set A), s \subset Q -> succ s \subset Q) -> *)
(*   P \subset Q. *)
(* Proof. *)
(*   intros Hz IH. rewrite <- spec. intros x [n [_ HP]]. *)
(*   revert x HP.  *)
(*   induction n. *)
(*   - eauto. *)
(*   - intros x. eapply IH. eauto. *)
(* Qed. *)



Class SizedSuchThatCorrect {A : Type} (P : A -> Prop) `{SizedProofEqs A P} (g : nat -> G (option A)) :=
  {
    sizedSTComplete :
      forall s, Some @: (iter s) \subset semGen (g s);

    sizedSTSound :
      forall s, semGen (g s) \subset lift (iter s)
  }.

Class SuchThatCorrect {A : Type} (P : A -> Prop) (g : G (option A)) :=
  {
    STComplete : Some @: [set x : A | P x ] \subset semGen g;

    STSound : semGen g \subset lift [set x : A | P x ]
  }.

(** * Dependent sized generators *)

Class GenSizedSuchThat (A : Type) (P : A -> Prop) :=
  {
    arbitrarySizeST : nat -> G (option A);
  }.

Notation "'genSizedST' x" := (@arbitrarySizeST _ x _) (at level 70).

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

Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

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

Lemma bigcup_setU_r:
  forall (U T : Type) (s : set U) (f g : U -> set T),
    \bigcup_(i in s) (f i :|: g i) <-->
    \bigcup_(i in s) f i :|: \bigcup_(i in s) g i.
Proof.
  firstorder.
Qed.

Lemma lift_bigcup_comm :
  forall (U T : Type) (s : set U) (f : U -> set T),
    inhabited U ->
    lift (\bigcup_(i in [set : U]) (f i)) <-->
    \bigcup_(i in [set : U]) (lift (f i)).
Proof.
  intros U T s f Hin. unfold lift.
  rewrite !bigcup_setU_r -!imset_bigcup.
  rewrite bigcup_const; eauto.
  reflexivity.
Qed.
    
Instance GenSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonic A P H PSMon}
: GenSuchThatMonotonic A P.

Class GenSizedSuchThatSizeMonotonicOpt (A : Type)
      `{GenSizedSuchThat A} :=
  {
    mon_opt :
      forall s s1 s2,
        isSome :&: semGenSize (arbitrarySizeST s1) s \subset
        isSome :&: semGenSize (arbitrarySizeST s2) s
  }.

Lemma option_subset {A} (s1 : set (option A)) :
  s1 \subset (isSome :&: s1) :|: [set None]. 
Proof.
  intros [x |]; firstorder.
Qed.

Lemma setU_l_subset {U} (s1 s2 s3 : set U) :
  s1 \subset s3 ->
  s2 \subset s3 ->
  (s1 :|: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_lift_lift_bigcup {T U} (s1 : set T) (f : T -> set U) :
  \bigcup_(x in s1) (lift (f x)) \subset lift (\bigcup_(x in s1) (f x)).
Proof.
  intros x [y [H1 [[z [H2 H3]] | H2]]].
  + inv H3. left; eexists; split; eauto.
    eexists; split; eauto.
  + inv H2; now right. 
Qed.

Lemma lift_subset_compat {U} (s1 s2 : set U) :
  s1 \subset s2 ->
  lift s1 \subset lift s2.
Proof.
  firstorder.
Qed.

Lemma lift_set_eq_compat {U} (s1 s2 : set U) :
  s1 <--> s2 ->
  lift s1 <--> lift s2.
Proof.
  firstorder.
Qed.

Instance ArbitraryCorrectFromSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H}
         `{@GenSizedSuchThatCorrect A P H PSized PCorr}
: SuchThatCorrect P arbitraryST.
Proof.
  constructor; unfold arbitraryST, GenSuchThatOfSized.
  - eapply subset_trans.
    eapply subset_respects_set_eq_r.
    eapply semSize_opt; eauto.
    intros. destruct H1. now eauto.
    intros x [y [Py Pg]]. inv Pg.
    eapply spec in Py. destruct Py as [n [H3 H4]].
    split. now eauto.
    eexists n. split; [now constructor |].
    eapply PCorr. eexists; split; eauto.
    firstorder. (* ..... *)
  - eapply subset_trans; [ now eapply option_subset |].
    eapply setU_l_subset; [| eapply setU_set_incl_r; now eapply subset_refl ].
    rewrite semSize_opt.
    eapply set_incl_setI_r.
    eapply subset_trans.
    eapply incl_bigcupr.
    intros n x Hg.
    eapply PCorr in Hg. exact Hg.
    eapply subset_trans; [ now apply bigcup_lift_lift_bigcup |].
    eapply lift_subset_compat.
    rewrite spec. now apply subset_refl.
    intros. destruct H1; eauto.
Qed.

(* TODO: Move to another file *)
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