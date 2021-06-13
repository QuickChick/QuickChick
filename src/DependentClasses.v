Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Producer Generators Enumerators Tactics Sets Classes.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Local Open Scope string.

Set Bullet Behavior "Strict Subproofs".
(** * Correctness of dependent generators *)

(* begin sizeEqs *)
Class SizedProofEqs {A : Type} (P : A -> Prop) :=
  { iter : nat -> set A;
    mon : forall n1 n2, n1 <= n2 -> iter n1 \subset iter n2;
    spec : \bigcup_(n : nat) iter n <--> P}.
(* end sizeEqs *)

Class SizedSuchThatCorrect {A : Type} (P : A -> Prop) `{SizedProofEqs A P} {G} `{Producer G} (g : nat -> G (option A)) :=
  { sizedSTCorrect : forall s, isSome :&: semProd (g s) <--> Some @: (iter s) }.

Class SuchThatCorrect {A : Type} (P : A -> Prop) {G} `{Producer G} (g : G (option A)) :=
  { STCorrect : isSome :&: semProd g <-->  Some @: [set x : A | P x ] }.

(** * Dependent sized generators *)

(* begin genSTSized_class *)
Class GenSizedSuchThat (A : Type) (P : A -> Prop) :=
  { arbitrarySizeST : nat -> G (option A) }.
(* end genSTSized_class *)

(** * Monotonicity of denendent sized generators *)

Class GenSizedSuchThatMonotonic (A : Type)
      `{GenSizedSuchThat A} `{forall s, SizeMonotonic (arbitrarySizeST s)}.


Class GenSizedSuchThatMonotonicOpt (A : Type)
      `{GenSizedSuchThat A} `{forall s, SizeMonotonicOpt (arbitrarySizeST s)}.

Class GenSizedSuchThatSizeMonotonic (A : Type)
      `{GenSizedSuchThat A}
      `{@SizedMonotonic _ G ProducerGen arbitrarySizeST}.

Class GenSizedSuchThatSizeMonotonicOpt (A : Type)
      `{GenSizedSuchThat A}
      `{@SizedMonotonicOpt A G ProducerGen arbitrarySizeST}.


(** * Correctness of denendent sized generators *)
  
Class GenSizedSuchThatCorrect (A : Type) (P : A -> Prop)
      `{GenSizedSuchThat A P}
      `{SizedProofEqs _ P}
      `{@SizedSuchThatCorrect A P _ G ProducerGen arbitrarySizeST}.

(** * Dependent generators *)

(* begin genST_class *)
Class GenSuchThat (A : Type) (P : A -> Prop) := { arbitraryST : G (option A) }.
(* end genST_class *)

Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

(** * Monotonicity of denendent generators *)

Class GenSuchThatMonotonic (A : Type) (P : A -> Prop) `{GenSuchThat A P}
      `{@SizeMonotonic (option A) G ProducerGen arbitraryST}.

Class GenSuchThatMonotonicOpt (A : Type) (P : A -> Prop) `{GenSuchThat A P}
      `{@SizeMonotonicOpt A G ProducerGen arbitraryST}.

(** * Correctness of dependent generators *)  

Class GenSuchThatCorrect {A : Type} (P : A -> Prop) 
      `{GenSuchThat A P}
      `{@SuchThatCorrect A P G ProducerGen arbitraryST}.

Class GenSuchThatMonotonicCorrect (A : Type) (P : A -> Prop)
      `{GenSuchThat A P}
      `{@SizeMonotonicOpt A G ProducerGen arbitraryST}
      `{@SuchThatCorrect A P G ProducerGen arbitraryST}.

(** Coercions *)
   
Instance GenSizedSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSizedSuchThat A P)
         (Hmon : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
: @GenSizedSuchThatMonotonicOpt A P Hgen Hmon := {}.

Instance GenSizedSuchThatSizeMonotonicOptOfSizedMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSizedSuchThat A P)
         (Hmon : SizedMonotonicOpt arbitrarySizeST)
: @GenSizedSuchThatSizeMonotonicOpt A P Hgen Hmon := {}.

Instance GenSizedSuchThatCorrectOptOfSizedSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : GenSizedSuchThat A P)
         (Heqs : SizedProofEqs P)
         (Hcorr : SizedSuchThatCorrect P arbitrarySizeST)
: @GenSizedSuchThatCorrect A P H Heqs Hcorr := {}.

Instance GenSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSuchThat A P)
         (Hmon : SizeMonotonicOpt arbitraryST)
: @GenSuchThatMonotonicOpt A _ Hgen Hmon := {}.

Instance GenSuchThatCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : GenSuchThat A P)
         (Hcorr : SuchThatCorrect P (genST P))
: @GenSuchThatCorrect A P H Hcorr := {}.

Instance SizeMonotonicOptofSizeMonotonic {A} (g : G (option A))
         {H : SizeMonotonic g} : SizeMonotonicOpt g.
Proof.
  intros s1 s2 Hs a.
  eapply monotonic; eauto.
Qed.

(** * Coercions from sized to unsized generators *)

(* Generators *)

(* begin GenSuchThatOfBounded *)
Instance GenSuchThatOfBounded (A : Type) (P : A -> Prop) (H : GenSizedSuchThat A P)
: GenSuchThat A P := { arbitraryST := sized arbitrarySizeST }.
(* end GenSuchThatOfBounded *)

Generalizable Variables PSized PMon PSMon PCorr.

(* Monotonicity *)

Instance GenSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonic A P H PSMon}
  : @GenSuchThatMonotonic A P (GenSuchThatOfBounded _ _ H)
    (@sizedSizeMonotonic G ProducerGen _ _
                         _
                         PMon PSMon) := {}.

Instance SizeMonotonicOptOfBounded' (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonicOpt A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H PSMon}
: SizeMonotonicOpt (genST P).
Proof.
  unfold arbitraryST, GenSuchThatOfBounded.
  red. red in PMon.
  do 2 red. intros.
  unfold semProdSizeOpt in *.
  red in PMon.
  apply semSizedSize in H3.
  apply semSizedSize.

  unfold SizedMonotonicOpt in PSMon.
  destruct (PSMon s1 s1 s2 H2 a). apply H3.
  apply (PMon s2 s1 s2); auto. do 3 red.
  eauto.
  rewrite /semGenSize => //=.
  exists x.
  eauto.
Qed.

(* begin SizeMonotonicOptOfBounded *)
Instance SizeMonotonicOptOfBounded (A : Type) (P : A -> Prop)
         (H1 : GenSizedSuchThat A P)
         (H2 : SizedProofEqs P) (* XXX change name *)
         (H3 : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
         (H4 : SizedMonotonicOpt arbitrarySizeST) (* XXX change name *)
: SizeMonotonicOpt (genST P).
(* end SizeMonotonicOptOfBounded *)
Proof.
  eapply SizeMonotonicOptOfBounded'.
  constructor; eauto.
  constructor; eauto.
Qed.

Instance GenSuchThatMonotonicOptOfSized' (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonicOpt A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H PSMon}
: GenSuchThatMonotonicOpt A P := {}.

(* Correctness *)
Instance SuchThatCorrectOfBounded' (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonicOpt A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H PSMon}
         `{@GenSizedSuchThatCorrect A P H PSized PCorr}
: SuchThatCorrect P arbitraryST.
Proof.
  constructor; unfold arbitraryST, GenSuchThatOfBounded.
  rewrite semSized_opt; eauto.
  split.
  - intros [H3 H4]. destruct a; try discriminate.
    eexists. split; [| reflexivity ].
    eapply spec.
    destruct H4 as [n [_ Hsem]]. 
    exists n. split. now constructor.
    assert (Ha : (isSome :&: semProd (arbitrarySizeST n)) (Some a)).
    { split; eauto. }
    eapply PCorr in Ha. destruct Ha as [a' [Hit Heq]]. inv Heq. eassumption.
  - intros [y [HP Heq]]. inv Heq.
    eapply spec in HP. destruct HP as [n [_ Hit]].
    split; eauto. exists n. split; [ now constructor |].
    eapply PCorr. eexists; split; eauto.
Qed.

(* begin SuchThatCorrectOfBounded *)
Instance SuchThatCorrectOfBounded (A : Type) (P : A -> Prop)
         (H1 : GenSizedSuchThat A P)
         (H2 : SizedProofEqs P) (* XXX change name *)
         (H3 : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
         (H4 : SizedMonotonicOpt arbitrarySizeST) (* XXX change name *)
         (H5 : SizedSuchThatCorrect P arbitrarySizeST)
: SuchThatCorrect P arbitraryST.
(* end SuchThatCorrectOfBounded *)
Proof.
  eapply SuchThatCorrectOfBounded'; eauto.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

(* Dependent Sized Enumerators *)
(** * Dependent sized generators *)

(* begin genSTSized_class *)
Class EnumSizedSuchThat (A : Type) (P : A -> Prop) :=
  { enumSizeST : nat -> E (option A) }.
(* end genSTSized_class *)

(** * Monotonicity of denendent sized generators *)

Class EnumSizedSuchThatMonotonic (A : Type)
      `{EnumSizedSuchThat A} `{forall s, SizeMonotonic (enumSizeST s)}.


Class EnumSizedSuchThatMonotonicOpt (A : Type)
      `{EnumSizedSuchThat A} `{forall s, SizeMonotonicOpt (enumSizeST s)}.

Class EnumSizedSuchThatSizeMonotonic (A : Type)
      `{EnumSizedSuchThat A}
      `{@SizedMonotonic _ E ProducerEnum enumSizeST}.

Class EnumSizedSuchThatSizeMonotonicOpt (A : Type)
      `{EnumSizedSuchThat A}
      `{@SizedMonotonicOpt A E ProducerEnum enumSizeST}.


(** * Correctness of denendent sized generators *)
  
Class EnumSizedSuchThatCorrect (A : Type) (P : A -> Prop)
      `{EnumSizedSuchThat A P}
      `{SizedProofEqs _ P}
      `{@SizedSuchThatCorrect A P _ E ProducerEnum enumSizeST}.

(** * Dependent generators *)

(* begin genST_class *)
Class EnumSuchThat (A : Type) (P : A -> Prop) := { enumSuchThat : E (option A) }.
(* end genST_class *)

Notation "'enumST' x" := (@enumSuchThat _ x _) (at level 70).

(** * Monotonicity of denendent generators *)

Class EnumSuchThatMonotonic (A : Type) (P : A -> Prop) `{EnumSuchThat A P}
      `{@SizeMonotonic (option A) E ProducerEnum enumSuchThat}.

Class EnumSuchThatMonotonicOpt (A : Type) (P : A -> Prop) `{EnumSuchThat A P}
      `{@SizeMonotonicOpt A E ProducerEnum enumSuchThat}.

(** * Correctness of dependent generators *)  

Class EnumSuchThatCorrect {A : Type} (P : A -> Prop) 
      `{EnumSuchThat A P}
      `{@SuchThatCorrect A P E ProducerEnum enumSuchThat}.

Class EnumSuchThatMonotonicCorrect (A : Type) (P : A -> Prop)
      `{EnumSuchThat A P}
      `{@SizeMonotonicOpt A E ProducerEnum enumSuchThat}
      `{@SuchThatCorrect A P E ProducerEnum enumSuchThat}.

(** Coercions *)
   
Instance EnumSizedSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSizedSuchThat A P)
         (Hmon : forall s : nat, SizeMonotonicOpt (enumSizeST s))
: @EnumSizedSuchThatMonotonicOpt A P Hgen Hmon := {}.

Instance EnumSizedSuchThatSizeMonotonicOptOfSizedMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSizedSuchThat A P)
         (Hmon : SizedMonotonicOpt enumSizeST)
: @EnumSizedSuchThatSizeMonotonicOpt A P Hgen Hmon := {}.

Instance EnumSizedSuchThatCorrectOptOfSizedSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : EnumSizedSuchThat A P)
         (Heqs : SizedProofEqs P)
         (Hcorr : SizedSuchThatCorrect P enumSizeST)
: @EnumSizedSuchThatCorrect A P H Heqs Hcorr := {}.

Instance EnumSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSuchThat A P)
         (Hmon : SizeMonotonicOpt enumSuchThat)
: @EnumSuchThatMonotonicOpt A _ Hgen Hmon := {}.

Instance EnumSuchThatCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : EnumSuchThat A P)
         (Hcorr : SuchThatCorrect P (enumST P))
: @EnumSuchThatCorrect A P H Hcorr := {}.

Instance SizeMonotonicOptofSizeMonotonicEnum {A} (g : E (option A))
         {H : SizeMonotonic g} : SizeMonotonicOpt g.
Proof.
  intros s1 s2 Hs a.
  eapply monotonic; eauto.
Qed.

(** * Coercions from sized to unsized generators *)

(* Enumerators *)

(* begin EnumSuchThatOfBounded *)
Instance EnumSuchThatOfBounded (A : Type) (P : A -> Prop) (H : EnumSizedSuchThat A P)
: EnumSuchThat A P := { enumSuchThat := sized enumSizeST }.
(* end EnumSuchThatOfBounded *)

(* Monotonicity *)

Instance EnumSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonic A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonic A P H PSMon}
  : @EnumSuchThatMonotonic A P (EnumSuchThatOfBounded _ _ H)
    (@sizedSizeMonotonic E ProducerEnum _ _
                         _
                         PMon PSMon) := {}.

Set Printing All.
Instance SizeMonotonicOptOfBoundedEnum' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
: SizeMonotonicOpt (enumST P).
Proof.
  unfold enumSuchThat, EnumSuchThatOfBounded.
  red. red in PMon.
  do 2 red. intros.
  unfold semProdSizeOpt in *.
  red in PMon.
  apply semSizedSize in H3.
  apply semSizedSize.
  unfold SizedMonotonicOpt in PSMon.
  unfold semProdSizeOpt in *.
(*
  destruct (PSMon s1 s1 s2 H2 a). apply H3.
  apply (PMon s2 s1 s2); auto. do 3 red.
  eauto.
  rewrite /semEnumSize => //=.
  exists x.
  eauto.
Qed.
 *)
Admitted.

(* begin SizeMonotonicOptOfBounded *)
Instance SizeMonotonicOptOfBoundedEnum (A : Type) (P : A -> Prop)
         (H1 : EnumSizedSuchThat A P)
         (H2 : SizedProofEqs P) (* XXX change name *)
         (H3 : forall s : nat, SizeMonotonicOpt (enumSizeST s))
         (H4 : SizedMonotonicOpt enumSizeST) (* XXX change name *)
: SizeMonotonicOpt (enumST P).
(* end SizeMonotonicOptOfBounded *)
Proof.
  eapply SizeMonotonicOptOfBoundedEnum'.
  constructor; eauto.
  constructor; eauto.
Qed.

Instance EnumSuchThatMonotonicOptOfSized' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
: EnumSuchThatMonotonicOpt A P := {}.

(* Correctness *)
Instance SuchThatCorrectOfBoundedEnum' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
         `{@EnumSizedSuchThatCorrect A P H PSized PCorr}
: SuchThatCorrect P enumSuchThat.
Proof.
  constructor; unfold enumSuchThat, EnumSuchThatOfBounded.
  rewrite semSized_opt; eauto.
  split.
  - intros [H3 H4]. destruct a; try discriminate.
    eexists. split; [| reflexivity ].
    eapply spec.
    destruct H4 as [n [_ Hsem]]. 
    exists n. split. now constructor.
    assert (Ha : (isSome :&: semProd (enumSizeST n)) (Some a)).
    { split; eauto. }
    eapply PCorr in Ha. destruct Ha as [a' [Hit Heq]]. inv Heq. eassumption.
  - intros [y [HP Heq]]. inv Heq.
    eapply spec in HP. destruct HP as [n [_ Hit]].
    split; eauto. exists n. split; [ now constructor |].
    eapply PCorr. eexists; split; eauto.
Qed.

(* begin SuchThatCorrectOfBounded *)
Instance SuchThatCorrectOfBoundedEnum (A : Type) (P : A -> Prop)
         (H1 : EnumSizedSuchThat A P)
         (H2 : SizedProofEqs P) (* XXX change name *)
         (H3 : forall s : nat, SizeMonotonicOpt (enumSizeST s))
         (H4 : SizedMonotonicOpt enumSizeST) (* XXX change name *)
         (H5 : SizedSuchThatCorrect P enumSizeST)
: SuchThatCorrect P enumSuchThat.
(* end SuchThatCorrectOfBounded *)
Proof.
  eapply SuchThatCorrectOfBoundedEnum'; eauto.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
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
Instance genGoodNarrow (n : nat) : EnumSizedSuchThat Foo (goodFooNarrow n) :=
  {
    enumSizeST := genGoodNarrow' n;
    shrinkSizeST x := []
  }.

(* For proofs we should generate this instances *)

Instance genGoodNarrowMon (n : nat) (s : nat) :
  SizeMonotonic (@enumSizeST Foo (goodFooNarrow n) _ s).
Abort.

Instance genGoodNarrowSMon (n : nat) :
  @EnumSTSizedSizeMotonic Foo (@goodFooNarrow n) _.
Abort.

Instance genGoodNarrowCorr (n : nat) :
  EnumSizeSuchThatCorrect (goodFooNarrow n) (@enumSizeST Foo (goodFooNarrow n) _).
Abort.
*)

(** We can now abstract away from sizes and get the generator and the proofs for free *)

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

