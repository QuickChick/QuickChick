Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Producer Generators Enumerators Tactics Sets Classes.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Local Open Scope string.
Local Open Scope set_scope.

Set Bullet Behavior "Strict Subproofs".
(** * Correctness of dependent generators *)

Class CorrectSizedST {A : Type} (P : A -> Prop) {G} `{Producer G} (g : nat -> G (option A)) :=
  { corrST : [ set x | exists s, semProdOpt (g s) x ]  <-->  P }.

Class CorrectST {A : Type} (P : A -> Prop) {G} `{Producer G} (g : G (option A)) :=
  { corr : semProdOpt g  <-->  P  }.

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
      `{@CorrectSizedST A P G ProducerGen arbitrarySizeST}.

  
(** * Dependent generators *)

(* begin genST_class *)
Class GenSuchThat (A : Type) (P : A -> Prop) := { arbitraryST : G (option A) }.
(* end genST_class *)

Notation "'genSizedST' x" := ((@arbitrarySizeST _ x _)) (at level 10).
Notation "'genST' x" := ((@arbitraryST _ x _)) (at level 10).

(** * Monotonicity of denendent generators *)

Class GenSuchThatMonotonic (A : Type) (P : A -> Prop) `{GenSuchThat A P}
      `{@SizeMonotonic (option A) G ProducerGen arbitraryST}.

Class GenSuchThatMonotonicOpt (A : Type) (P : A -> Prop) `{GenSuchThat A P}
      `{@SizeMonotonicOpt A G ProducerGen arbitraryST}.

(** * Correctness of dependent generators *)  

Class GenSuchThatCorrect {A : Type} (P : A -> Prop) 
      `{GenSuchThat A P}
      `{@CorrectST A P G ProducerGen arbitraryST}.

Class GenSuchThatMonotonicCorrect (A : Type) (P : A -> Prop)
      `{GenSuchThat A P}
      `{@SizeMonotonicOpt A G ProducerGen arbitraryST}
      `{@CorrectST A P G ProducerGen arbitraryST}.

(** Coercions *)
   
#[global] Instance GenSizedSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSizedSuchThat A P)
         (Hmon : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
: @GenSizedSuchThatMonotonicOpt A P Hgen Hmon := {}.

#[global] Instance GenSizedSuchThatSizeMonotonicOptOfSizedMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSizedSuchThat A P)
         (Hmon : SizedMonotonicOpt arbitrarySizeST)
: @GenSizedSuchThatSizeMonotonicOpt A P Hgen Hmon := {}.

#[global] Instance GenSizedSuchThatCorrectOptOfSizedSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : GenSizedSuchThat A P)
         (Hcorr : CorrectSizedST P arbitrarySizeST)
: @GenSizedSuchThatCorrect A P H Hcorr := {}.

#[global] Instance GenSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : GenSuchThat A P)
         (Hmon : SizeMonotonicOpt arbitraryST)
: @GenSuchThatMonotonicOpt A _ Hgen Hmon := {}.

#[global] Instance GenSuchThatCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : GenSuchThat A P)
         (Hcorr : CorrectST P (genST P))
: @GenSuchThatCorrect A P H Hcorr := {}.

#[global] Instance GenSuchThatMonotonicCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : GenSuchThat A P)
         (Hcorr : CorrectST P (genST P))
         (Hmon : SizeMonotonicOpt (genST P))
: @GenSuchThatMonotonicCorrect A P H Hmon Hcorr := {}.

#[global] Instance SizeMonotonicOptofSizeMonotonic {A} (g : G (option A))
         {H : SizeMonotonic g} : SizeMonotonicOpt g.
Proof.
  intros s1 s2 Hs a.
  eapply monotonic; eauto.
Qed.

(** * Coercions from sized to unsized generators *)

(* Generators *)

(* begin GenSuchThatOfBounded *)
#[global] Instance GenSuchThatOfBounded (A : Type) (P : A -> Prop) (H : GenSizedSuchThat A P)
: GenSuchThat A P := { arbitraryST := sized arbitrarySizeST }.
(* end GenSuchThatOfBounded *)

Generalizable Variables PSized PMon PSMon PCorr.

(* Monotonicity *)

#[global] Instance GenSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonic A P H PMon}
         `{@GenSizedSuchThatSizeMonotonic A P H PSMon}
  : @GenSuchThatMonotonic A P (GenSuchThatOfBounded _ _ H)
    (@sizedSizeMonotonic G ProducerGen _ _
                         _
                         PMon PSMon) := {}.

#[global] Instance SizeMonotonicOptOfBounded' (A : Type) (P : A -> Prop)
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
#[global] Instance SizeMonotonicOptOfBounded (A : Type) (P : A -> Prop)
         (H1 : GenSizedSuchThat A P)
         (H3 : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
         (H4 : SizedMonotonicOpt arbitrarySizeST) (* XXX change name *)
: SizeMonotonicOpt (genST P).
(* end SizeMonotonicOptOfBounded *)
Proof.
  eapply SizeMonotonicOptOfBounded'.
  constructor; eauto.
  constructor; eauto.
Qed.

#[global] Instance GenSuchThatMonotonicOptOfSized' (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonicOpt A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H PSMon}
: GenSuchThatMonotonicOpt A P := {}.

(* Correctness *)
#[global] Instance SuchThatCorrectOfBounded' (A : Type) (P : A -> Prop)
         {H : GenSizedSuchThat A P}
         `{@GenSizedSuchThatMonotonicOpt A P H PMon}
         `{@GenSizedSuchThatSizeMonotonicOpt A P H PSMon}
         `{@GenSizedSuchThatCorrect A P H PCorr}
: CorrectST P arbitraryST.
Proof.
  constructor; unfold arbitraryST, GenSuchThatOfBounded.
  split.
  - intros [s [_ H4]].
    eapply semSizedSizeGen in H4.
    eapply PCorr. eexists; eauto. eexists; eauto.
    split; eauto. reflexivity.
    
  - intros Hp. eapply PCorr in Hp. destruct Hp as [s [x [_ Hs]]].
    eexists (max s x). split. reflexivity.
    eapply semSizedSizeGen.

    eapply PMon; [ | eapply PSMon; [ | eassumption ]].
    ssromega.
    ssromega.
Qed.

(* begin SuchThatCorrectOfBounded *)
#[global] Instance SuchThatCorrectOfBounded (A : Type) (P : A -> Prop)
         (H1 : GenSizedSuchThat A P)
         (H3 : forall s : nat, SizeMonotonicOpt (arbitrarySizeST s))
         (H4 : SizedMonotonicOpt arbitrarySizeST) (* XXX change name *)
         (H5 : CorrectSizedST P arbitrarySizeST)
: CorrectST P arbitraryST.
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
      `{@CorrectSizedST A P E ProducerEnum enumSizeST}.

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
      `{@CorrectST A P E ProducerEnum enumSuchThat}.

Class EnumSuchThatMonotonicCorrect (A : Type) (P : A -> Prop)
      `{EnumSuchThat A P}
      `{@SizeMonotonicOpt A E ProducerEnum enumSuchThat}
      `{@CorrectST A P E ProducerEnum enumSuchThat}.

(** Coercions *)
   
#[global] Instance EnumSizedSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSizedSuchThat A P)
         (Hmon : forall s : nat, SizeMonotonicOpt (enumSizeST s))
: @EnumSizedSuchThatMonotonicOpt A P Hgen Hmon := {}.

#[global] Instance EnumSizedSuchThatSizeMonotonicOptOfSizedMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSizedSuchThat A P)
         (Hmon : SizedMonotonicOpt enumSizeST)
: @EnumSizedSuchThatSizeMonotonicOpt A P Hgen Hmon := {}.

#[global] Instance EnumSizedSuchThatCorrectOptOfSizedSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : EnumSizedSuchThat A P)
         (Hcorr : CorrectSizedST P enumSizeST)
: @EnumSizedSuchThatCorrect A P H Hcorr := {}.

#[global] Instance EnumSuchThatMonotonicOptOfSizeMonotonic
         (A : Type) (P : A -> Prop) (Hgen : EnumSuchThat A P)
         (Hmon : SizeMonotonicOpt enumSuchThat)
: @EnumSuchThatMonotonicOpt A _ Hgen Hmon := {}.

#[global] Instance EnumSuchThatCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : EnumSuchThat A P)
         (Hcorr : CorrectST P (enumST P))
: @EnumSuchThatCorrect A P H Hcorr := {}.

#[global] Instance SizeMonotonicOptofSizeMonotonicEnum {A} (g : E (option A))
         {H : SizeMonotonic g} : SizeMonotonicOpt g.
Proof.
  intros s1 s2 Hs a.
  eapply monotonic; eauto.
Qed.

#[global] Instance EnumSuchThatMonotonicCorrectOptOfSuchThatCorrect
         (A : Type) (P : A -> Prop) (H : EnumSuchThat A P)
         (Hcorr : CorrectST P (enumST P))
         (Hmon : SizeMonotonicOpt (enumST P))
  : @EnumSuchThatMonotonicCorrect A P H Hmon Hcorr := {}.


(** * Coercions from sized to unsized generators *)

(* Enumerators *)

(* begin EnumSuchThatOfBounded *)
#[global] Instance EnumSuchThatOfBounded (A : Type) (P : A -> Prop) (H : EnumSizedSuchThat A P)
: EnumSuchThat A P := { enumSuchThat := sized enumSizeST }.
(* end EnumSuchThatOfBounded *)

(* Monotonicity *)

#[global] Instance EnumSuchThatMonotonicOfSized (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonic A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonic A P H PSMon}
  : @EnumSuchThatMonotonic A P (EnumSuchThatOfBounded _ _ H)
    (@sizedSizeMonotonic E ProducerEnum _ _
                         _
                         PMon PSMon) := {}.


#[global] Instance SizeMonotonicOptOfBoundedEnum' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
: SizeMonotonicOpt (enumST P).
Proof.
  unfold enumSuchThat, EnumSuchThatOfBounded.
  eapply sizedSizeMonotonicOpt; eauto with typeclass_instances.
Qed.

(* begin SizeMonotonicOptOfBounded *)
#[global] Instance SizeMonotonicOptOfBoundedEnum (A : Type) (P : A -> Prop)
         (H1 : EnumSizedSuchThat A P)
         (H3 : forall s : nat, SizeMonotonicOpt (enumSizeST s))
         (H4 : SizedMonotonicOpt enumSizeST) (* XXX change name *)
: SizeMonotonicOpt (enumST P).
(* end SizeMonotonicOptOfBounded *)
Proof.
  eapply SizeMonotonicOptOfBoundedEnum'.
  constructor; eauto.
  constructor; eauto.
Qed.

#[global] Instance EnumSuchThatMonotonicOptOfSized' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
: EnumSuchThatMonotonicOpt A P := {}.


Lemma size_CorrectST {A : Type} (P : A -> Prop) {G} {PG : Producer G}
         {PS: @ProducerSemantics G PG} (g : nat -> G (option A))
         {Hm1 : forall s, SizeMonotonicOpt (g s)}
         {Hm2 : SizedMonotonicOpt g}
         {_ : CorrectSizedST P g} : CorrectST P (sized g).
Proof.
  inv H. constructor.
  intros x. split; intros Hin.
  - eapply corrST0.
    inv Hin. inv H0. eapply semSizedSize in H2.
    eexists. eexists; split; eauto.
  - eapply corrST0 in Hin. inv Hin. inv H0. inv H1.
    eexists (max x0 x1). split; eauto. eapply semSizedSize.
    eapply Hm1; [ | eapply Hm2; [ | eassumption ]]; ssromega. 
Qed.

(* Correctness *)
#[global] Instance SuchThatCorrectOfBoundedEnum' (A : Type) (P : A -> Prop)
         {H : EnumSizedSuchThat A P}
         `{@EnumSizedSuchThatMonotonicOpt A P H PMon}
         `{@EnumSizedSuchThatSizeMonotonicOpt A P H PSMon}
         `{@EnumSizedSuchThatCorrect A P H PCorr}
: CorrectST P enumSuchThat.
Proof.
  constructor; unfold enumSuchThat, EnumSuchThatOfBounded.
  eapply size_CorrectST; eauto with typeclass_instances.
Qed.

(* begin SuchThatCorrectOfBounded *)
#[global] Instance SuchThatCorrectOfBoundedEnum (A : Type) (P : A -> Prop)
         (H1 : EnumSizedSuchThat A P)
         (H3 : forall s : nat, SizeMonotonicOpt (enumSizeST s))
         (H4 : SizedMonotonicOpt enumSizeST) (* XXX change name *)
         (H5 : CorrectSizedST P enumSizeST)
: CorrectST P enumSuchThat.
(* end SuchThatCorrectOfBounded *)
Proof.
  eapply SuchThatCorrectOfBoundedEnum'; eauto.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.


Lemma enumeratingOpt_sound A P (e : E (option A)) {Hc : CorrectST P e} ch s :
  enumeratingOpt e ch s = Some true ->
  exists x, P x /\ ch x = Some true.
Proof.
  unfold enumeratingOpt.
  assert (Hs : forall x, LazyList.In_ll (Some x) (Enumerators.run e s) ->
                         P x).
  { intros. eapply Hc. eexists. split; eauto. reflexivity. 
    simpl. eassumption. }
  revert Hs.
  generalize (Enumerators.run e s), false. clear.
  induction l; intros b Hyp Heq; simpl in *.
  - destruct b; congruence.
  - destruct a; eauto. destruct (ch a) as [ [| ] | ] eqn:Heq'; eauto.
Qed.

Lemma enumeratingOpt_complete A P (e : E (option A)) {Hc : CorrectST P e} ch x :
  P x ->
  ch x = Some true ->
  exists s, enumeratingOpt e ch s = Some true.
Proof.
  unfold enumeratingOpt. intros Hp Heq. 
  assert (Hs : semProdOpt e x).
  { eapply Hc. eassumption. }
  destruct Hs as [s [_ Hs]]. simpl in *. unfold semEnumSize in Hs.
  exists s. revert Hs Heq. 
  generalize (Enumerators.run e s), false. clear.
  induction l; intros b Hin Heq; simpl in *.
  - exfalso; eauto.
  - inv Hin. 
    + rewrite Heq. reflexivity.
    + destruct a; eauto.
      destruct (ch a) as [ [| ] | ] eqn:Heq'; eauto.    
Qed.


Lemma enumeratingOpt_sound_simpl A (e : E (option A)) ch s :
  enumeratingOpt e ch s = Some true ->
  exists x, ch x = Some true.
Proof.
  unfold enumeratingOpt.
  generalize (Enumerators.run e s), false. clear.
  induction l; intros b Heq; simpl in *.
  - destruct b; congruence.
  - destruct a; eauto. destruct (ch a) as [ [| ] | ] eqn:Heq'; eauto.
Qed.    
