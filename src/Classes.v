Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Classes.Morphisms.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrnat.
Require Import Sets Tactics.
Require Import Recdef.
Require Import List.

Require Import ZArith ZArith.Znat Arith.

Require Import Producer Generators Enumerators.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope set_scope.

(** Apply a function n times *)
Fixpoint appn {A} (f : A -> A) (n : nat) : A ->  A :=
  fun x =>
    match n with
      | 0%nat => x
      | S n' => f (appn f n' x)
    end.

Infix "^" := appn (at level 30, right associativity) : fun_scope.


(** Instance Hierarchy  

   GenSized 
      |
      |
     Gen   Shrink
       \    /
        \  /
      Arbitrary
*)

(** * Generator-related classes *)

(* begin gen_sized_class *)
Class GenSized (A : Type) :=
  { arbitrarySized : nat -> G A }.
(* end gen_sized_class *)

(* begin gen_class *)
Class Gen (A : Type) := { arbitrary : G A }.
(* end gen_class *)

(** Shrink class *)
Class Shrink (A : Type) :=
  { shrink : A -> list A }.

(** Arbitrary Class *)
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.

Class Fuzzy (A : Type) := { fuzz : A -> G A }.

(* TODO: should be able to fail? i.e. outputs G (option A) instead *)
Class Mutate (A : Type) := { mutate : A -> G A }.
  
Class EnumSized (A : Type) := { enumSized : nat -> E A }.
  
Class Enum (A : Type) := { enum : E A }.

Class Sized (A : Type) :=
  { size : A -> nat }.

(* ZP: This is not longer usefull *) 
(* 
(** * Sizes of types *)
  
Class Sized (A : Type) :=
  { size : A -> nat }.

Class CanonicalSized (A : Type) `{Sized A} :=
  {
    zeroSized : set A;
    succSized : set A -> set A;

    zeroSized_spec : zeroSized <--> [ set x : A | size x = 0 ];
    succSized_spec :
      forall n, succSized [ set x : A | size x <= n ] <--> [ set x : A | size x <= S n ]
 
  }.

Lemma size_ind (A : Type) `{Hyp : Sized A} :
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

Lemma size_lfp (A : Type) `{Hyp : CanonicalSized A} :
  [set x : A | True ] <--> \bigcup_(s : nat) [set x : A | size x <= s ].
Proof.
  intros a; split; eauto. intros _.
  exists (size a). split; eauto. constructor.
Qed.

Lemma succ_lfp (A : Type) `{Hyp : CanonicalSized A}
      `{Proper _ (respectful set_eq set_eq) succSized} s :
  [set x : A | size x <= s ] <-->  (succSized ^ s) zeroSized.
Proof.
  induction s.
  simpl.
  - rewrite zeroSized_spec.
    split; intros; ssromega.
  - simpl. rewrite <- succSized_spec.
    rewrite IHs. reflexivity.
Qed.
*) 
(* Lemma succ_lfp' (A : Type) `{Hyp : CanonicalSized A} : *)
(*   \bigcup_(s : nat)  (succSized ^ s) zeroSized <--> [ set x : A | True ]. *)
(* Proof. *)
(*   intros. split; eauto. *)
(*   intros _. *)
(*   eapply set_eq_trans. *)
(*   Focus 2. symmetry. *)
(*   eapply succ_lfp. *)
(*   simpl.  *)
(*   rewrite succ_lfp at 2. *)
(* split. *)
(*     split. rewrite IHs. firstorder. *)
(*     IHs. *)
(*   firstorder. reflexivity. split; intros; eauto. *)
(*   exists (size a). *)
(*   remember (size a) as s. *)
(*   revert a Heqs. induction s; intros. *)
(*   - split. constructor. *)
(*     simpl. eapply zeroSized_spec. now eauto. *)
(*   - split. constructor. *)
(*     simpl. *)
(*     eapply (succSized_spec. *)
(*     eassumption. *)
(*   eapply size_ind. *)
  
(*   [set x : A | True ] <-->  . *)

(** * Correctness classes *)

(** Correctness of sized generators *)

Class CorrectSized {A : Type} {G} `{Producer G} (g : nat -> G A)  :=
  { prodCorrectSized :
      [ set n | exists s, semProd (g s) n ] <--> [set : A]
  }.


(** Correctness of generators *)
Class Correct (A : Type) {G} `{Producer G} (g : G A)  :=
  {
    prodCorrect : semProd g <--> [set : A]
  }.

(** * Monotonic generators *)

(** Monotonicity of size parametric generators *)
Class GenSizedMonotonic (A : Type) `{GenSized A}
      `{forall s, SizeMonotonic (arbitrarySized s)}.

(** Monotonicity of size parametric generators v2 *)
Class GenSizedSizeMonotonic (A : Type) `{GenSized A}
        `{SizedMonotonic A G arbitrarySized}.

Class GenMonotonic (A : Type) `{Gen A} `{@SizeMonotonic A G ProducerGen arbitrary}.

(** Monotonicity of size parametric generators *)
Class EnumSizedMonotonic (A : Type) `{EnumSized A}
      `{forall s, @SizeMonotonic A E ProducerEnum (enumSized s)}.

(** Monotonicity of size parametric generators v2 *)
Class EnumSizedSizeMonotonic (A : Type) `{EnumSized A}
        `{@SizedMonotonic A E ProducerEnum enumSized}.

Class EnumMonotonic (A : Type) `{Enum A}
        `{@SizeMonotonic A E ProducerEnum enum}.
  
(** * Correct generators *)

Class GenSizedCorrect (A : Type) `{GenSized A}
      `{@CorrectSized A G ProducerGen arbitrarySized}.

Class GenCorrect (A : Type) `{Gen A}
        `{@Correct A G ProducerGen arbitrary}.
 
(* Monotonic and Correct generators *)
Class GenMonotonicCorrect (A : Type)
      `{Gen A}
      `{@SizeMonotonic A G ProducerGen arbitrary}
      `{@Correct  A G ProducerGen arbitrary}.

Class EnumSizedCorrect (A : Type)
        `{EnumSized A} `{@CorrectSized A E ProducerEnum enumSized}.

Class EnumCorrect (A : Type) `{Enum A}
        `{@Correct A E ProducerEnum enum}.
 
(* Monotonic and Correct generators *)
Class EnumMonotonicCorrect (A : Type)
      `{Enum A}
      `{@SizeMonotonic A E ProducerEnum enum}
      `{@Correct A E ProducerEnum enum}.

  
(** Coercions *)
  
#[global] Instance GenSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : forall s, @SizeMonotonic A G ProducerGen (arbitrarySized s))
: @GenSizedMonotonic A Hgen Hmon := {}.
  
#[global] Instance GenMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Gen A) (Hmon : @SizeMonotonic A G ProducerGen arbitrary)
: @GenMonotonic A Hgen Hmon := {}.

#[global] Instance GenSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : GenSized A)
         `{Hcor : @CorrectSized A G ProducerGen arbitrarySized}
: @GenSizedCorrect A Hgen Hcor := {}.

#[global] Instance GenMonotonicCorrectOfMonotnicCorrect
         (A : Type) (Hgen : Gen A)
         (Hmon : @SizeMonotonic A G ProducerGen arbitrary)
         `{Hcor : @Correct A G ProducerGen arbitrary}
  : @GenMonotonicCorrect A Hgen Hmon Hcor := {}.



#[global] Instance GenSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : GenSized A) (Hmon : @SizedMonotonic A G ProducerGen arbitrarySized)
: @GenSizedSizeMonotonic A Hgen ProducerGen Hmon := {}.

#[global] Instance GenOfGenSized {A} `{GenSized A} : Gen A :=
  {| arbitrary := sized arbitrarySized |}.

#[global] Instance ArbitraryOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A := {}.

Generalizable Variables PSized PMon PSMon PCorr.

#[global] Instance GenMonotonicOfSized (A : Type)
         `{H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H ProducerGen PSMon}
  : @GenMonotonic A
                  (@GenOfGenSized A H) 
                  (@sizedSizeMonotonic G ProducerGen _ A
                                       (@arbitrarySized A H)
                                       PMon PSMon) := {}.

#[global] Instance GenCorrectOfSized (A : Type)
         {H : GenSized A}
         `{@GenSizedMonotonic A H PMon}
         `{@GenSizedSizeMonotonic A H ProducerGen PSMon}
         `{@GenSizedCorrect A H PCorr} : Correct A arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; now eauto with typeclass_instances.
  - destruct PCorr. 
    rewrite <- prodCorrectSized0. 

    split. intros [n [? H3]]. eexists. eassumption.

    intros [s H4]. eexists; split; eauto. reflexivity.
Qed.

(* 
Lemma nat_set_ind (A : Type) `{GenSized A} `{Hyp : CanonicalSized A} :
  (semProd (arbitrarySized 0) <--> zeroSized) ->
  (forall (s : nat) (elems : set A),
     semProd (arbitrarySized s) <--> elems ->
     semProd (arbitrarySized (s.+1)) <--> succSized elems) ->
  (forall s : nat, semProd (arbitrarySized s) <--> (fun x : A => size x <= s)).
Proof.
  intros HO IH. intros n; induction n.
  - eapply set_eq_trans with (B := (fun x : A => size x = 0)).
    rewrite -zeroSized_spec //=.
    intros s. destruct (size s). now firstorder.
    split; intros; ssromega.
  - rewrite -succSized_spec. eauto.
Qed.
 *)

#[global] Instance EnumSizedMonotonicOfSizeMonotonic
         (A : Type) (Hgen : EnumSized A) (Hmon : forall s, @SizeMonotonic A E ProducerEnum (enumSized s))
: @EnumSizedMonotonic A Hgen Hmon := {}.
  
#[global] Instance EnumMonotonicOfSizeMonotonic
         (A : Type) (Hgen : Enum A) (Hmon : @SizeMonotonic A E ProducerEnum enum)
: @EnumMonotonic A Hgen Hmon := {}.

#[global] Instance EnumSizedCorrectOfSizedCorrect
         (A : Type) (Hgen : EnumSized A)
         `{Hcor : @CorrectSized A E ProducerEnum enumSized}
: @EnumSizedCorrect A Hgen Hcor := {}.

#[global] Instance EnumCorrectOfCorrect
         (A : Type) (Hgen : Enum A)
         `{Hcor : @Correct A E ProducerEnum enum}
: @EnumCorrect A Hgen Hcor := {}.

#[global] Instance EnumMonotonicCorrectOfMonotnicCorrect
         (A : Type) (Hgen : Enum A)
         (Hmon : @SizeMonotonic A E ProducerEnum enum)
         `{Hcor : @Correct A E ProducerEnum enum}
  : @EnumMonotonicCorrect A Hgen Hmon Hcor := {}.


#[global] Instance EnumSizedSizeMonotonicOfSizedMonotonic
         (A : Type) (Hgen : EnumSized A) (Hmon : @SizedMonotonic A E ProducerEnum enumSized)
: @EnumSizedSizeMonotonic A Hgen Hmon := {}.

#[global] Instance EnumOfEnumSized {A} `{EnumSized A} : Enum A :=
  {| enum := sized enumSized |}.

(*
#[global] Instance EnumOfGenShrink {A} `{Gen A} `{Shrink A} : Arbitrary A := {}.
 *)

#[global] Instance EnumMonotonicOfSized (A : Type)
         `{H : EnumSized A}
         `{@EnumSizedMonotonic A H PMon}
         `{@EnumSizedSizeMonotonic A H PSMon}
  : @EnumMonotonic A
                  (@EnumOfEnumSized A H)
                  (@sizedSizeMonotonic E ProducerEnum _ A
                                       (@enumSized A H)
                                       PMon PSMon) := {}.

#[global] Instance EnumCorrectOfSized' (A : Type)
         {H : EnumSized A}
         `{@EnumSizedMonotonic A H PMon}
         `{@EnumSizedSizeMonotonic A H PSMon}
         `{@EnumSizedCorrect A H PCorr} : Correct A enum.
Proof.
  constructor. unfold arbitrary, EnumOfEnumSized. 
  eapply set_eq_trans.
  - eapply semSized_alt; eauto with typeclass_instances.
  - destruct PCorr. 
    rewrite <- prodCorrectSized0. 

    split. intros [n [? H3]]. eexists. eassumption.

    intros [s H4]. eexists; split; eauto. reflexivity.
Qed.

#[global] Instance EnumCorrectOfSized (A : Type)
         (H1 : EnumSized A)
         (H3 : forall s : nat, SizeMonotonic (enumSized s))
         (H4 : SizedMonotonic enumSized)
         (H5 : CorrectSized enumSized)
  : Correct A enum.
Proof.
  eapply EnumCorrectOfSized'; eauto.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.


Lemma enumerating_complete A (e : E A) {Hc : Correct A e} ch :
  (exists x, ch x = Some true) ->
  exists s, enumerating e ch s = Some true.
Proof.
  intros [x Hch].
  unfold enumerating.
  assert (Hin : semProd e x).
  { eapply Hc. reflexivity. }
  destruct Hin as [s [_ Hsem]]. simpl in *.
  unfold semEnumSize in *.
  exists s. revert Hsem.
  generalize (Enumerators.run e s), false.
  induction l; intros b Hin; inv Hin; simpl.
  - rewrite Hch. reflexivity.
  - destruct (ch a); eauto.
    destruct b0; eauto.
Qed.

Lemma lazylist_backtrack_opt_is_true A (l: LazyList.LazyList (option A)) ch b :
  lazylist_backtrack_opt l ch true = Some b -> b = true. 
Proof.
  induction l.
  - simpl. congruence.
  - simpl in *.
    destruct a.
    + destruct (ch a) eqn:Heq. destruct b0. congruence.
      now eauto. now eauto.
    + eauto.
Qed. 

Lemma lazylist_backtrack_opt_is_false A (l: LazyList.LazyList (option A)) ch b :
  lazylist_backtrack_opt l ch b = Some false -> b = false. 
Proof.
  revert b; induction l; intros b.
  - simpl. destruct b; try congruence.
  - simpl in *. 
    destruct a.
    + destruct (ch a) eqn:Heq. destruct b0. congruence.
      now eauto. intros Hin. eapply H in Hin. congruence. 
    + intros Hn. eapply lazylist_backtrack_opt_is_true in Hn.
      congruence.
Qed. 

Lemma lazylist_backtrack_opt_true A (l: LazyList.LazyList (option A)) ch b :
  lazylist_backtrack_opt l ch b = Some true <->
  exists x, LazyList.In_ll (Some x) l /\ ch x = Some true.
Proof.
  revert b; induction l; intros b.
  - simpl. split; intros Hc; try congruence.
    destruct b; congruence. 
    destruct Hc. inv H; exfalso; eauto.
  - split.
    + intros Hl.
      simpl in *. destruct a.
      destruct (ch a) eqn:Heq.
      * destruct b0.
        -- eexists. split; eauto.
        -- eapply H in Hl. destruct Hl. inv H0.
           eexists; split; eauto.
      * eapply H in Hl. destruct Hl. inv H0.
        eexists; split; eauto.
      * eapply H in Hl. destruct Hl. inv H0.
        eexists; split; eauto.
    + intros Hc; inv Hc. inv H0. simpl in *. destruct a. 
      * inv H1. inv H3. rewrite H2. reflexivity.
        destruct (ch a) eqn:Heq. destruct b0. reflexivity.
        eapply H. eexists. now split; eauto.
        eapply H. eexists. now split; eauto.
      * inv H1. congruence. eapply H. eexists. now split; eauto.
Qed.

Lemma lazylist_backtrack_opt_false A (l: LazyList.LazyList (option A)) ch :
  lazylist_backtrack_opt l ch false = Some false <->
  (forall x, LazyList.In_ll (Some x) l -> ch x = Some false) /\
  ~ LazyList.In_ll None l.
Proof.
  induction l. 
  - simpl. split; intros Hc.
    split; eauto. intros. now inv H.
    reflexivity.
  - split.
    + intros Hl.
      simpl in *.
      destruct a.
      * destruct (ch a) eqn:Heq. destruct b.
        congruence.
        
        -- eapply H in Hl. inv Hl.
           split.
           intros. inv H2; eauto. inv H3. eassumption.

           intros Hc; inv Hc. congruence. eauto.

        -- eapply lazylist_backtrack_opt_is_false in Hl. congruence.

      * eapply lazylist_backtrack_opt_is_false in Hl. congruence.

    + intros [H1 H2].
      simpl.
      destruct a. 
      * destruct (ch a) eqn:Heq. destruct b.
        rewrite H1 in Heq. congruence.
        now left.
        eapply H. split. intros. eapply H1.
        right. eassumption.
        intros Hc. eapply H2. right. eassumption.
        rewrite H1 in Heq. congruence. now left.

      * exfalso. eapply H2. now left.
Qed.        
        

Lemma enumeratingOpt_monotonic A (e : E (option A))
      {Hc : SizeMonotonicOpt e} {Hfp : SizeFP e}
      ch1 ch2 s1 s2 b :
  (s1 <= s2)%coq_nat ->
  (forall x, ch1 x = Some b -> ch2 x = Some b) ->
  enumeratingOpt e ch1 s1 = Some b ->
  enumeratingOpt e ch2 s2 = Some b.
Proof.
  intros Hleq Hall Hen.

  specialize (Hc _ _ Hleq).
  specialize (Hfp _ _ Hleq).
  
  unfold enumeratingOpt in *.
  unfold semProdSizeOpt in *. simpl in *. 
  unfold semEnumSize in *.
  revert Hc Hfp Hen. 

  generalize (run e s1), (run e s2).

  intros l1 l2 Hs1 Hs2 Hl.
  destruct b.

  - eapply lazylist_backtrack_opt_true in Hl.
    destruct Hl. destruct H.

    eapply lazylist_backtrack_opt_true.
    eexists. split.
    eapply Hs1. eassumption.
    eapply Hall. eassumption.

  - eapply lazylist_backtrack_opt_false in Hl.
    destruct Hl. 

    eapply lazylist_backtrack_opt_false.

    split. intros x Hin. eapply Hall. eapply H.
    eapply Hs2. eassumption. eassumption.

    intros Hc. eapply H0. eapply Hs2. eassumption. eassumption.
Qed. 
