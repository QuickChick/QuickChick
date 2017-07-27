Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Checker.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

(* Class wrapper around "decidable" *)
(* begin decidable_class *)
    Class Dec (P : Prop) : Type := { dec : decidable P }.
(* end decidable_class *)

(* BCP: If I understand correctly, removing "Global" everywhere would
   change nothing... Or? *)

(* Additional Checkable instance *)
Global Instance testDec {P} `{H : Dec P} : Checkable P :=
  {|
    checker p := _
  |}.
Proof.
  destruct H.
  destruct dec0.
  - exact (checker true).
  - exact (checker false).
Defined.

Global Instance Dec_neg {P} {H : Dec P} : Dec (~ P).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D; auto.
Defined.

Global Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

Global Instance Dec_disj {P Q} {H : Dec P} {I : Dec Q} : Dec (P \/ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

(* BCP: Not clear this is a good idea, but... *)
(* Leo: Should be ok with really low priority *)
Global Instance Dec_impl {P Q} {H : Dec P} {I : Dec Q} : Dec (P -> Q) | 100.
Proof.
  constructor. unfold decidable.
  destruct H as [D]. destruct D; destruct I as [D]; destruct D; auto.
  left. intros. contradiction. 
Defined.

Global Instance Dec_In {A} (Eq: forall (x y : A), Dec (x = y))
         (x : A) (l : list A) : Dec (In x l) := 
  {| dec := in_dec (fun x' y' => @dec _ (Eq x' y')) x l |}.

Class Eq (A : Type) :=
  { 
    dec_eq : forall (x y : A), decidable (x = y)
  }.

Global Instance Eq__Dec {A} `{H : Eq A} (x y : A) : Dec (x = y) :=
  {|
    dec := _
  |}.
Proof.
  unfold decidable.
  apply H.
Defined.

(* Lifting common decidable instances *)
Global Instance Dec_eq_bool (x y : bool) : Dec (x = y).
Proof. constructor; unfold decidable; decide equality. Defined.

Global Instance Dec_eq_nat (m n : nat) : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
Defined.

Global Instance Dec_eq_opt (A : Type) (m n : option A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H.
Defined.

Global Instance Dec_eq_prod (A B : Type) (m n : A * B)
  `{_ : forall (x y : A), Dec (x = y)} 
  `{_ : forall (x y : B), Dec (x = y)} 
  : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H0. apply H.
Defined.

Global Instance Dec_eq_list (A : Type) (m n : list A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof.
  constructor.
  unfold decidable.
  decide equality.
  apply H.
Defined.

Definition ascii_to_list (x : Ascii.ascii) : list bool.
Proof.
  destruct x.
  apply (cons b (cons b0 (cons b1 (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 nil)))))))).
Defined.

Lemma list_eq_imp_ascii_eq (c1 c2 : Ascii.ascii) :
  ascii_to_list c1 = ascii_to_list c2 -> c1 = c2.
Proof.
  intros. destruct c1; destruct c2. simpl in H.
  inversion H; clear H; subst. reflexivity.
Defined.

Lemma dec_ascii (m n : Ascii.ascii) : {m = n} + {m <> n}.
Proof.
  assert ({ascii_to_list m = ascii_to_list n} + {ascii_to_list m <> ascii_to_list n}).
  { apply Dec_eq_list. apply Dec_eq_bool. }
  destruct H.
  - left. apply list_eq_imp_ascii_eq. auto.
  - right. intro. apply n0. subst. reflexivity.
Defined.
Hint Resolve dec_ascii.

Global Instance Dec_ascii (m n : Ascii.ascii) : Dec (m = n).
Proof. constructor. unfold ssrbool.decidable. apply dec_ascii. Defined.

Global Instance Dec_string (m n : string) : Dec (m = n).
Proof.
  constructor.
  unfold ssrbool.decidable.
  repeat decide equality. 
Defined.

(* Everything that uses the Decidable Class *)
Require Import DecidableClass.

Instance dec_class_dec P (H : Decidable P): Dec P.
Proof.
  constructor; destruct H; destruct Decidable_witness.
  - left; auto.
    apply Decidable_spec; auto.
  - right => H; eauto.
    apply Decidable_spec in H.
    inversion H.
Defined.

(*
Example foo (m n : nat) := 
  match @dec (m = n) _ with 
    | left  _ => 0 
    | right _ => 1
  end.

(* Eval compute in foo 0 1. *)
Example bar (m n : nat) := 
  if (m=n)? then 0 else 1.

(* Eval compute in bar 0 1. *)
*)


(* Not sure about the level or binding, but good idea *)
Notation "P '?'" := (match (@dec P _) with 
                       | left _ => true
                       | right _ => false
                     end) (at level 100).

Compute ((42 = 42)?).
