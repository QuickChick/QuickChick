Require Import AbstractGen.
Require Import List ssreflect ssrbool ssrnat seq.

Definition Pred (A : Type) := A -> Prop. 

Class Sized {A : Type} := {
  size : A -> nat
}.

(* SizedPred n = A set of elements with size at most n *)
Definition below n {A :Type} `{Sized A} (P : Pred A) : Prop :=
  forall a, P a -> size a <= n.

Definition BoundedPred n A `{Sized A} : Type :=
  {P : Pred A | below n P}.

Definition SizedPred A `{Sized A} :=
  forall n : nat, BoundedPred n A.

(* Incompatible type *)
Program Definition sized {A} `{Sized A} (f : SizedPred A) : Pred A :=
  fun a => exists n, f n a. (* The union over all ns of f n *)

(* Properties of sized *)
Program Lemma silly1 : forall A `{Sized A} f (a : A),
  (sized f) a -> exists n, f n a.
Proof. trivial. Qed.

(* Incompatible type *)
Definition resize {A} `{Sized A} (n : nat)
  (f : SizedPred A) : BoundedPred n A := f n.

(* Equivalence on sets of outcomes *) 
Definition peq {A} (m1 m2 : Pred A) := 
  forall A, m1 A <-> m2 A.

(* the set of outcomes m1 is a subset of m2 *) 
Definition pincl {A} (m1 m2 : Pred A) :=
  forall A, m1 A -> m2 A. 

Program Definition total {A} `{Sized A} n  : BoundedPred n A :=
  fun a => size a <= n.
Next Obligation. unfold below. auto. Qed.

Lemma sized_total : forall A `{Sized A},
  peq (sized total)
      (fun _ => True).
Proof.
  intros A H a. split; intro H'. trivial.
  unfold sized, total. simpl. exists (size a). by [].
Qed.

(* Can't go in the other direction
Definition convert {A} `{Sized A} {n} (bp : BoundedPred n A) : SizedPred A :=
  fun _ => bp.
*)

(*
Lemma resize_multiple : forall n m g,
  resize n (resize m g) = resize m g.
The term "resize m g" has type "BoundedPred m ?69"
 while it is expected to have type "SizedPred ?65".
*)
