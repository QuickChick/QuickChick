Require Import AbstractGen SetOfOutcomes.
Require Import List ssreflect ssrbool ssrnat seq.

(* Experiment on properly tracking sizes
   Conclusion: this seems too complicated to be worth the trouble *)

Class Sized {A : Type} := {
  size : A -> nat
}.

(* BoundedPred n = A set of elements with size at most n *)
Definition below n {A :Type} `{Sized A} (P : Pred A) : Prop :=
  forall a, P a -> size a <= n.

Definition BoundedPred n A `{Sized A} : Type :=
  {P : Pred A | below n P}.

(* SizedPred = A sized-indexed family *)
Definition SizedPred A `{Sized A} :=
  forall n : nat, BoundedPred n A.

(* Type of sized incompatible with signature in AbstractGen *)
Program Definition sized {A} `{Sized A} (f : SizedPred A) : Pred A :=
  fun a => exists n, f n a. (* The union over all ns of f n *)

(* A non-trivial(?) propery of sized *)

Program Definition total {A} `{Sized A} n  : BoundedPred n A :=
  fun a => size a <= n.
Next Obligation. unfold below. auto. Qed.

Lemma sized_total : forall A `{Sized A},
  peq (sized total) (fun _ => True).
Proof.
  intros A H a. split; intro H'. trivial.
  unfold sized, total. simpl. exists (size a). by [].
Qed.

(* Conclusion: resize is an internal implemetation detail of
   QuickCheck and shouldn't be exposed in AbstractGen; it doesn't make
   much sense in the sets of outcomes word *)
(* Type of resize incompatible with signature in AbstractGen *)
Definition resize {A} `{Sized A} (n : nat)
  (f : SizedPred A) : BoundedPred n A := f n.

(* Can't go in the other direction
Definition convert {A} `{Sized A} {n} (bp : BoundedPred n A) : SizedPred A :=
  fun _ => bp.
*)

(* Was trying to write some property of resize, but none of the ones
   we could think of would even type-check in this setting

Lemma sized_resize : forall {A} `{Sized A} n f,
  resize n (sized f) = f n.
The term "sized f" has type "Pred A" while it is expected to have type
 "SizedPred A".

Lemma resize_multiple : forall n m g,
  resize n (resize m g) = resize m g.
The term "resize m g" has type "BoundedPred m ?69"
 while it is expected to have type "SizedPred ?65".
*)
