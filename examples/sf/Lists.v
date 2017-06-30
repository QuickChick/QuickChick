(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import ZoeStuff.
(* End prelude *)

Require Export Induction.

Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Instance dec_natprod (p q : natprod) : Dec (p = q).
Proof. constructor; unfold decidable; repeat decide equality. Defined.

Derive (Arbitrary, Show) for natprod.
Derive (Sized, CanonicalSized) for natprod.
Derive SizeMonotonic for natprod using genSnatprod.
Derive SizedMonotonic for natprod.
(* ZOE: Derive SizedCorrect for natprod using genSnatprod and SizeMonotonicnatprod. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Admitted. (* QuickChick surjective_pairing'. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Admitted. (* QuickChick surjective_pairing. *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Admitted. (* QuickChick snd_fst_is_swap. *)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Admitted. (* QuickChick fst_swap_is_snd. *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Instance dec_natlist (p q : natlist) : Dec (p = q).
Proof. constructor; unfold decidable; repeat decide equality. Defined.

(* Leo: Not sure why (Arbitrary, Show) doesn't work here *)
Derive Arbitrary for natlist.
Derive Show for natlist.
Derive Sized for natlist.
Derive CanonicalSized for natlist.
Derive SizeMonotonic for natlist using genSnatlist.
Derive SizedMonotonic for natlist.
Derive SizedCorrect for natlist using genSnatlist and SizeMonotonicnatlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Admitted. (* QuickChick nil_app. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Admitted. (* QuickChick tl_length_pred. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Admitted. (* QuickChick app_assoc. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

(* rev_length_firsttry *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Admitted. (* QuickChick app_length. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Admitted. (* QuickChick rev_length. *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Admitted. (* QuickChick app_nil_r. *)

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Admitted. (* QuickChick rev_app_distr. *)

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Admitted. (* QuickChick rev_involutive. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Admitted. (* QuickChick app_assoc4. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Admitted. (* QuickChick ble_n_Sn. *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Instance dec_natoption (p q : natlist) : Dec (p = q).
Proof. constructor; unfold decidable; repeat decide equality. Defined.

Derive Arbitrary for natoption.
Derive Show for natoption.
Derive Sized for natoption.
Derive CanonicalSized for natoption.
Derive SizeMonotonic for natoption using genSnatoption.
Derive SizedMonotonic for natoption.
Derive SizedCorrect for natoption using genSnatoption and SizeMonotonicnatoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* Filled *)
Definition hd_error (l : natlist) : natoption :=
  match l with 
  | nil => None
  | a :: _ => Some a 
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Admitted. (* QuickChick option_elim_hd. *)

End NatList.

(* This is probably a poor choice with ssr *)
Inductive id : Type :=
  | Id : nat -> id.

Instance dec_id (p q : id) : Dec (p = q).
Proof. constructor; unfold decidable; repeat decide equality. Defined.

Derive Arbitrary for id.
Derive Show for id.
Derive Sized for id.
Derive CanonicalSized for id.
Derive SizeMonotonic for id using genSid.
Derive SizedMonotonic for id.
(* ZOE : again? Derive SizedCorrect for id using genSid and SizeMonotonicid. *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Admitted. (* QuickChick beq_id_refl. *)

(* LEO: Continue *)
Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or by applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
    partial map (or adds a new entry if the given key is not already
    present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.


(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)
End PartialMap.

(** **** Exercise: 2 starsM (baz_num_elts)  *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?  (Answer in English
    or the natural language of your choice.)

(* FILL IN HERE *)
*)
(** [] *)

(** $Date: 2016-12-17 23:53:20 -0500 (Sat, 17 Dec 2016) $ *)

