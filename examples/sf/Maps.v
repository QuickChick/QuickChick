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

Require Import Ascii String.

Derive (Arbitrary, Show) for ascii.
Derive (Sized, CanonicalSized) for ascii.
Derive SizeMonotonic for ascii using genSascii.
Derive SizedMonotonic for ascii.
(* Zoe: Derive SizedCorrect for ascii using genSascii and SizeMonotonicascii. *)

Derive (Arbitrary, Show) for string.
Derive (Sized, CanonicalSized) for string.
Derive SizeMonotonic for string using genSstring.
Derive SizedMonotonic for string.


Inductive id : Type :=
  | Id : string -> id.

Derive (Arbitrary, Show) for id.
Derive (Sized, CanonicalSized) for id.
Derive SizeMonotonic for id using genSid.
Derive SizedMonotonic for id.
(* ZOEEE : Derive SizedCorrect for id using genSid and SizeMonotonicid.*)

Instance eq_dec_id (x y : id) : Dec (x = y).
constructor; unfold decidable. repeat decide equality. Defined.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Admitted. (* QuickChick beq_id_refl. *) 

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Admitted. (* Prop *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Admitted. (* Prop *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Admitted. (* Leo: TODO *) 

(* Maps as functions are bad, explicit maps instead *)

Definition partial_map := list (id * nat).

Definition empty : partial_map := nil.

Definition update := @cons (id * nat).

Inductive bind : partial_map -> id -> nat -> Prop :=
  | BindNow   : forall x a m, bind (cons (x, a) m) x a
  | BindLater : forall x x' a a' m',
                  ~ (x = x') ->
                  bind m' x a -> 
                  bind (cons (x',a') m') x a.

Derive ArbitrarySizedSuchThat for (fun x => bind m x a).
Derive SizeMonotonicSuchThatOpt for (fun x => bind m x a).

(* ZOE!
Derive SizedProofEqs for (fun x => bind m x a).
Derive GenSizedSuchThatCorrect for (fun x => bind m x a).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun x => bind m x a).
*)
Instance adm_st m a : SuchThatCorrect (fun x => bind m x a) (genST (fun x => bind m x a)).
Admitted.

Instance checkFalse : Checkable False := {| checker := fun _ => checker false |}.

Instance bind_dec m x v : Dec (bind m x v) :=
  {| dec := _ |}.
Proof.
  move: x v.
  induction m => x v.
  - right => contra. inversion contra.
  - destruct a as [x' v'].
    destruct (eq_dec_id x x') as [[Eq | Neq]].
    + destruct (Dec_eq_nat v v') as [[EqV | NeqV]].
      * subst; left ; constructor; eauto.
      * subst; right => Contra.
        inversion Contra; subst; eauto.
    + subst; specialize (IHm x v).
      destruct IHm as [L | R].
      * left; constructor; eauto.
      * right => Contra; inversion Contra; subst; eauto.
Defined.

Conjecture apply_empty : forall x a, ~ (bind empty x a).
(* QuickChick apply_empty. *)
(* Gave Up! - QuickChick apply_empty_unfolded. *)

Conjecture update_eq : forall (m: partial_map) x v,
    bind (update (x,v) m) x v.
(* QuickChick update_eq. *)

Theorem update_neq : forall v x1 x2
                       (m : partial_map),
  x2 <> x1 ->
    forall v' v'', bind (cons (x2, v) m) x1 v' ->
                   bind m x1 v'' ->
                   v' = v''.
Admitted. (* Leo: TODO QuickChick update_neq. *)

(*
Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.
*) 

Definition total_map := (partial_map * nat)%type.

Definition t_empty v : total_map := (empty, v).

Definition t_update (m : partial_map) (d : nat) (x : id) (v : nat) :=
  (update (x, v) m, d).

Inductive t_bind : partial_map -> nat -> id -> nat -> Prop :=
  | T_BindDef   : forall x v, t_bind nil v x v
  | T_BindNow   : forall x a m d, t_bind (cons (x, a) m) d x a
  | T_BindLater : forall x x' a a' m' d,
                  ~ (x = x') ->
                  t_bind m' d x a -> 
                  t_bind (cons (x',a') m') d x a.

Derive ArbitrarySizedSuchThat for (fun x => t_bind m d x a).
Derive SizeMonotonicSuchThatOpt for (fun x => t_bind m d x a).

Instance adm_st' d m a : SuchThatCorrect (fun x => t_bind m d x a) (genST (fun x => t_bind m d x a)).
Admitted.

Lemma t_apply_empty:  forall x v v', t_bind empty v x v' -> v = v'.
Admitted. (* Leo TODO: suchtat4_2  QuickChick t_apply_empty. *)

Fixpoint lookup m x : option nat :=
  match m with 
  | nil => None
  | (x',v)::t => if (x = x') ? then Some v else lookup t x
  end.

Definition t_lookup (m : total_map) x := 
  let (m, d) := m in
  match lookup m x with
  | Some v => v
  | None => d
  end.
(*
Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_neq)  *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter [IndProp].  We begin
    by proving a fundamental _reflection lemma_ relating the equality
    proposition on [id]s with the boolean function [beq_id]. *)

(** **** Exercise: 2 stars, optional (beq_idP)  *)
(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now, given [id]s [x1] and [x2], we can use the [destruct (beq_idP
    x1 x2)] to simultaneously perform case analysis on the result of
    [beq_id x1 x2] and generate hypotheses about the equality (in the
    sense of [=]) of [x1] and [x2]. *)

(** **** Exercise: 2 stars (t_update_same)  *)
(** With the example in chapter [IndProp] as a template, use
    [beq_idP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

*)