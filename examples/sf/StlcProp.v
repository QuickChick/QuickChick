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

Require Import Smallstep.
Require Import Stlc.

Lemma canonical_forms_bool : forall t,
  empty |- t \typ TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Admitted.  (* QuickChick canonical_forms_bool. *)

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \typ (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Admitted. (* Existential *)

Theorem progress : forall t T,
     empty |- t \typ T ->
     value t \/ exists t', t ===> t'.
Admitted. (* Existential *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall i,
      appears_free_in i (tvar i)
  | afi_app1 : forall i t1 t2,
      appears_free_in i t1 -> appears_free_in i (tapp t1 t2)
  | afi_app2 : forall i t1 t2,
      appears_free_in i t2 -> appears_free_in i (tapp t1 t2)
  | afi_abs : forall i y T11 t12,
      y <> i  ->
      appears_free_in i t12 ->
      appears_free_in i (tabs y T11 t12)
  | afi_if1 : forall i t1 t2 t3,
      appears_free_in i t1 ->
      appears_free_in i (tif t1 t2 t3)
  | afi_if2 : forall i t1 t2 t3,
      appears_free_in i t2 ->
      appears_free_in i (tif t1 t2 t3)
  | afi_if3 : forall i t1 t2 t3,
      appears_free_in i t3 ->
      appears_free_in i (tif t1 t2 t3).

Hint Constructors appears_free_in.

Derive ArbitrarySizedSuchThat for (fun i => appears_free_in i t).
Derive SizeMonotonicSuchThatOpt for (fun i => appears_free_in i t).
(* Zoe!
Derive SizedProofEqs for (fun i => appears_free_in i t).
Derive GenSizedSuchThatCorrect for (fun i => appears_free_in i t).
Derive GenSizedSuchThatSizeMonotonicOpt for (fun i => appears_free_in i t).
*)
Instance appears_free_in_gen_correct t : SuchThatCorrect (fun i => appears_free_in i t) 
                                                         (@arbitraryST _ (fun i => appears_free_in i t) _).
Admitted.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Instance dec_closed t : Dec (closed t). Admitted.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \typ T ->
   exists T', bind Gamma x T'.
Admitted. (* Existential *)

Corollary typable_empty__closed : forall t T,
    empty |- t \typ T  ->
    closed t.
Admitted. (* Todo dec: QuickChick typable_empty__closed. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     cons (x,U) Gamma |- t \typ T ->
     empty |- v \typ U   ->
     Gamma |- [x:=v]t \typ T.
Admitted. (* Todo has_type_Dec QuickChick substitution_preserves_typing. *)

Theorem preservation : forall t t' T,
     empty |- t \typ T  ->
     t ===> t'  ->
     empty |- t' \typ T.
Admitted. (* Out of scope - step to a function *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \typ T ->
  t ===>* t' ->
  ~(stuck t').
Admitted. (* Existential *)

