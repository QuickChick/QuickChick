Require Import String List.

From QuickChick Require Import QuickChick Tactics.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import classes.
Import GenLow GenHigh Tactics Sets Arbitrary.
Import GenLow GenHigh.
Import ListNotations.
Import QcDefaultNotation.

Open Scope qc_scope.
Open Scope string.

Set Bullet Behavior "Strict Subproofs".

(* Decidability classes *)
(* TODO (maybe): Find a way to unify these? *)
Class DepDec1 {A : Type} (P : A -> Prop) :=
  {
    depDec1 : forall (x : A), {P x} + {~ (P x)}
  }.

Class DepDec2 {A B : Type} (P : A -> B -> Prop) :=
  {
    depDec2 : forall (x : A) (y : B), {P x y} + {~ (P x y)}
  }.

Class DepDec3 {A B C : Type} (P : A -> B -> C -> Prop) :=
  {
    depDec3 : forall (x : A) (y : B) (z : C), {P x y z} + {~ (P x y z)}
  }.

Class DepDec (P : Prop) := 
  { depDec : {P} + {~ P} }.

Instance eq_dec_test (x y : nat) : DepDec (x = y) := 
  {| depDec := _ |}.
Proof.  
  decide equality.
Defined.

Definition foo (m n : nat) := 
  if @depDec (m = n) _ then 0 else 1.

Eval compute in foo 0 1.

Notation " 'dec' P " := (@depDec P _) (at level 70).

Definition bar (m n : nat) := if dec (m = n) then 0 else 1.

Eval compute in bar 0 1.

Instance DepDec_Fun {A} (x : A) (P : A -> Prop) `{_ : DepDec (P x)} : DepDec (forall x, P x) := 
  {| depDec := _ |}.
Proof.
