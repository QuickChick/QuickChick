From Coq Require Import Init.Nat Lia List.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssreflect.eqtype ssrnat.
Import QcNotation. Import QcDefaultNotation.
Import ListNotations.

Require Import QuickChick.TacticsUtil ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.

From Ltac2 Require Import Ltac2.

(* Inductive not_In {A: Type} : A -> list A -> Prop := *)
(* | In_nil: forall x, not_In x [] *)
(* | In_cons : forall x y l, *)
(*     x <> y -> not_In x l -> not_In x (y :: l).  *)

(* XXX Leo DEBUG params *)

(* This gives an unsound enum *)

(* Inductive not_In : nat -> list nat -> Prop := *)
(* | In_nil: forall x, not_In x [] *)
(* | In_cons : forall x y l, *)
(*     x <> y -> not_In x l -> not_In x (y :: l). *)

(* XXX Leo DEBUG *)

Inductive not_In : nat -> list nat -> Prop :=
| In_nil: forall x, not_In x []
| In_cons : forall x y l,
    not_In x l -> x <> y -> not_In x (y :: l).

Derive DecOpt for (not_In x l).


Instance not_In_SizeMonotonic x l : DecOptSizeMonotonic (not_In x l).
Proof. derive_mon (). Qed.

Instance not_In__sound x l : DecOptSoundPos (not_In x l).
Proof. derive_sound (). Qed.

Instance not_In_complete x l : DecOptCompletePos (not_In x l).
Proof. derive_complete (). Qed.
       

Derive EnumSizedSuchThat for (fun x => eq x n).

Instance EnumSizedSuchThateq_SizedMonotonic X {_ : Enum X} (n : X) :
  SizedMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThateq n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThateq_SizeMonotonic X `{_ : EnumMonotonic X} (n : X) :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThateq n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThateq_Correct X `{_ : EnumMonotonicCorrect X} (n : X) :
  CorrectSizedST (fun m => eq n m) (@enumSizeST _ _ (EnumSizedSuchThateq n)).
Proof. derive_enumST_Correct (). Qed.

Derive EnumSizedSuchThat for (fun n => not_In n l).

Instance EnumSizedSuchThatnot_In_SizedMonotonic l :
  SizedMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThatnot_In l)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatnot_In_SizeMonotonic l :
    forall s, SizeMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThatnot_In l) s).
Proof. derive_enumST_SizeMonotonic (). Qed.


Instance EnumSizedSuchThatnot_In_Correct l :
    CorrectSizedST (fun n => not_In n l) (@enumSizeST _ _ (EnumSizedSuchThatnot_In l)).
Proof. derive_enumST_Correct (). Qed.

