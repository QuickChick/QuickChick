From QuickChick Require Import QuickChick Tactics TacticsUtil Instances
     Classes DependentClasses Sets EnumProofs.

Require Import String. Open Scope string.
From Coq Require Import List Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Set Bullet Behavior "Strict Subproofs".

(** Examples *)

Inductive tree A : Type :=
| Leaf : A -> tree A
| Leaf' : A -> A -> tree A
| Node : A -> tree A -> tree A -> tree A.


Derive Instance EnumSized for tree.

#[local]
Instance EnumTree_SizedMonotonic A {_ : Enum A} :
  SizedMonotonic (@enumSized _ (@EnumSizedtree A _)).
Proof. derive_enum_SizedMonotonic (). Qed.
  
#[local]
Instance EnumTree_SizeMonotonic A `{EnumMonotonic A} :
  forall s, SizeMonotonic (@enumSized _ (@EnumSizedtree A _) s).
Proof. derive_enum_SizeMonotonic (). Qed. 

#[local]
Instance EnumTree_correct A `{EnumMonotonicCorrect A} :
  CorrectSized (@enumSized _ (@EnumSizedtree A _)).
Proof. derive_enum_Correct (). Qed. 

Inductive Foo : Type :=
| Bar.

Derive Instance EnumSized for Foo.

#[local]
Instance EnumFoo_SizedMonotonic :
  SizedMonotonic (@enumSized _ EnumSizedFoo).
Proof. derive_enum_SizedMonotonic (). Qed.
  
#[local]
Instance EnumFoo_SizeMonotonic :
  forall s, SizeMonotonic (@enumSized _ EnumSizedFoo s).
Proof. derive_enum_SizeMonotonic (). Qed. 

#[local]
Instance EnumFoo_correct :
  CorrectSized (@enumSized _ EnumSizedFoo).
Proof. derive_enum_Correct (). Qed. 


Inductive Foo2 A : Type :=
| Bar1
| Bar2 : A -> Foo2 A.


Derive Instance EnumSized for Foo2.

#[local]
Instance EnumFoo2_SizedMonotonic A {_ : Enum A} :
  SizedMonotonic (@enumSized _ (@EnumSizedFoo2 A _)).
Proof. derive_enum_SizedMonotonic (). Qed.
  
#[local]
Instance EnumFoo2_SizeMonotonic A `{EnumMonotonic A} :
  forall s, SizeMonotonic (@enumSized _ (@EnumSizedFoo2 A _) s).
Proof. derive_enum_SizeMonotonic (). Qed. 

#[local]
Instance EnumFoo2_correct A `{EnumMonotonicCorrect A} :
  CorrectSized (@enumSized _ (@EnumSizedFoo2 A _)).
Proof. derive_enum_Correct (). Qed. 


(* Example with two IH *)
Inductive goodTree : nat -> tree nat  -> Prop :=
| GL : goodTree 0 (Leaf nat 0)
| GN :
    forall k t1 t2 n m,
      goodTree n t1 ->
      goodTree m t2 ->
      goodTree m t1 ->
      goodTree (S n) (Node nat k t1 t2).
