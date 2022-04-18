From QuickChick Require Import QuickChick Tactics TacticsUtil Instances
     Classes DependentClasses Sets.

Require Import String. Open Scope string.
Require Import List micromega.Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Set Bullet Behavior "Strict Subproofs".



Inductive tree A : Type :=
| Leaf : A -> tree A
| Leaf' : A -> A -> tree A
| Node : A -> tree A -> tree A -> tree A.


Derive GenSized for tree.


Instance GenTree_SizedMonotonic A {_ : Gen A} :
  SizedMonotonic (@arbitrarySized _ (@GenSizedtree A _)).
Proof.  derive_gen_SizedMonotonic (). Qed.

Instance GenTree_SizeMonotonic A `{GenMonotonic A} :
  forall s, SizeMonotonic (@arbitrarySized _ (@GenSizedtree A _) s).
Proof.  derive_gen_SizeMonotonic (). Qed.

Instance GenTree_correct A `{GenMonotonicCorrect A} :
  CorrectSized (@arbitrarySized _ (@GenSizedtree A _)).
Proof. derive_gen_Correct (). Qed.



Inductive tree1 :=
| Leaf1 : tree1
| Node1 : nat -> tree1 -> tree1 -> tree1.


Inductive bst : nat -> nat -> tree1 -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf1
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node1 n t1 t2).


Derive EnumSizedSuchThat for (fun m => le n m).
Derive ArbitrarySizedSuchThat for (fun m => le n m).

Derive DecOpt for (bst min max t).
Derive EnumSizedSuchThat for (fun t => bst min max t).
Derive ArbitrarySizedSuchThat for (fun t => bst min max t).

Instance GenSizedSuchThatbst_SizedMonotonic min max :
  SizedMonotonicOpt (@arbitrarySizeST _ _ (@GenSizedSuchThatbst min max)).
Proof. derive_genST_SizedMonotonic (). Qed.



Instance GenSizedSuchThatle_SizedMonotonic n :
  SizedMonotonicOpt (@arbitrarySizeST _ _ (@GenSizedSuchThatle n)).
Proof. derive_genST_SizedMonotonic (). Qed.

Instance GenSizedSuchThatle_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@arbitrarySizeST _ _ (@GenSizedSuchThatle n) s).
Proof. derive_genST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizeMonotonic min max :
  forall s, SizeMonotonicOpt (@arbitrarySizeST _ _ (@GenSizedSuchThatbst min max) s).
Proof. derive_genST_SizeMonotonic (). Qed.


Instance GenSizedSuchThatle_Correct n :
  CorrectSizedST [eta le n] (@arbitrarySizeST _ _ (@GenSizedSuchThatle n)).
Proof. derive_genST_Correct (). Qed.
  

 
Instance GenSizedSuchThatbst_Correct n m :
  CorrectSizedST (bst n m) (@arbitrarySizeST _ _ (@GenSizedSuchThatbst n m)).
Proof. derive_genST_Correct (). Qed.

