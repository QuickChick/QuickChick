From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes
     DependentClasses Sets EnumProofs.

Require Import String. Open Scope string.
Require Import List micromega.Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import enumProofs. (* TODO change *)

Set Bullet Behavior "Strict Subproofs".


(* Inductive mylist (A : Type) : Type := *)
(*     mynil : mylist A | mycons : A -> mylist A -> mylist A. *)

(* Derive EnumSized for mylist. *)

Inductive In' : nat -> list nat -> Prop :=
| In_hd :
    forall x l, In' x (cons x l)
| In_tl :
    forall x y l, In' x l -> In' x (cons y l).

(* (* XXX BUG *) *)
Derive DecOpt for (In' a l).
Derive ArbitrarySizedSuchThat for (fun x => In' x l).
Derive EnumSizedSuchThat for (fun x => In' x l).

Inductive ltest : list nat -> nat -> Prop :=
  | ltestnil :
      ltest [] 0
  | ltestcons :
      forall x m' m l,
        (* eq (m' + 1) m -> *)
        In' m' l ->
        ltest l m' ->
        ltest (x :: l) m.

Derive EnumSizedSuchThat for (fun n => eq x n).
Derive EnumSizedSuchThat for (fun n => eq n x).

(* Derive DecOpt for (ltest l n). *)

(* Derive EnumSizedSuchThat for (fun n => ltest l n). *)


Set Typeclasses Debug.
QuickChickDebug Debug On.

Derive DecOpt for (ltest l n).


  
Derive EnumSizedSuchThat for (fun n => le m n).

Inductive goodTree : nat -> tree nat  -> Prop :=
| GL : forall a, goodTree 0 (Leaf nat a)
| GN :
    forall k t1 t2 n (* m : nat)*),
      (* le m n -> *)
      goodTree n t1 ->
      goodTree n t1 ->
      goodTree (S n) (Node nat k t1 t2).

Derive DecOpt for (goodTree n t).

(* XXX this fails if tree has type param A ... *) 

Instance DecOptgoodTree_listSizeMonotonic n t : DecOptSizeMonotonic (goodTree n t).
Proof. derive_mon (). Qed.

Instance DecOptgoodTree_list_sound n t : DecOptSoundPos (goodTree n t).
Proof. derive_sound (). Qed.

Instance DecOptgoodTree_list_complete n t : DecOptCompletePos (goodTree n t).
Proof. derive_complete (). Qed.

Derive EnumSizedSuchThat for (fun t => goodTree k t).


Inductive tree1 :=
| Leaf1 : tree1
| Node1 : nat -> tree1 -> tree1 -> tree1.


Inductive bst : nat -> nat -> tree1 -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf1
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node1 n t1 t2).


Derive DecOpt for (bst min max t).


Derive EnumSizedSuchThat for (fun t => bst min max t).



Instance EnumSizedSuchThatgoodTree_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizedMonotonic min max :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max)).
Proof. derive_enumST_SizedMonotonic (). Qed.  


Instance EnumSizedSuchThatgoodTree_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizeMonotonic min max :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max) s).
Proof. derive_enumST_SizeMonotonic (). Qed.


(* XXX predicate must be eta expanded, otherwise typeclass resolution fails *)
Instance EnumSizedSuchThatle_Correct n :
  CorrectSizedST [eta le n] (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_Correct (). Qed.


Instance EnumSizedSuchThatgoodTree_Correct n :
  CorrectSizedST (goodTree n) (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_Correct (). Qed.  



Instance EnumSizedSuchThatbst_Correct n m :
  CorrectSizedST (bst n m) (@enumSizeST _ _ (@EnumSizedSuchThatbst n m)).
Proof. derive_enumST_Correct (). Qed.
