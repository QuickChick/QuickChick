From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes
     DependentClasses Sets EnumProofs.

Require Import String. Open Scope string.
Require Import List micromega.Lia.
Require Import enumProofs. 

Import ListNotations.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

From Ltac2 Require Import Ltac2.

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n m, m = n * n -> square_of n m.

Derive EnumSizedSuchThat for (fun x => square_of x n).

Inductive tree1 :=
| Leaf1 : tree1
| Node1 : nat -> tree1 -> tree1 -> tree1.

Inductive perfect' : nat -> tree1 -> Prop :=
| PerfectLeaf : perfect' 0 Leaf1
| PerfectNode : forall x l r n, perfect' n l -> perfect' n r ->
                                perfect' (S n) (Node1 x l r).

Derive DecOpt for (perfect' n t).

Derive EnumSizedSuchThat for (fun n => perfect' n t).

Inductive perfect : tree1 -> Prop :=
| Perfect : forall n t, perfect' n t -> perfect t.

Derive DecOpt for (perfect t).

Lemma semProdSizeOpt_bicupNone A s (S : set A) :
  \bigcup_(x in [:: returnEnum (@None A)]) semProdSizeOpt x s \subset S.
Proof.
  intros x Hin. inv Hin. inv H. inv H0.
  - inv H1. congruence.
    inv H.
  - inv H.
Qed.

Set Bullet Behavior "Strict Subproofs".

Inductive In' {A} : A -> list A -> Prop :=
| In_hd :
    forall x l, In' x (cons x l)
| In_tl :
    forall x y l, In' x l -> In' x (cons y l).


Derive DecOpt for (In' a l).
 
Instance DecOptIn'_listSizeMonotonic A {_ : Enum A} {_ : Dec_Eq A}
         (x : A) (l : list A) : DecOptSizeMonotonic (In' x l).
Proof. derive_mon (). Qed.

Instance DecOptIn'_list_sound A {_ : Enum A} {_ : Dec_Eq A} (x : A) (l : list A) :
  DecOptSoundPos (In' x l).
Proof. derive_sound (). Qed.

Instance DecOptIn'_list_complete A {_ : Enum A} {_ : Dec_Eq A} (x : A) (l : list A) :
  DecOptCompletePos (In' x l).
Proof. derive_complete (). Qed.

Derive ArbitrarySizedSuchThat for (fun x => In' x l).
Derive EnumSizedSuchThat for (fun x => In' x l).

Instance EnumSizedSuchThatIn'_SizedMonotonic A {_ : Enum A} {_ : Dec_Eq A} l :
  SizedMonotonicOpt (@enumSizeST A _ (EnumSizedSuchThatIn' l)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatIn'_SizeMonotonic  A {_ : Enum A} {_ : Dec_Eq A}
         (* `{EnumMonotonic A} *) l :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThatIn' l) s).
Proof. derive_enumST_SizeMonotonic (). Qed.


Instance EnumSizedSuchThatIn'_Correct A {_ : Enum A}  {_ : Dec_Eq A}
         (* `{EnumMonotonicCorrect A} *) l :
  CorrectSizedST (fun x => In' x l) (@enumSizeST _ _ (EnumSizedSuchThatIn' l)).
Proof. derive_enumST_Correct (). Qed.
 
Derive EnumSizedSuchThat for (fun l => In' x l).


Inductive bst : nat -> nat -> tree1 -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf1
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node1 n t1 t2).

Derive DecOpt for (le min max).
Derive EnumSizedSuchThat for (fun m => le n m).

Derive EnumSizedSuchThat for (fun t => bst min max t).

Derive ArbitrarySizedSuchThat for (fun m => le n m).
Derive ArbitrarySizedSuchThat for (fun t => bst min max t).

Derive DecOpt for (bst min max t).
  
Instance EnumSizedSuchThatle_SizedAMonotonic n :
  SizedMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_SizedMonotonicFP (). Qed. 

Instance EnumSizedSuchThatle_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizeMonotonicFP n :
  forall s, SizeMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatle n) s).
Proof. derive_enumST_SizeMonotonicFP (). Qed. 

(* XXX predicate must be eta expanded, otherwise typeclass resolution fails *)
Instance EnumSizedSuchThatle_Correct n :
  CorrectSizedST [eta le n] (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_Correct (). Qed.

Instance EnumSizedSuchThatbst_SizedMonotonicFP min max :
  SizedMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatbst min max)).
Proof. derive_enumST_SizedMonotonicFP (). Qed.

Instance EnumSizedSuchThatbst_SizedMonotonic min max :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max)).
Proof. derive_enumST_SizedMonotonic (). Qed.  

Instance EnumSizedSuchThatbst_SizeMonotonic min max :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizeMonotonicFP min max :
  forall s, SizeMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatbst min max) s).
Proof. derive_enumST_SizeMonotonicFP (). Qed.
  
Instance EnumSizedSuchThatbst_Correct n m :
  CorrectSizedST (bst n m) (@enumSizeST _ _ (@EnumSizedSuchThatbst n m)).
Proof. derive_enumST_Correct (). Qed.


(* XXX missing enum list instances. *) 
(* Instance EnumSizedSuchThatIn'0_SizedMonotonic A {_ : Enum A} x : *)
(*   SizedMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThatIn'0 x)). *)
(* Proof. derive_enumST_SizedMonotonic (). Qed. *)


Inductive ltest : list nat -> nat -> Prop :=
  | ltestnil :
      ltest [] 0
  | ltestcons :
      forall x m' m l,
        (m' + 1) = m ->
        (* In' m' l -> *)
        ltest l m' ->
        ltest (x :: l) m.


Derive EnumSizedSuchThat for (fun n => eq x n).
Derive EnumSizedSuchThat for (fun n => eq n x).

Derive DecOpt for (ltest l n).

Instance DecOptltest_listSizeMonotonic l x : DecOptSizeMonotonic (ltest l x).
Proof. derive_mon (). Qed.

Instance DecOptltest_listsound l x : DecOptSoundPos (ltest l x).
Proof. derive_sound (). Qed. 

Instance DecOptIn'ltest_complete A {_ : Enum A} {_ : Dec_Eq A} x l :
  DecOptCompletePos (ltest x l).
Proof. derive_complete (). Qed.

(* Set Typeclasses Debug. *)
(* QuickChickDebug Debug On. *)

(* XXX error *)
(* Derive EnumSizedSuchThat for (fun l => ltest l n). *)

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



Instance EnumSizedSuchThatgoodTree_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatgoodTree_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatgoodTree_SizedMonotonicFP n :
  SizedMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_SizedMonotonicFP (). Qed.
   
Instance EnumSizedSuchThatgoodTree_SizeMonotonicFP n :
  forall s, SizeMonotonicOptFP (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n) s).
Proof. derive_enumST_SizeMonotonicFP (). Qed.


Instance EnumSizedSuchThatgoodTree_Correct n :
  CorrectSizedST (goodTree n) (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_Correct (). Qed.
