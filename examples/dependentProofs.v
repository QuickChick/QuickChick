From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.
Require Import List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Set Bullet Behavior "Strict Subproofs".

Instance bindOptMonotonic
        {A B} (g : G (option A)) (f : A -> G (option B))
        `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
  SizeMonotonic (bindGenOpt g f).
Admitted.

Instance suchThatMaybeMonotonic
         {A : Type} (g : G A) (f : A -> bool) `{SizeMonotonic _ g} : 
  SizeMonotonic (suchThatMaybe g f).
Admitted.

Instance suchThatMaybeOptMonotonic
         {A : Type} (g : G (option A)) (f : A -> bool) `{SizeMonotonic _ g} : 
  SizeMonotonic (suchThatMaybeOpt g f).
Admitted.

Lemma bigcap_setU_l:
  forall (U T : Type) (s1 s2 : set U) (f : U -> set T),
    \bigcap_(i in s1) f i :&: \bigcap_(i in s2) f i <--> \bigcap_(i in s1 :|: s2) f i.
Proof.
  intros. split.
  - intros [ H1 H2 ] x [ H3 | H3 ]; eauto.
  - intros H. split; intros x H3; eapply H.
    now left. now right.
Qed.


(* Instance frequencySizeMonotonic_alt  *)
(* : forall {A : Type} (g0 : G A) (lg : seq (nat * G A)), *)
(*     SizeMonotonic g0 -> *)
(*     lg \subset [set x | SizeMonotonic x.2 ] -> *)
(*     SizeMonotonic (frequency g0 lg). *)
(* Admitted. *)

(* Lemma semFreqSize : *)
(*   forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)) (size : nat), *)
(*     semGenSize (freq ((fst ng, snd ng) ;; l)) size <--> *)
(*     \bigcup_(x in (ng :: l)) semGenSize x.2 size. *)
(* Admitted. *)

Typeclasses eauto := debug.

Require Import zoo DependentTest.

Lemma eq_symm {A : Type} (x y : A) :
  x = y -> y = x.
Proof.
  firstorder.
Qed.

Lemma plus_leq_compat_l n m k :
  n <= m ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma plus_leq_compat_r n m k :
  n <= k ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma leq_refl: forall n, n <= n.
Proof.
  intros. ssromega.
Qed.

(* Yikes this is stupid, find a workaround *)
Definition prop := Prop.


Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.


(* Example with two IH *)

Inductive goodTree : nat -> tree -> Prop :=
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n m, goodTree n t1 ->
                      goodTree m t2 ->
                      goodTree m t1 ->
                      goodTree (S n) (Node k t1 t2).

Instance DecgoodTree (n : nat) (t : tree) : Dec (goodTree n t).
Admitted.

Instance DecTreeEq (t1 t2 : tree) : Dec (t1 = t2).
Admitted.


Derive ArbitrarySizedSuchThat for (fun foo => goodTree n foo).

Derive SizedProofEqs for (fun foo => goodTree n foo).

Derive SizeMonotonicSuchThatOpt for (fun foo => goodTree n foo).


Lemma succ_neq_zero :
  forall x, S x <> 0.
Proof.
  firstorder.
Qed.

Lemma isSomeSome {A : Type} (y : A) :
  Some y.
Proof.
  exact isT.
Qed.

Lemma semBacktrack:
  forall (A : Type) (l : seq (nat * G (option A))),
    semGen (backtrack l) <-->
    (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGen x.2))) :|:
    ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGen x.2))).
Admitted.


Lemma semSuchThatMaybe_complete:
  forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
    s \subset semGen g ->
    (Some @: (s :&: (fun x : A => f x))) \subset
    semGen (suchThatMaybe g f).
Proof.
Admitted.

Lemma semSuchThatMaybeOpt_complete:
  forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
    (Some @: s) \subset semGen g ->
    (Some @: (s :&: (fun x : A => f x))) \subset
    semGen (suchThatMaybeOpt g f).
Proof.
Admitted.

Lemma semSuchThatMaybe_sound:
  forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
    semGen g \subset s ->
    semGen (suchThatMaybe g f) \subset ((Some @: (s :&: (fun x : A => f x))) :|: [set None]).
Proof.
Admitted.

Lemma semSuchThatMaybeOpt_sound:
  forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
    semGen g \subset ((Some @: s) :|: [set None]) ->
    semGen (suchThatMaybeOpt g f) \subset (Some @: (s :&: (fun x : A => f x)) :|: [set None]).
Proof.
Admitted.

(* QuickChickDebug Debug On. *)

(* Derive GenSizedSuchThatCorrect for (fun foo => goodTree n foo). *)

(* XXX these instances should be present *)
Existing Instance genSFoo.
Existing Instance shrFoo.
Derive SizeMonotonic for Foo using genSFoo.
Derive SizedMonotonic for Foo using genSFoo.
Derive Sized for Foo.

(* TODO fix oneof, admitting for now *)
(* Derive SizedCorrect for Foo using genSFoo and SizeMonotonicFoo. *)

Instance lala : SizedCorrect (@arbitrarySized Foo _).
Admitted.

Existing Instance GenSizedSuchThatgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooUnif n foo). *)

(* Interesting. Do we need  Global instance?? *) 
Existing Instance GenSizedSuchThatgoodFooNarrow.  (* Why???? *)

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooNarrow n foo).

Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooNarrow n foo). *)

Existing Instance GenSizedSuchThatgoodFooCombo.

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooCombo n foo).

Derive SizedProofEqs for (fun foo => goodFooCombo n foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooCombo n foo). *)

Existing Instance GenSizedSuchThatgoodFoo.

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFoo input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFoo input x).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFoo n foo). *)


Existing Instance GenSizedSuchThatgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooPrec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooPrec input x).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooPrec n foo). *)

Existing Instance GenSizedSuchThatgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooMatch n foo).

Derive SizedProofEqs for (fun foo => goodFooMatch n foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooMatch n foo). *)

Existing Instance GenSizedSuchThatgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooRec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooRec input x).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooRec n foo). *)

Inductive goodFooB : nat -> Foo -> Prop := 
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooB input x).

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooB n foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooB n foo). *)

Inductive LRTree : tree -> Prop :=
| PLeaf : LRTree Leaf
| PNode :
    forall m t1 t2,
      ~ t1 = Node 2 Leaf Leaf ->
      ~ Node 4 Leaf Leaf = t1 ->
      LRTree t1 ->
      LRTree t2 ->
      LRTree (Node m t1 t2).



Derive ArbitrarySizedSuchThat for (fun (x : tree) => LRTree x).

(* XXX sucThatMaybe case *)

Instance DecidableLRTree t : Dec (LRTree t).
Proof.
Admitted.

(* Instance DecEqLRTree (t1 t2 : tree): Dec (t1 = t2). *)
(* Proof. *)
(* Admitted. *)


Derive SizedProofEqs for (fun (x : tree) => LRTree x).

(* XXX bug *)
Derive SizeMonotonicSuchThatOpt for (fun foo => LRTree foo).

(* Derive GenSizedSuchThatCorrect for (fun foo => LRTree foo). *)

(* Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo). *)
(* XXX
   bug for 
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n, goodTree n t1 ->
                      ~ t1 =  t2 ->υ
                      (* goodTree m t1 -> *)
                      goodTree (S n) (Node k t1 t2).
*)


Inductive HeightTree : nat -> tree -> Prop :=
| HLeaf : forall n, HeightTree n Leaf
| HNode :
    forall t1 t2 n m,
      HeightTree n t1 ->
      HeightTree n t2 ->
      HeightTree (S n) (Node m t1 t2).


Instance ArbitrarySuchThatEql {A} (x : A) : GenSuchThat A (fun y => eq x y) :=
  {| arbitraryST := returnGen (Some x) |}.



(* XXX breaks gen *)

(* Inductive ex_test : tree -> Prop := *)
(* | B : ex_test Leaf  *)
(* | Ind : *)
(*     forall (list  y12  : nat) t, *)
(*       list = y12 -> *)
(*       ex_test (Node 4 t t). *)

(* Derive ArbitrarySizedSuchThat for (fun (x : tree) => ex_test x). *)

(* Set Printing All.  *)

(* Inductive LRTree : tree -> Prop := *)
(* | PLeaf : LRTree Leaf *)
(* | PNode : *)
(*     forall m t1 t2, *)
(*       Node 2 Leaf Leaf = t1 -> *)
(*       t1 = Node 2 Leaf Leaf -> *)
(*       LRTree t1 -> *)
(*       LRTree t2 -> *)
(*       LRTree (Node m t1 t2). *)

(* Inductive test : nat -> Foo -> Prop := *)
(* | T : forall (x : False), test 1 Foo1. *)

(* Derive ArbitrarySizedSuchThat for (fun foo => test n foo). *)

(* Inductive test1 : bool -> Foo -> Prop := *)
(* | T1 : forall (x1 x2 x3 : bool), x1 = x3 -> test1 x2 Foo1. *)

(* Derive ArbitrarySizedSuchThat for (fun foo => test1 n foo). *)

(* Inductive test2 : nat -> Foo -> Prop := *)
(* | T2 : forall (x1 x2 : bool), x1 = x2 ->  test2 1 Foo1. *)
 
(* Derive ArbitrarySizedSuchThat for (fun foo => test2 n foo). *)

(* XXX weird bug when naming binders with name of already existing ids,
   e.g. nat, list*)

(* Inductive HeightTree : nat -> tree -> Prop := *)
(* | HLeaf : forall n, HeightTree n Leaf *)
(* | HNode : *)
(*     forall t1 t2 n k m, *)
(*       k = 3 -> *)
(*       HeightTree k t2 -> *)
(*       HeightTree k t1 -> *)
(*       HeightTree n (Node m t1 t2). *)

(* Inductive goodTree : nat -> tree -> Prop := *)
(* | GL : goodTree 0 Leaf *)
(* | GN : forall k t1 t2 n m, goodTree n t1 -> *)
(*                       goodTree m t2 -> *)
(*                       goodTree (n + m + 1) (Node k t1 t2). *)

(* Lemma test2 {A} (gs1 gs2 : nat -> list (nat * G (option A))) s s1 s2 :  *)
(*       \bigcup_(g in gs1 s1) (semGenSize (snd g) s) \subset  \bigcup_(g in gs2 s2) (semGenSize (snd g) s) -> *)
(*       semGenSize (backtrack (gs1 s1)) s \subset semGenSize (backtrack (gs2 s2)) s. *)
(* Admitted. *)

(* Goal (forall inp : nat, SizedMonotonic (@arbitrarySizeST Foo (fun (x : Foo) => goodFooRec inp x) _)). *)
(* Proof. *)
(*   intros inp. *)
(*   constructor. *)
(*   intros s s1 s2. *)
(*   revert inp. *)
(*   induction s1; induction s2; intros. *)
(*   - simpl. eapply subset_refl. *)
(*   - simpl. *)
(*     refine (test *)
(*               (fun s => [(1, returnGen (Some Foo1))]) *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               s 0 s2 _). *)
(*     admit. *)
(*   - ssromega. *)
(*   - simpl. *)
(*     refine (test *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               s s1 s2 _). *)
(*     admit. *)
