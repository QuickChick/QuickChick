From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.
Require Import List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Set Bullet Behavior "Strict Subproofs".

Lemma cons_subset {A : Type} (x : A) (l : seq A) (P : set A) :
  P x ->
  l \subset P ->
  (x :: l) \subset P.
Proof.
  intros Px Pl x' Hin. inv Hin; firstorder.
Qed.

Lemma nil_subset {A : Type} (P : set A) :
  [] \subset P.
Proof.
  intros x H; inv H.
Qed.

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

Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo).

Lemma imset_union_incl {U T : Type} (s1 s2 : set U) (f : U -> T) :
  f @: (s1 :|: s2) \subset (f @: s1) :|: (f @: s2).
Proof.
  firstorder.
Qed.

Lemma imset_singl_incl {U T : Type} (x : U) (f : U -> T) :
  f @: [set x] \subset [set (f x)].
Proof.
  intros y Hin. destruct Hin as [y' [Hin1 Hin2]].
  inv Hin1. inv Hin2. reflexivity.
Qed.

Lemma imset_set0_incl  {U T : Type} (f : U -> T) :
  f @: set0 \subset set0.
Proof.
  firstorder.
Qed.

Lemma semBacktrack:
  forall (A : Type) (l : seq (nat * G (option A))),
    semGen (backtrack l) <-->
    (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGen x.2))) :|:
    ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGen x.2))).
Admitted.

Lemma set_eq_set_incl_r {U : Type} (s1 s2 : set U) :
  s1 <--> s2 -> s2 \subset s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_set_incl_l {U : Type} (s1 s2 : set U) :
  s1 <--> s2 -> s1 \subset s2.
Proof.
  firstorder.
Qed.

Lemma rewrite_set_l {U : Type} (s1 s2 : set U) x :
  s1 x ->
  s1 <--> s2 ->
  s2 x.
Proof.
  firstorder.
Qed.

Lemma rewrite_set_r {U : Type} (s1 s2 : set U) x :
  s2 x ->
  s1 <--> s2 ->
  s1 x.
Proof.
  firstorder.
Qed.

Lemma succ_neq_zero :
  forall x, S x <> 0.
Proof.
  firstorder.
Qed.

Lemma imset_bigcup_incl_l :
  forall {T U V : Type} (f : U -> V) (A : set T) (F : T -> set U),
  f @: (\bigcup_(x in A) F x) \subset \bigcup_(x in A) f @: F x.
Proof.
  firstorder.
Qed.

Lemma in_imset {U T} (f : U -> T) (S : set U) (x : T) :
  (f @: S) x -> exists y, x = f y.
Proof.
  move => [y [H1 H2]]; eauto.
Qed.

Lemma isSomeSome {A : Type} (y : A) :
  Some y.
Proof.
  exact isT.
Qed.

Lemma semBindOptSizeMonotonicIncl_l {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  Some @: s1 \subset semGen g ->
  \bigcup_(a in s1) semGen (f a) \subset semGen (bindGenOpt g f).
Admitted.

Lemma semBindSizeMonotonicIncl_l {A B} (g : G A) (f : A -> G B) (s1 : set A)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  s1 \subset semGen g ->
  \bigcup_(a in s1) semGen (f a) \subset semGen (bindGen g f).
Admitted.

Lemma semBindOptSizeMonotonicIncl_r {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  semGen g \subset (Some @: s1) :|: [set None] ->
  (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
  semGen (bindGenOpt g f) \subset Some @: (\bigcup_(a in s1) s2 a) :|: [set None].
Admitted.

Lemma semBindSizeMonotonicIncl_r {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  semGen g \subset s1 ->
  (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
  semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].
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

Lemma lift_union_compat {A} (s1 s2 : set (option A)) (s3 s4 : set A) :
  s1 \subset lift s3 ->
  s2 \subset lift s4 ->
  (s1 :|: s2) \subset lift (s3 :|: s4).
Proof.
  firstorder.
Qed.

Lemma lift_subset_compat {A} (s1 s2 : set (option A)) (s3 s4 : set A) :
  s1 \subset lift s3 ->
  s2 \subset lift s4 ->
  (s1 :|: s2) \subset lift (s3 :|: s4).
Proof.
  firstorder.
Qed.

Lemma lift_subset_pres_l {A} (s1 : set (option A)) (s2 s3 : set A) :
  s1 \subset lift s2 ->
  s1 \subset lift (s2 :|: s3).
Proof.
  firstorder.
Qed.

Lemma lift_subset_pres_r {A} (s1 : set (option A)) (s2 s3 : set A) :
  s1 \subset lift s3 ->
  s1 \subset lift (s2 :|: s3).
Proof.
  firstorder.
Qed.


Lemma set_incl_setI_l {A} (s1 s2 s3 : set A) :
  s1 \subset s3 ->
  (s1 :&: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma set_incl_setI_r {A} (s1 s2 s3 : set A) :
  s2 \subset s3 ->
  (s1 :&: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma set_incl_setU_l {A} (s1 s2 s3 : set A) :
  s1 \subset s3 ->
  s2 \subset s3 ->
  (s1 :|: s2) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set_I_l {A B} (s1 s2 : set A) (s3 : set B) (f : A -> set B) :
  \bigcup_(x in s1) (f x) \subset s3 ->
  \bigcup_(x in (s1 :&: s2)) (f x) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set_U {A B} (s1 s2 : set A) (s3 : set B) (f : A -> set B) :
  \bigcup_(x in s1) (f x) \subset s3 ->
  \bigcup_(x in s2) (f x) \subset s3 ->
  \bigcup_(x in (s1 :|: s2)) (f x) \subset s3.
Proof.
  firstorder.
Qed.

Lemma bigcup_set0_subset {A B} (s : set B) (f : A -> set B) :
  \bigcup_(x in set0) (f x) \subset s.
Proof.
  firstorder.
Qed.

(* QuickChickDebug Debug On. *)

Fixpoint aux_iter (size0 input0_0 : nat) {struct size0} : set tree :=
  match size0 with
    | 0 =>
      match input0_0 with
        | 0 => [set Leaf]
        | _.+1 => set0
      end :|: set0
    | size'.+1 =>
      match input0_0 with
        | 0 => [set Leaf]
        | _.+1 => set0
      end
        :|: (match input0_0 with
               | 0 => set0
               | n.+1 =>
                 \bigcup_(t1 in aux_iter size' n)
                  \bigcup_(m in [set: nat])
                  \bigcup_(t2 in aux_iter size' m)
                  (match
                      @dec (goodTree m t1) (DecgoodTree m t1)
                      return (forall _ : tree, Prop)
                    with
                      | left _ =>
                        \bigcup_(k in [set: nat])
                         [set 
                            Node k t1 t2]
                      | right _ =>  set0
                    end)
             end :|: set0)
  end.

Fixpoint arb_aux (size0 input0_0 : nat) {struct size0} : G (option tree) :=
  match size0 with
    | 0 =>
      backtrack
        [(1,
          match input0_0 with
            | 0 => returnGen (Some Leaf)
            | _.+1 => returnGen None
          end)]
    | size'.+1 =>
      backtrack
        [(1,
          match input0_0 with
            | 0 => returnGen (Some Leaf)
            | _.+1 => returnGen None
          end);
          (1,
           match input0_0 with
             | 0 => returnGen None
             | n.+1 =>
               doM! t1 <- arb_aux size' n;
             do! m <- arbitrary;
             doM! t2 <- arb_aux size' m;
             match
               @dec (goodTree m t1) (DecgoodTree m t1)
               return (G (option tree))
             with
               | left _ =>  do! k <- arbitrary;
               returnGen (Some (Node k t1 t2))
               | right _ => returnGen None
             end
           end)]
  end.


Lemma bigcup_cons_subset {A B} l (ls : seq A) (f : A -> set B) s :
  f l \subset s ->
  \bigcup_(x in ls) (f x) \subset s ->
  \bigcup_(x in l :: ls) (f x) \subset s. 
Proof.
  intros H1 H2 x [y [Hl Hr]].
  inv Hl.
  - eauto.
  - eapply H2. eexists; split; eauto.
Qed.

Lemma bigcup_nil_subset {A B} (f : A -> set B) s :
  \bigcup_(x in []) (f x) \subset s. 
Proof.
  intros x [y [H1 H2]]. inv H1.
Qed.

Derive GenSizedSuchThatCorrect for (fun foo => goodTree n foo).

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

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooUnif n foo).

(* Interesting. Do we need  Global instance?? *) 
Existing Instance GenSizedSuchThatgoodFooNarrow.  (* Why???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooNarrow n foo).

Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooNarrow n foo).

Existing Instance GenSizedSuchThatgoodFooCombo.

Derive SizeMonotonicSuchThat for (fun foo => goodFooCombo n foo).

Derive SizedProofEqs for (fun foo => goodFooCombo n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooCombo n foo).

Existing Instance GenSizedSuchThatgoodFoo.

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFoo input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFoo input x).

Derive GenSizedSuchThatCorrect for (fun foo => goodFoo n foo).


Existing Instance GenSizedSuchThatgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooPrec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooPrec input x).

(* Derive GenSizedSuchThatCorrect for (fun foo => goodFooPrec n foo). *)

Existing Instance GenSizedSuchThatgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooMatch n foo).

Derive SizedProofEqs for (fun foo => goodFooMatch n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooMatch n foo).

Existing Instance GenSizedSuchThatgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooRec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooRec input x).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooRec n foo).

Inductive goodFooB : nat -> Foo -> Prop := 
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooB input x).

Derive SizeMonotonicSuchThat for (fun foo => goodFooB n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooB n foo).

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
Derive SizeMonotonicSuchThat for (fun foo => LRTree foo).
QuickChickDebug Debug On.

Derive GenSizedSuchThatCorrect for (fun foo => LRTree foo).

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
