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

Lemma semBindOptSizeMonotonicIncl {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  Some @: s1 \subset semGen g ->
  \bigcup_(a in s1) semGen (f a) \subset semGen (bindGenOpt g f).
Admitted.

Lemma semBindSizeMonotonicIncl {A B} (g : G A) (f : A -> G B) (s1 : set A)
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonic (f a)} :
  s1 \subset semGen g ->
  \bigcup_(a in s1) semGen (f a) \subset semGen (bindGen g f).
Admitted. 

Lemma completeGT (i : nat):
  forall n,
    Some @: (@DependentClasses.iter _ (fun x => goodTree i x) _ n) \subset
         (semGen (@arbitrarySizeST _ _ (arbSizedSTgoodTree i) n)).
Proof.
  refine
    (nat_ind
       (fun n =>
          forall i,
            Some @: (@DependentClasses.iter _ _ (SizedProofEqsgoodTree i)  n) \subset
            (semGen (@arbitrarySizeST _ _ (arbSizedSTgoodTree i) n)))
       (fun i x Hin =>
          (* semantics of backtrack *)
          rewrite_set_r
            _ _ _
            (* push imset inside the unions and destruct *)
            (match (imset_union_incl _ _ _ _ Hin) with
               | or_introl H1 => 
                 or_introl
                   (* exists gen *)
                   (ex_intro _ _
                             (conj
                                (conj
                                   (* the first one *)
                                   (or_introl erefl)
                                   (* 1 <> 0 *)
                                   (succ_neq_zero _))
                                (* branch specific *)
                                (* match input *)
                                (match i
                                      as i
                                       return (Some @: match i with
                                                         | 0 => [set Leaf]
                                                         | _.+1 => set0
                                                       end) x ->
                                              ((fun u : option tree => u)
                                                 :&: semGen
                                                 match i with
                                                   | 0 => returnGen (Some Leaf)
                                                   | _.+1 => returnGen None
                                                 end) x
                                 with
                                   | 0 => fun H2 =>
                                           match (imset_singl_incl _ _ _ H2) with
                                             | erefl => conj isT (rewrite_set_r _ _ _ erefl (semReturn _))
                                           end
                                   | S n => fun H2 => (False_ind _ (imset_set0_incl _ _ H2))
                                 end H1)
                             ))
               (* last case empty set *) 
               | or_intror H2 => (False_ind _ (imset_set0_incl _ _ H2))
             end)
            (semBacktrack _ [(1,
                              match i with
                                | 0 => returnGen (Some Leaf)
                                | _.+1 => returnGen None
                              end)])
       )
       (fun m IHn i x Hin =>
          rewrite_set_r
            _ _ _
            (* push imset inside the unions and destruct *)
            (match (imset_union_incl _ _ _ _ Hin) with
               (* base case *)
               | or_introl H1 => _
               (* inductive case *) 
               | or_intror H2 =>
                 match (imset_union_incl _ _ _ _ H2) with
                   | or_introl H3 => _
                   (* last case empty set *)
                   | or_intror H4 => (False_ind _ (imset_set0_incl _ _ H4))
                 end
             end)
            (semBacktrack _ _)
       )
       i).
  
  - refine (or_introl
              (* exists gen *)
              (ex_intro _ _
                        (conj
                           (conj
                              (* the first one *)
                              (or_introl erefl)
                              (* 1 <> 0 *)
                              (succ_neq_zero _))
                           (* branch specific *)
                           (* match input *)
                           (match i
                                  as i
                                  return (Some @: match i with
                                                    | 0 => [set Leaf]
                                                    | _.+1 => set0
                                                  end) x ->
                                         ((fun u : option tree => u)
                                            :&: semGen
                                            match i with
                                              | 0 => returnGen (Some Leaf)
                                              | _.+1 => returnGen None
                                            end) x
                            with
                              | 0 => fun H2 =>
                                      match (imset_singl_incl _ _ _ H2) with
                                        | erefl => _ (* conj isT (rewrite_set_r _ _ _ erefl (semReturn _)) *)
                                      end
                              | S n => fun H2 => (False_ind _ (imset_set0_incl _ _ H2))
                            end H1)
                        ))).
    refine (conj isT (rewrite_set_r _ _ _ erefl (semReturn _))).
  - (* pick the geneator that corresponds to the current branch *)
    refine
      (or_introl (ex_intro _ _ (conj (conj (or_intror (or_introl erefl)) (succ_neq_zero _)) _))).
    refine (conj
              (match in_imset  _ _ _ H3 with
                 | ex_intro y Heq => eq_ind_r (fun x => isSome x) (isSomeSome _) Heq
               end) _).
    refine
      (match i as i return
             (Some @: (match i with
                         | 0 => set0 
                         | _.+1 => _
                       end)) x -> _
       with
         | 0 => fun H3 => (False_ind _ (imset_set0_incl _ _ H3))
         | S i => fun H3 => _
       end H3).
    refine 
      (match imset_bigcup_incl_l _ _ _ _ H3 with
         | ex_intro t1 (conj Ht1 Hc1) => 
           @semBindOptSizeMonotonicIncl
             _ _
             _ _ _
             (SizeMonotonicgoodTree m i)
             _ (IHn i) _
             (ex_intro _ t1
                       (conj Ht1 (match imset_bigcup_incl_l _ _ _ _ Hc1 with
                                    | ex_intro n (conj Hn Hc2) =>
                                      _
                                  end)
                       ))
             
       end).
    admit.
    simpl in Hc2.
    refine
      ((rewrite_set_r
          _ _ _
          (ex_intro
             _ n
             (conj
                (rewrite_set_r _ _ _ I arbitraryCorrect)
                (match imset_bigcup_incl_l _ _ _ _ Hc2 with
                   | ex_intro t2 (conj Ht2 Hc3) =>
                     @semBindOptSizeMonotonicIncl
                       _ _
                       _ _ _
                       (SizeMonotonicgoodTree m n)
                       _ (IHn n) _ 
                      (ex_intro _ t2 (conj Ht2 _))
                end)
             ))
          (@semBindSizeMonotonic
             _ _
             _
             _
             _ _)
       )).
    admit.
    simpl in Hc3.
    refine
      (match (@dec (goodTree n t1) (DecgoodTree n t1)) as s
             return
             @imset tree (option tree) (@Some tree)
                    match
                      s
                    with
                      | left _ =>
                        @bigcup nat tree (@setT nat)
                                (fun k : nat => @set1 tree (Node k t1 t2))
                      | right _ => @set0 tree
                    end x ->
             semGen
               (match
                   s
                 with
                   | left _ =>
                     do! k <- arbitrary; returnGen (Some (Node k t1 t2))
                                      | right _ =>  returnGen None
                 end) x

       with
         | left _ =>
           fun Hc4 =>
             match imset_bigcup_incl_l _ _ _ _  Hc4 with
               | ex_intro k (conj Hk Hc5) =>
                 @semBindSizeMonotonicIncl
                   _ _ _ _ _ _ _
                   (set_eq_set_incl_r _ _ arbitraryCorrect) _
                   (ex_intro _ k (conj Hk (eq_ind _ _ (rewrite_set_r _ _ _ erefl (semReturn _)) _ (imset_singl_incl _ _ _ Hc5))))
             end
         | right _ => fun Hc3 => (False_ind _ (imset_set0_incl _ _ Hc3))
       end Hc3
      )
    .
    admit.

Existing Instance genSFoo.
Existing Instance shrFoo.
(* XXX these instances should be present *)
Derive SizeMonotonic for Foo using genSFoo.
Derive SizedMonotonic for Foo using genSFoo.

Typeclasses eauto := debug.

Existing Instance arbSizedSTgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

(* Interesting. Do we need  Global instance?? *) 
Existing Instance arbSizedSTgoodFooNarrow.  (* Why???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooNarrow n foo).

Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

Existing Instance arbSizedSTgoodFoo.

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFoo input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFoo input x).

Existing Instance arbSizedSTgoodFooCombo.

Derive SizeMonotonicSuchThat for (fun foo => goodFooCombo n foo).

Derive SizedProofEqs for (fun foo => goodFooCombo n foo).

Existing Instance arbSizedSTgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooPrec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooPrec input x).

Existing Instance arbSizedSTgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooMatch n foo).

Derive SizedProofEqs for (fun foo => goodFooMatch n foo).

Existing Instance arbSizedSTgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooRec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooRec input x).

Inductive goodFooB : nat -> Foo -> Prop := 
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooB input x).


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


Instance DecidableLRTree t : Dec (LRTree t).
Proof.
Admitted.

Instance DecEqLRTree (t1 t2 : tree): Dec (t1 = t2).
Proof.
Admitted.


Derive SizedProofEqs for (fun (x : tree) => LRTree x).


  Set Printing All. eassumption.
  simpl. eassumption.
  
  (* Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo). *)
(* XXX
   bug for 
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n, goodTree n t1 ->
                      ~ t1 =  t2 ->
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
