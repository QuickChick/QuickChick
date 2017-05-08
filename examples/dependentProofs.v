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

Require Import DependentTest zoo.

Existing Instance genSFoo.
Existing Instance shrFoo.
(* XXX these instances should be present *)
Derive SizeMonotonic for Foo using genSFoo.
Derive SizedMonotonic for Foo using genSFoo.

Typeclasses eauto := debug.

(* Interesting. Do we need Global instance?? *) 
Existing Instance arbSizedSTgoodFooNarrow.  (* Why???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooNarrow n foo).

Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

Lemma test (n : nat) :
  \bigcup_(s : nat) (@DependentClasses.iter _ _ (SizedProofEqsgoodFooNarrow n) s) <--> (fun foo => goodFooNarrow n foo).
Proof.
  refine
    (fun foo =>
       conj
         (fun H =>
            match H with
              | ex_intro s (conj Hs Hi) => _
            end
         )
         _).
  - refine
      (nat_ind
          (fun s : nat =>
             forall n : nat,
               (DependentClasses.iter s foo -> goodFooNarrow n foo))
          (fun n Hs =>
             match Hs with
               | or_introl H1 =>
                 match H1 with
                   | erefl => GoodNarrowBase n
                 end
               | or_intror H2 =>
                 False_ind _ H2
             end)
          (fun s IHs n Hs =>
             match Hs with
               | or_introl H1 =>
                 match H1 with
                   | erefl => GoodNarrowBase n
                 end
               | or_intror H2 =>
                 match H2 with
                   | or_introl H1 =>
                     match H1 with
                       | ex_intro x (conj s2 Hs2) =>
                         (match
                             @dec (goodFooNarrow (S O) x) (goodFooNarrow_dec (S O) x) as s3
                             return
                             ((match s3 with | left _ => [set x] | right _ => set0 end) foo ->
                              goodFooNarrow n foo)
                           with
                             | left H3 =>
                               fun hin =>
                                 (GoodNarrow n foo
                                             (IHs 0 (match hin with
                                                       | erefl => s2
                                                     end))
                                             (match hin with
                                                | erefl => H3
                                              end))
                             | right H4 => fun Hin => False_ind _ Hin
                           end) Hs2    
                     end
                   | or_intror H2 => False_ind _ H2
                 end
             end)
          s n Hi
      ).
  - refine
      (goodFooNarrow_ind
         (fun n foo => (\bigcup_(s : nat) (@DependentClasses.iter _ _ (SizedProofEqsgoodFooNarrow n) s)) foo)
         (fun n => ex_intro _ 0 (conj I (or_introl erefl)))
         (fun n foo Hf IHf Hf' IHf' =>
            match IHf with
              | ex_intro x (conj Hn Hs) =>
                ex_intro
                  _ (S x)
                  (conj
                     I
                     (or_intror
                        (or_introl
                           (ex_intro
                              _ foo (conj
                                       Hs
                                       (match
                                           @dec (goodFooNarrow (S O) foo) (goodFooNarrow_dec (S O) foo)
                                           as s3
                                           return match s3 with | left _ => [set foo] | right _ => set0 end foo
                                         with
                                           | left H3 => erefl
                                           | right H4 => False_ind _ (H4 Hf')
                                         end)
                           )))))
            end)         
         n foo).    
Qed.

Existing Instance arbSizedSTgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

Existing Instance arbSizedSTgoodFoo.

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFoo input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFoo input x).

Existing Instance arbSizedSTgoodFooCombo.

Derive SizeMonotonicSuchThat for (fun foo => goodFooCombo n foo).

Derive SizedProofEqs for (fun foo => goodFooCombo n foo).

Existing Instance arbSizedSTgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooMatch n foo).

Derive SizedProofEqs for (fun foo => goodFooMatch n foo).

Existing Instance arbSizedSTgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooRec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooRec input x).

Existing Instance arbSizedSTgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooPrec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooPrec input x).

Inductive goodFooB : nat -> Foo -> Prop := 
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).
Derive SizedProofEqs for (fun (x : Foo) => goodFooB input x).


Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Inductive HeightTree : nat -> tree -> Prop :=
| HLeaf : forall n, HeightTree n Leaf
| HNode :
    forall t1 t2 n m,
      HeightTree n t1 ->
      HeightTree n t2 ->
      HeightTree (S n) (Node m t1 t2).

(* ΧΧΧ this breaks gens *)
Inductive LRTree : tree -> Prop :=
| PLeaf : LRTree Leaf
| PNode :
    forall m t1 t2,
      t1 = t2 ->
      LRTree t1 ->
      LRTree t2 ->
      LRTree (Node m t1 t2).

Derive ArbitrarySizedSuchThat for (fun (x : tree) => HeightTree input x).
Derive SizedProofEqs for (fun (x : tree) => HeightTree input x).


(* XXX breaks gen *)
(* Inductive HeightTree : nat -> tree -> Prop := *)
(* | HLeaf : forall n, HeightTree n Leaf *)
(* | HNode : *)
(*     forall t1 t2 n k m, *)
(*       k = 3 -> *)
(*       HeightTree k t2 -> *)
(*       HeightTree k t1 -> *)
(*       HeightTree n (Node m t1 t2). *)

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
