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

Lemma eq_symm {A : Type} (x y : A) :
  x = y -> y = x.
Proof.
  firstorder.
Qed.


Derive SizeMonotonicSuchThat for (fun foo => goodFooNarrow n foo).
Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

(* Example with two IH *)
Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Inductive goodTree : nat -> tree -> Prop :=
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n m, goodTree n t1 ->
                      goodTree m t2 ->
                      goodTree (S n) (Node k t1 t2).

Derive ArbitrarySizedSuchThat for (fun foo => goodTree n foo).

Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo).

Derive SizedProofEqs for (fun foo => goodTree n foo).

(* Lemma iter_mon (input0_ : nat) : *)
(*   forall n1 n2, n1 <= n2 ->  *)
(*            (@DependentClasses.iter tree _ (SizedProofEqsgoodTree input0_)) n1 \subset (@DependentClasses.iter tree _ (SizedProofEqsgoodTree input0_)) n2. *)

(* Lemma lala (input0_ : nat) : *)
(*   (fun foo => goodTree input0_ foo) \subset *)
(*   (\bigcup_(n in [set: nat]) (@DependentClasses.iter tree _ (SizedProofEqsgoodTree input0_)) n). *)
(* Proof. *)
(*   revert input0_. *)
(*   unfold set_incl.  *)
(*   refine (goodTree_ind (fun input0_ a => (\bigcup_(n in [set: nat]) DependentClasses.iter n) a) *)
(*                        (ex_intro _ 0 (conj I (or_introl _))) *)
(*                        (fun k t1 t2 n m H1 IH1 H2 IH2 => _)). *)
(*   exact erefl. *)

(*   refine (match IH1 with *)
(*             | ex_intro n (conj _ IH1) => *)
(*               match IH2 with *)
(*                 | ex_intro m (conj _ IH2) => _ *)
(*               end *)
(*           end). *)
(*   exists (S (n + m)).  *)
(*   split. now constructor. *)
(*   right. left. *)
(*   simpl in *.  *)
(*   eexists. split.  admit. (* needs monotonicity *) *)
(*   eexists. split.  now constructor. *)
(*   eexists. split.  admit. (* needs monotonicity *) *)
(*   eexists. *)
  
(*   eauto. now constructor. *)
 
(*   eauto. *)
(*   simpl. *)

(*   left. reflexivity. *)
(*   Show Proof. *)


(* Lemma lala (input0_ : nat) : *)
(*   (fun foo => goodFooNarrow input0_ foo) \subset (\bigcup_(n in [set: nat]) (@DependentClasses.iter Foo _ (SizedProofEqsgoodFooNarrow input0_)) n). *)
(* Proof. *)
(*   revert input0_. *)
(*   refine (goodFooNarrow_ind _ (fun input0_ => ex_intro _ 0 (conj I (or_introl erefl)))  (fun input0_ x H1 IH1 H2 IH2 => _)). *)
(*   refine *)
(*     (match IH1 with *)
(*        | ex_intro m (conj HT IH1) => *)
(*          ex_intro *)
(*            _ (S m) *)
(*            (conj *)
(*               HT *)
(*               (or_intror *)
(*                  (or_introl *)
(*                     (ex_intro _ x (conj *)
(*                                      IH1 *)
(*                                      (match *)
(*                                          @dec (goodFooNarrow (S O) x) (goodFooNarrow_dec (S O) x) *)
(*                                          as s *)
(*                                          return (match s with *)
(*                                                    | left _ => @set1 Foo x *)
(*                                                    | right _ => @set0 Foo *)
(*                                                  end x *)
(*                                                 ) *)
(*                                        with *)
(*                                          | left eq => erefl *)
(*                                          | right neq => False_ind _ (neq H2) *)
(*                                        end)))))) *)
(*      end). *)
  

Existing Instance arbSizedSTgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

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
      ~ t1 = Node 2 Leaf Leaf ->
      ~ Node 4 Leaf Leaf = t1 ->
      LRTree t1 ->
      LRTree t2 ->
      LRTree (Node m t1 t2).

Instance ArbitrarySuchThatEql {A} (x : A) : GenSuchThat A (fun y => eq x y) :=
  {| arbitraryST := returnGen (Some x) |}.

Instance DecidableLRTree t : Dec (LRTree t).
Proof.
Admitted.

Instance DecEqLRTree (t1 t2 : tree): Dec (t1 = t2).
Proof.
Admitted.

Derive ArbitrarySizedSuchThat for (fun (x : tree) => LRTree x).
Derive SizedProofEqs for (fun (x : tree) => LRTree x).


Definition iter :=
  (let
   fix aux_iter size0 :=
     match size0 with
     | O => setU (set1 (@Leaf)) set0
     | S size' =>
         setU (set1 (@Leaf))
           (setU
              (bigcup
                 (fun t1 =>
                  match
                    @dec
                      (@eq (tree) (Node (S (S (S (S (O))))) (Leaf) (Leaf)) t1)
                      _
                  with
                  | left eq0 => False
                  | right neq =>
                      match
                        @dec (@eq (tree) t1 (Node (S (S (O))) (Leaf) (Leaf)))
                          _
                      with
                      | left eq0 => False
                      | right neq => aux_iter size' t1
                      end
                  end)
                 (fun t1 =>
                  bigcup (aux_iter size')
                    (fun t2 => bigcup setT (fun m => set1 (@Node m t1 t2)))))
              set0)
     end in
 fun size0 => aux_iter size0).

Lemma lala :
  forall n1 n2, n1 <= n2 -> iter n1 \subset iter n2.
Proof.
  refine (fun n1 n2 =>
 nat_ind
   (fun n1 =>
    forall n2,
    Basics.impl (leq n1 n2)
      (set_incl
         (iter n1)
         (iter n2)))
   (fun n2 =>
    nat_ind
      (fun n2 =>
       Basics.impl (leq 0 n2)
         (set_incl
            (iter 0)
            (iter n2)))
      (fun Hleq => @subset_refl _ _)
      (fun n2 IHn2 Hleq =>
       setU_set_subset_compat (@subset_refl _ _)
         (setU_subset_r _ (@subset_refl _ _))) n2)
   (fun n1 IHn1 n2 =>
    nat_ind
      (fun n2 =>
       Basics.impl (leq (S n1) n2)
         (set_incl
            (iter (S n1))
            (iter n2)))
      (fun Hleq => False_ind _ (lt0_False Hleq))
      (fun n2 IHn2 Hleq =>
       setU_set_subset_compat (@subset_refl _ _)
         (setU_set_subset_compat
            (incl_bigcup_compat
               ( _
                (*  fun t1 => *)
                (* match *)
                (*   @dec *)
                (*     (@eq (tree) (Node (S (S (S (S (O))))) (Leaf) (Leaf)) t1) *)
                (*     _ as s *)
                (*   return *)
                (*     (Basics.impl *)
                (*        match s with *)
                (*        | left eq0 => _ *)
                (*        | right neq => _ *)
                (*        end match s with *)
                (*            | left eq0 => _ *)
                (*            | right neq => _ *)
                (*            end) *)
                (* with *)
                (* | left heq => (@subset_refl _ _) t1 *)
                (* | right hneq => *)
                (*     match *)
                (*       @dec (@eq (tree) t1 (Node (S (S (O))) (Leaf) (Leaf))) _ *)
                (*       as s *)
                (*       return *)
                (*         (Basics.impl *)
                (*            match s with *)
                (*            | left eq0 => _ *)
                (*            | right neq => _ *)
                (*            end *)
                (*            match s with *)
                (*            | left eq0 => _ *)
                (*            | right neq => _ *)
                (*            end) *)
                (*     with *)
                (*     | left heq => (@subset_refl _ _) t1 *)
                (*     | right hneq => IHn1 n2 Hleq t1 *)
                (*     end *)
                (* end *)
               )
               (fun t1 =>
                incl_bigcup_compat (IHn1 n2 Hleq)
                  (fun t2 =>
                   incl_bigcup_compat (@subset_refl _ _)
                     (fun m => @subset_refl _ _)))) 
            (@subset_refl _ _))) n2) n1 n2).

  refine
    (
      fun t1 =>
        match
          @dec
            (@eq (tree) (Node (S (S (S (S (O))))) (Leaf) (Leaf)) t1)
            _ as s
          return
          (Basics.impl
             match s with
               | left eq0 => set0 t1
               | right neq => _
             end match s with
                   | left eq0 => set0 t1
                   | right neq => _
                 end)
        with
          | left heq => (@subset_refl _ _) t1 
          | right hneq => _
            (* match *)
            (*   @dec (@eq (tree) t1 (Node (S (S (O))) (Leaf) (Leaf))) _ *)
            (*   as s *)
            (*   return *)
            (*   (Basics.impl *)
            (*      match s with *)
            (*        | left eq0 => _ *)
            (*        | right neq => _ *)
            (*      end *)
            (*      match s with *)
            (*        | left eq0 => _ *)
            (*        | right neq => _ *)
            (*      end) *)
            (* with *)
            (*   | left heq => (@subset_refl _ _) t1 *)
            (*   | right hneq => IHn1 n2 Hleq t1 *)
            (* end *)
        end).


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

(* XXX weid bug when naming binders with name of already existing ids,
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
