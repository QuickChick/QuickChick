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

Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

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



(* Derive SizedProofEqs for (fun (x : tree) => LRTree x). *)


Instance DecidableLRTree t : Dec (LRTree t).
Proof.
Admitted.

Instance DecEqLRTree (t1 t2 : tree): Dec (t1 = t2).
Proof.
Admitted.

Let iter1 : nat ->  set tree :=
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

Lemma pmon :
  forall s1 s2, s1 <= s2 -> iter1 s1 \subset iter1 s2.
Admitted.

Lemma lala :
  (fun z => LRTree z) \subset (\bigcup_(n : nat) (iter1 n)).
Proof.
  refine (fun x =>
            LRTree_ind
              (fun _gen =>
                 bigcup setT
                        (fun n =>
                           iter1 n) _gen)
              (ex_intro _ (S 0) (conj I (or_introl (Logic.eq_refl _))))
              (fun m t1 t2 H0 H1 H2 IH2 H3 IH3 =>
                 match IH2 with
                   | ex_intro y2 Pc2 =>
                     match Pc2 with
                       | conj HT P2 =>
                         match IH3 with
                           | ex_intro y3 Pc3 =>
                             match Pc3 with
                               | conj HT P3 =>
                                 ex_intro _ (S (Nat.add (Nat.add 0 y2) y3))
                                          (conj I
                                                (or_intror
                                                   (or_introl
                                                      (ex_intro _ _
                                                                (conj _
                                                                   (* match *)
                                                                   (*   @dec *)
                                                                   (*     (@eq (tree) *)
                                                                   (*          (Node  *)
                                                                   (*             (S (S (S (S (O)))))  *)
                                                                   (*             (Leaf)  *)
                                                                   (*             (Leaf)) t1) _ as s *)
                                                                   (*   return *)
                                                                   (*   match s with *)
                                                                   (*     | left eq0 => False *)
                                                                   (*     | right neq => *)
                                                                   (*       match *)
                                                                   (*         @dec *)
                                                                   (*           (@eq  *)
                                                                   (*              (tree) t1 *)
                                                                   (*              (Node  *)
                                                                   (*                 (S (S (O)))  *)
                                                                   (*                 (Leaf)  *)
                                                                   (*                 (Leaf))) _ *)
                                                                   (*       with *)
                                                                   (*         | left eq0 => False *)
                                                                   (*         | right neq => *)
                                                                   (*           (iter1 *)
                                                                   (*              (Nat.add (Nat.add 0 y2) y3)) *)
                                                                   (*             t1 *)
                                                                   (*       end *)
                                                                   (*   end *)
                                                                   (* with *)
                                                                   (*   | left Heq1 => False_ind _ (H1 Heq1) *)
                                                                   (*   | right Hneq1 => *)
                                                                   (*     match *)
                                                                   (*       @dec *)
                                                                   (*         (@eq  *)
                                                                   (*            (tree) t1 *)
                                                                   (*            (Node  *)
                                                                   (*               (S (S (O)))  *)
                                                                   (*               (Leaf)  *)
                                                                   (*               (Leaf))) _ as s *)
                                                                   (*       return *)
                                                                   (*       match s with *)
                                                                   (*         | left eq0 => False *)
                                                                   (*         | right neq => *)
                                                                   (*           (iter1 (Nat.add (Nat.add 0 y2) y3)) *)
                                                                   (*             t1 *)
                                                                   (*       end *)
                                                                   (*     with *)
                                                                   (*       | left Heq0 => False_ind _ (H0 Heq0) *)
                                                                   (*       | right Hneq0 => *)
                                                                   (*         pmon _ *)
                                                                   (*              (Nat.add (Nat.add 0 y2) y3) *)
                                                                   (*              (plus_leq_compat_l _ _ _ *)
                                                                   (*                                 (leq_addl _ _)) _ P2 *)
                                                                   (*     end *)
                                                                   (* end *)
                                                                   (ex_intro _ _
                                                                             (conj
                                                                                (pmon _
                                                                                      (Nat.add (Nat.add 0 y2) y3)
                                                                                      (leq_addl _ _) _ P3)
                                                                                (ex_intro _ _
                                                                                          (conj I (Logic.eq_refl _))))))))))
                             end
                         end
                     end
                 end) x).
  destruct (@dec
               (@eq (tree)
                    (Node
                       (S (S (S (S (O)))))
                       (Leaf)
                       (Leaf)) t1) _).
  refine (False_ind _ (H1 e)).

  destruct (@dec
              (@eq
                 (tree) t1
                 (Node
                    (S (S (O)))
                    (Leaf)
                    (Leaf))) _).

  refine( False_ind _ (H0 e)).
  refine (pmon _
               (Nat.add (Nat.add 0 y2) y3)
               _ _ P2).
  Show Proof.
  (plus_leq_compat_l _ _ _ (leq_addl _ _))



  refine (match
             @dec
               (@eq (tree)
                    (Node
                       (S (S (S (S (O)))))
                       (Leaf)
                       (Leaf)) t1) _ as s
             return
             match s with
               | left eq0 => False
               | right neq => _
                 (* match *)
                 (*   @dec *)
                 (*     (@eq *)
                 (*        (tree) t1 *)
                 (*        (Node *)
                 (*           (S (S (O))) *)
                 (*           (Leaf) *)
                 (*           (Leaf))) _ *)
                 (* with *)
                 (*   | left eq0 => False *)
                 (*   | right neq =>  *)
                 (*     (iter1 *)
                 (*        (Nat.add (Nat.add 0 y2) y3)) *)
                 (*       t1 *)
                 (* end *)
             end
           with
             | left Heq1 => False_ind _ (H1 Heq1)
             | right Hneq1 => _
                               match
                                 @dec
                                   (@eq
                                      (tree) t1
                                      (Node
                                         (S (S (O)))
                                         (Leaf)
                                         (Leaf))) _ as s
                                 return
             (*   match s with *)
             (*     | left eq0 => False *)
             (*     | right neq => *)
             (*       (iter1 (Nat.add (Nat.add 0 y2) y3)) *)
             (*         t1 *)
             (*   end *)
             (* with *)
             (*   | left Heq0 => _ (* False_ind _ (H0 Heq0) *) *)
             (*   | right Hneq0 => _ *)
             (*     (* pmon _ *) *)
             (*     (*      (Nat.add (Nat.add 0 y2) y3) *) *)
             (*     (*      (plus_leq_compat_l _ _ _ *) *)
             (*     (*                         (leq_addl _ _)) _ P2 *) *)
             (* end *)
         end).



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


(* Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo). *)
(* XXX
   bug for 
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n, goodTree n t1 ->
                      ~ t1 =  t2 ->
                      (* goodTree m t1 -> *)
                      goodTree (S n) (Node k t1 t2).
*)

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
