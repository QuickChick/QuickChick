From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.
Require Import List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Set Bullet Behavior "Strict Subproofs".

Instance backtrackSizeMonotonic :
  forall {A : Type} (lg : seq (nat * G (option A))),
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (backtrack lg).
Admitted.

Instance matchSizeMonotonic 
         {A : Type} (g1 g2 : G A) (P : Prop) {H : Dec P}
         {H1 : SizeMonotonic g1} {H2 : SizeMonotonic g2} :
  SizeMonotonic 
    (match @dec P H
     with
       | left eq => g1
       | right neq => g2
     end).
Proof.
  destruct (P ?); eauto.
  Show Proof.

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

Existing Instance arbSizedSTgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooUnif input x).

Existing Instance arbSizedSTgoodFoo.

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFoo input x).

Existing Instance arbSizedSTgoodFooCombo.

Derive SizeMonotonicSuchThat for (fun foo => goodFooCombo n foo).

Existing Instance arbSizedSTgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun foo => goodFooMatch n foo).

Existing Instance arbSizedSTgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooRec input x).

Existing Instance arbSizedSTgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooPrec input x).

Inductive goodFooB : nat -> Foo -> Prop := 
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).


Lemma test {A} (gs1 gs2 : nat -> list (nat * G (option A))) s s1 s2 : 
      \bigcup_(g in gs1 s1) (semGenSize (snd g) s) \subset  \bigcup_(g in gs2 s2) (semGenSize (snd g) s) ->
      semGenSize (backtrack (gs1 s1)) s \subset semGenSize (backtrack (gs2 s2)) s.
Admitted.

Goal (forall inp : nat, SizedMonotonic (@arbitrarySizeST Foo (fun (x : Foo) => goodFooRec inp x) _)).
Proof.
  intros inp.
  constructor.
  intros s s1 s2.
  revert inp.
  induction s1; induction s2; intros.
  - simpl. eapply subset_refl.
  - simpl.
    refine (test
              (fun s => [(1, returnGen (Some Foo1))])
              (fun s => [(1, returnGen (Some Foo1));
                       (1,
                        doM! foo <-
                           (fix aux_arb (size0 input0_ : nat) {struct size0} : 
                              G (option Foo) :=
                              match size0 with
                                | 0 => backtrack [(1, returnGen (Some Foo1))]
                                | size'.+1 =>
                                  backtrack
                                    [(1, returnGen (Some Foo1));
                                      (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))]
                              end) s 0; returnGen (Some (Foo2 foo)))])
              s 0 s2 _).
    admit.
  - ssromega.
  - simpl.
    refine (test
              (fun s => [(1, returnGen (Some Foo1));
                       (1,
                        doM! foo <-
                           (fix aux_arb (size0 input0_ : nat) {struct size0} : 
                              G (option Foo) :=
                              match size0 with
                                | 0 => backtrack [(1, returnGen (Some Foo1))]
                                | size'.+1 =>
                                  backtrack
                                    [(1, returnGen (Some Foo1));
                                      (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))]
                              end) s 0; returnGen (Some (Foo2 foo)))])
              (fun s => [(1, returnGen (Some Foo1));
                       (1,
                        doM! foo <-
                           (fix aux_arb (size0 input0_ : nat) {struct size0} : 
                              G (option Foo) :=
                              match size0 with
                                | 0 => backtrack [(1, returnGen (Some Foo1))]
                                | size'.+1 =>
                                  backtrack
                                    [(1, returnGen (Some Foo1));
                                      (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))]
                              end) s 0; returnGen (Some (Foo2 foo)))])
              s s1 s2 _).
    admit.
