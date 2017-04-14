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


Derive Arbitrary for Foo.
Derive Show for Foo.

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

Lemma lala :
forall s input0_ : nat,
  SizeMonotonic
    (@arbitrarySizeST (Foo)
                      (fun _forGen => (@goodFooMatch) input0_ _forGen) _ s).
  refine
    (nat_ind
       (fun s =>
          forall input0_ : nat,
            SizeMonotonic
              (@arbitrarySizeST (Foo)
                                (fun _forGen => (@goodFooMatch) input0_ _forGen) _ s))
       _ _).
  refine (fun input0_ : nat =>
     backtrackSizeMonotonic
       (cons
          (pair 1
                match input0_ with
                  | @O => returnGen (@Some (Foo) (@Foo1))
                  | _ => returnGen (@None (Foo))
                end) nil) _).

  refine (cons_subset _ _ _ _ (nil_subset _)).
  simpl.
  refine (match input0_ with
            | @O => returnGenSizeMonotonic (Some (@Foo1))
            | _ => yreturnGenSizeMonotonic None
          end (nil_subset _)). ).
       (fun size0 IHs (input0_ : nat) =>
          backtrackSizeMonotonic
            (cons
               (pair 1
                     match input0_ with
                       | @O => returnGen (@Some (Foo) (@Foo1))
                       | _ => returnGen (@None (Foo))
                     end) nil)
            (cons_subset _ _ _
                         match input0_ with
                           | @O => returnGenSizeMonotonic (Some (@Foo1))
                           | _ => returnGenSizeMonotonic None
                         end (nil_subset _)))).

Derive SizeMonotonicSuchThat for (fun foo => goodFooMatch n foo).

Existing Instance arbSizedSTgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooRec input x).

Existing Instance arbSizedSTgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThat for (fun (x : Foo) => goodFooPrec input x).
