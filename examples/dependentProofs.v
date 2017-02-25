From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.
Require Import List.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Require Import DependentTest zoo.

Set Bullet Behavior "Strict Subproofs".


(* Notes :
   Monotonicity should be easy and we should be able to derive
   it just from the shape of the generator.
 *)

Instance backtrackSizeMonotonic :
  forall {A : Type} (lg : seq (nat * G (option A))),
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (backtrack lg).
Admitted.

Print genGoodNarrow'.

Typeclasses eauto := debug.

(* Interesting. Do we need Global instance?? *) 
Existing Instance genGoodNarrow'.  (* ???? *)

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

Instance genGoodNarrowMon (s : nat) (input : nat) :
  SizeMonotonic (@arbitrarySizeST _ (fun (x : Foo) => goodFooNarrow input x) _ s).
Proof.
  revert input.
  refine (nat_ind (fun s => forall input, SizeMonotonic (arbitrarySizeST s)) (fun input => _) (fun s IHs input => _) s).
  -
    (* Experience shows that we will an annotation for the generators list.
       However current implementation uses references with a non transparent way
       so we should NOT run the code twice *)
    refine (backtrackSizeMonotonic _ _).
    refine (cons_subset _ _ _ _ (nil_subset _)).
    now eauto with typeclass_instances.
  - refine (backtrackSizeMonotonic _ _).
    refine (cons_subset _ _ _ _ _).
    now eauto with typeclass_instances.
    refine (cons_subset _ _ _ _ _).
    simpl. (* dep_dec gets simplified *)
    refine (@bindOptMonotonic _ _ _ _ (IHs 0) _).
    eapply nil_subset.
Qed.

Existing Instance genGoodUnif'.  (* ???? *)

(* ArbitrarySizedSuchThat Foo [eta goodFooNarrow input] *)
Instance genGoodUnifMon (s : nat) (input : nat) :
  SizeMonotonic (@arbitrarySizeST _ (fun (x : Foo) => goodFooUnif input x) _ s).
Proof.
  revert input.
  refine (nat_ind (fun s => forall input, SizeMonotonic (arbitrarySizeST s)) (fun input => _) (fun s IHs input => _) s).
  - (* Experience shows that we will an annotation for the generators list.
       However current implementation uses references with a non transparent way
       so we should NOT run the code twice *)
    refine (backtrackSizeMonotonic _ (cons_subset _ _ _ _ (nil_subset _))).
    now eauto with typeclass_instances.
  - refine (backtrackSizeMonotonic _ _).
    refine (cons_subset _ _ _ _ (nil_subset _)).
    now eauto with typeclass_instances.
Qed.

Existing Instance genGoodMatch'.

(* ArbitrarySizedSuchThat Foo [eta goodFooNarrow input] *)
Instance genGoodMatchMon (s : nat) :
  forall input, SizeMonotonic (@arbitrarySizeST _ (fun (x : Foo) => goodFooMatch input x) _ s).
Proof.
  refine
    (nat_ind
       (fun s => forall input, SizeMonotonic (arbitrarySizeST s))
       (fun input =>
          (backtrackSizeMonotonic
             [(1,
               match input with
                 | 0 => returnGen (Some Foo1)
                 | _.+1 => returnGen None
               end)]
             (match input with
                | 0 => (cons_subset _ _ _ (returnGenSizeMonotonic _) (nil_subset _))
                | S i => (cons_subset _ _ _ (returnGenSizeMonotonic _) (nil_subset _))
              end)))
       (fun s IHs input =>
          (backtrackSizeMonotonic
             [(1,
               match input with
                 | 0 => returnGen (Some Foo1)
                 | _.+1 => returnGen None
               end)]
             (match input with
                | 0 => (cons_subset _ _ _ (returnGenSizeMonotonic _) (nil_subset _))
                | S i => (cons_subset _ _ _ (returnGenSizeMonotonic _) (nil_subset _))
              end))
       ) s).
Qed.