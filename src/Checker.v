Set Implicit Arguments.

Require Import List.
Require Import String.

Require Import RoseTrees.
Require Import Show.
Require Import State.
Require Import GenLow GenHigh.
Require Import Arbitrary.

Import GenLow GenHigh.

(* Extraction will map this to something that additionally prints stuff *)
Definition trace (A : Type) (s : string) (a : A) : A := a.

(* Note : Simple Callbacks fall under strict positivity of result... *)
Inductive CallbackKind :=
| Counterexample
| NotCounterexample.

Inductive SmallResult :=
  MkSmallResult : option bool -> bool -> string -> bool ->
                  list string -> SmallResult.

Inductive Callback : Type :=
| PostTest :
    CallbackKind -> (State -> SmallResult -> nat) -> Callback
| PostFinalFailure :
    CallbackKind -> (State -> SmallResult -> nat) -> Callback.

Record Result :=
  MkResult {
      ok          : option bool; (* Test case result - maybe == discard *)
      expect      : bool;        (* If false, property should fail *)
      reason      : string;      (* Error message *)
      interrupted : bool;        (* ? *)
      stamp       : list string; (* Collected values for this test case *)
      callbacks   : list Callback
    }.

(* I WANT RECORD UPDATES :'( *)
Definition succeeded := MkResult (Some true ) true "" false nil nil.
Definition failed    := MkResult (Some false) true "" false nil nil.
Definition rejected  := MkResult (   None   ) true "" false nil nil.

Definition updReason (r : Result) (s' : string) : Result :=
  match r with
    | MkResult o e _ i s c => MkResult o e s' i s c
  end.

Definition addCallback (res : Result) (c : Callback) : Result :=
  match res with
    | MkResult o e r i s cs => MkResult o e r i s (cons c cs)
  end.

(* CH: The name of this should change; we no longer call checkers props *)
Record QProp : Type :=
  MkProp
    {
      unProp : Rose Result
    }.

Definition Checker : Type := G QProp.

Class Checkable (A : Type) : Type :=
  {
    checker : A -> Checker
  }.

(* mapping and lifting functions *)

Definition liftBool (b : bool) : Result :=
  if b then succeeded else updReason failed "Falsifiable".

Definition mapProp {P : Type} {_ : Checkable P}
           (f : QProp -> QProp) (prop : P) : Checker :=
  fmap f (checker prop).

Definition mapRoseResult {P : Type} {_ : Checkable P}
           (f : Rose Result -> Rose Result) (prop : P) : Checker :=
  mapProp (fun p => match p with MkProp t => MkProp (f t) end) prop.

Definition mapTotalResult {prop : Type} {_ : Checkable prop}
           (f : Result -> Result) : prop -> Checker :=
  mapRoseResult (fmapRose f).

Global Instance testResult : Checkable Result :=
  {|
    (* Left a protectResults out! *)
    checker r := returnGen (MkProp (returnRose r))
  |}.


Global Instance testBool : Checkable bool :=
  {|
    checker b := checker (liftBool b)
  |}.

(* ZP/CH: what's the relation between unit and discards? *)
Global Instance testUnit : Checkable unit :=
  {|
    checker := fun _ => checker rejected
  |}.

Global Instance testProp : Checkable QProp :=
  {|
    checker p := returnGen p
  |}.

Global Instance testGenProp (P : Type) `{Checkable P} : Checkable (G P) :=
  {|
    checker p := bindGen p checker
  |}.

Global Instance testChecker : Checkable Checker :=
  {|
      checker x := x
  |}.

(* Checker Combinators *)

(* The following function on its own does not have a decreasing argument...

     Fixpoint props {prop A : Type} {t : Checkable prop}
                    (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
       MkRose (checker (pf x)) (List.map (props pf shrinker) (shrinker x)).
 *)
Fixpoint props' {prop A : Type} {t : Checkable prop} (n : nat)
         (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
  match n with
    | O =>
      MkRose (checker (pf x)) (lazy nil)
    | S n' =>
      MkRose (checker (pf x)) (lazy (List.map (props' n' pf shrinker) (shrinker x)))
  end.

(* Arbitrary choice for number of shrinks.. *)
Definition props {prop A : Type} `{Checkable prop}
           (pf : A -> prop) (shrinker : A -> list A) (x : A) : Rose Checker :=
  props' 1000 pf shrinker x.

Definition shrinking {prop A : Type} `{Checkable prop}
           (shrinker : A -> list A) (x0 : A) (pf : A -> prop) : Checker :=
  fmap (fun x => MkProp (joinRose (fmapRose unProp x)))
       (promote (props pf shrinker x0)).

Definition callback {prop : Type} `{Checkable prop}
           (cb : Callback) : prop -> Checker :=
  mapTotalResult (fun r => addCallback r cb).

Definition printTestCase {prop : Type} `{Checkable prop}
           (s : string) (p : prop) : Checker :=
  callback (PostFinalFailure Counterexample (fun _st _res => trace s 0)) p.

Definition whenFail {prop : Type} `{Checkable prop}
           (str : string) : prop -> Checker :=
  callback (PostFinalFailure Counterexample (fun _st _sr => trace str 0)).


Definition expectFailure {prop: Type} `{Checkable prop} (p: prop) :=
  mapTotalResult (fun res =>
                    MkResult (ok res) false (reason res)
                             (interrupted res) (stamp res) (callbacks res))
                 p.

(* NOTE: Ignoring the nat argument. Use label or collect ONLY *)
Definition cover {prop : Type} {_ : Checkable prop}
           (b : bool) (n : nat) (s : string) : prop -> Checker :=
  if b then
    mapTotalResult (fun res =>
                      let '(MkResult o e r i st c) := res in
                      MkResult o e r i (s :: st) c)
  else checker.

Definition classify {prop : Type} {_ : Checkable prop}
           (b : bool) (s : string) : prop -> Checker :=
  cover b 0 s.

Definition label {prop : Type} {_ : Checkable prop}
           (s : string) : prop -> Checker :=
  classify true s.

Definition collect {A prop : Type} `{_ : Show A} {_ : Checkable prop}
           (x : A) : prop -> Checker :=
  label (show x).


Definition implication {prop : Type} `{Checkable prop} (b : bool) (p : prop) : Checker :=
  if b then checker p else (returnGen (MkProp (returnRose rejected))).


Definition forAll {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G A)  (pf : A -> prop) : Checker :=
  bindGen gen (fun x =>
                 printTestCase (show x ++ newline) (pf x)).

Definition forAllShrink {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=

  bindGen gen (fun x : A =>
                 shrinking shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

Definition forAllShrinkShow {A prop : Type} {_ : Checkable prop}
           (gen : G A) (shrinker : A -> list A) (show' : A -> string) (pf : A -> prop) : Checker :=
  bindGen gen (fun x =>
                 shrinking shrinker x (fun x' =>
                                         printTestCase (show' x' ++ newline) (pf x'))).

Global Instance testFun {A prop : Type} `{Show A}
       {_ : Arbitrary A} {_ : Checkable prop} : Checkable (A -> prop) :=
  {
    checker f := forAllShrink arbitrary shrink f
  }.

Global Instance testPolyFun {prop : Type -> Type} {_ : Checkable (prop nat)} : Checkable (forall T, prop T) :=
  {
    checker f := printTestCase "" (f nat)
  }.

Global Instance testPolyFunSet {prop : Set -> Type} {_ : Checkable (prop nat)} : Checkable (forall T, prop T) :=
  {
    checker f := printTestCase "" (f nat)
  }.

Notation "x ==> y" := (implication x y) (at level 55, right associativity)
                      : Checker_scope.
