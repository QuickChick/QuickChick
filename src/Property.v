Set Implicit Arguments.

Require Import List.
Require Import String.

Require Import Show.
Require Import State.
Require Import AbstractGen Gen.
Require Import Arbitrary.

(* Extraction will map this to something that additionally prints stuff *)
Definition trace (A : Type) (s : string) (a : A) : A := a.

(* Note : Simple Callbacks fall under strict positivity of result... *)
Inductive CallbackKind :=
| Counterexample 
| NotCounterexample.

Inductive SmallResult := 
  MkSmallResult : option bool -> bool -> string -> bool -> 
                  list (string * nat) -> SmallResult.

Inductive Callback : Type :=
| PostTest : 
    CallbackKind -> (State -> SmallResult -> nat) -> Callback
| PostFinalFailure : 
    CallbackKind -> (State -> SmallResult -> nat) -> Callback.

Record Result :=
MkResult {
    ok : option bool;
    expect : bool;
    reason : string;
    interrupted : bool;
    stamp : list (string * nat);
    callbacks : list Callback
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

Inductive Rose (A : Type) : Type := 
  MkRose : A -> Lazy (list (Rose A)) -> Rose A.

Definition returnRose {A : Type} (x : A) := MkRose x (lazy nil).

Fixpoint joinRose {A : Type} (r : Rose (Rose A)) : Rose A :=
  match r with
    | MkRose (MkRose a ts) tts =>
      MkRose a (lazy (List.map joinRose (force tts) ++ (force ts)))
  end.

Fixpoint fmapRose {A B : Type} (f : A -> B) (r : Rose A) : Rose B :=
  match r with
    | MkRose x rs => MkRose (f x) (lazy (List.map (fmapRose f) (force rs)))
  end.

Definition bindRose {A B : Type} (m : Rose A) (k : A -> Rose B) : Rose B :=
  joinRose (fmapRose k m).

Record QProp : Type := MkProp
{
  unProp : Rose Result
}.

Definition Property := Gen QProp.
Class Testable (A : Type) : Type :=
{
  property : A -> Property
}.

Instance testResult : Testable Result :=
{|
  (* Left a protectResults out! *)
  property r := returnGen (MkProp (returnRose r)) 
|}.

Definition liftBool (b : bool) : Result :=
  if b then succeeded else updReason failed "Falsifiable".

Instance testBool : Testable bool :=
{|
  property b := property (liftBool b)
|}.

Instance testUnit : Testable unit :=
{|
  property := fun _ => property rejected
|}.

Instance testProp : Testable QProp :=
{|
  property p := returnGen p
|}.

Instance testGenProp (P : Type) : Testable P -> Testable (Gen P) :=
{|
  property p := bindGen p property
|}.
(* Left out exception handling! 
   property p :=
    match p with
      | MkProp r => returnGen r
    end
|}.*)

Definition mapProp {P : Type} {_ : Testable P}
           (f : QProp -> QProp) (prop : P) : Property :=
  fmapGen f (property prop).
  
Definition mapRoseResult {P : Type} {_ : Testable P} 
           (f : Rose Result -> Rose Result) (prop : P) : Property :=
  mapProp (fun p => match p with MkProp t => MkProp (f t) end) prop.

Definition mapTotalResult {prop : Type} {_ : Testable prop}
           (f : Result -> Result) : prop -> Property :=
  mapRoseResult (fmapRose f).

Definition callback {prop : Type} {_ : Testable prop} 
           (cb : Callback) : prop -> Property :=
  mapTotalResult (fun r => addCallback r cb).

Definition whenFail {prop : Type} `{_ : Testable prop}
           (cb : nat -> nat) : prop -> Property :=
  callback (PostFinalFailure Counterexample (fun _st _sr => cb 0)).

(* The following function on its own does not have a decreasing argument... 

Fixpoint props {prop A : Type} {t : Testable prop} 
         (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
  MkRose (property (pf x)) (List.map (props pf shrinker) (shrinker x)).
*)
Fixpoint props' {prop A : Type} {t : Testable prop} (n : nat)
         (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
  match n with
    | O => 
      MkRose (property (pf x)) (lazy nil)
    | S n' =>
      MkRose (property (pf x)) (lazy (List.map (props' n' pf shrinker) (shrinker x)))
  end.

(* Arbitrary choice for number of shrinks.. *)
Definition props {prop A : Type} {t : Testable prop}
           (pf : A -> prop) (shrinker : A -> list A) (x : A) :=
  props' 1000 pf shrinker x.

Definition shrinking {prop A : Type} {_ : Testable prop}
           (shrinker : A -> list A) (x0 : A) (pf : A -> prop) : Property :=
  fmapGen (fun x => MkProp (joinRose (fmapRose unProp x))) 
       (promote fmapRose ((props pf shrinker x0))).

Definition printTestCase {prop : Type} {tp : Testable prop} 
           (s : string) (p : prop) : Property :=
  callback (PostFinalFailure Counterexample (fun _st _res => trace s 0)) p.

Definition forAllShrink {A prop : Type} {_ : Testable prop}
           (show : A -> string)
           (gen : Gen A) (shrinker : A -> list A) (pf : A -> prop) : Property :=
  bindGen gen (fun x => 
    shrinking shrinker x (fun x' =>
      printTestCase (show x' ++ newline) (pf x'))).

Instance testFun {A prop : Type} `{_ : Show A}
         {_ : Arbitrary A} `{_ : Testable prop} : Testable (A -> prop) :=
{
  property f := forAllShrink show arbitrary shrink f
}.
  
(* Test Case Distribution *)
Definition cover {prop : Type} `{_ : Testable prop}
           (b : bool) (n : nat) (s : string) : prop -> Property :=
  if b then 
    mapTotalResult (fun res => 
                      let '(MkResult o e r i st c) := res in
                      MkResult o e r i ((s,n)::st) c)
  else property.

Definition classify {prop : Type} `{_ : Testable prop}
           (b : bool) (s : string) : prop -> Property :=
  cover b 0 s.

Definition label {prop : Type} `{_ : Testable prop}
           (s : string) : prop -> Property :=
  classify true s.

Definition collect {A prop : Type} `{_ : Show A} `{_ : Testable prop} 
           (x : A) : prop -> Property :=
  label (show x).
