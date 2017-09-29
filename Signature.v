Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.
Require Import QuickChick ZArith Strings.Ascii Strings.String.

Module Type QuickChickSig.

  Parameter RandomSeed : Type.

  (* The monad G of generators that hides random seeds. *)
  Parameter G : Type -> Type.

  (** =================================================================== *)
  (** Monadic operations.                                                 *)
  (** =================================================================== *)

  (* Semantics of G base on sets of outcomes *)
  Parameter semGen : forall {A : Type} (g : G A), set A.
  Parameter semGenSize : forall {A : Type} (g : G A) (size : nat), set A.

  (** * Primitive generator combinators *)
  (* Note: Soon, these will be replaced by an ExtLib dependency. *)

  Parameter returnGen  : forall {A : Type}, A -> G A.
  Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter bindGen :  forall {A B : Type}, G A -> (A -> G B) -> G B.

  (* Version of bind where the continuation also takes a _proof_ that
     the value received is within the set of outcomes of the generator *)
  Parameter bindGen' : forall {A B : Type} (g : G A), 
      (forall (a : A), (a \in semGen g) -> G B) -> G B. 

  (* Version of bind for the (G (option .)) monad. 
     Useful for chaining generators that could fail/backtrack. *)
  Parameter bindGenOpt : forall {A B : Type}, 
      G (option A) -> (A -> G (option B)) -> G (option B).

  (* Lifts. *)
  Parameter liftGen : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter liftGen2 : forall {A1 A2 B : Type},
                         (A1 -> A2 -> B) -> G A1 -> G A2 -> G B.
  Parameter liftGen3 : forall {A1 A2 A3 B : Type},
                         (A1 -> A2 -> A3 -> B) -> G A1 -> G A2 -> G A3 -> G B.
  Parameter liftGen4 : forall {A1 A2 A3 A4 B : Type},
                         (A1 -> A2 -> A3 -> A4 -> B) ->
                         G A1 -> G A2 -> G A3 -> G A4 -> G B.
  Parameter liftGen5 : forall {A1 A2 A3 A4 A5 B : Type},
                         (A1 -> A2 -> A3 -> A4 -> A5 -> B) ->
                         G A1 -> G A2 -> G A3 -> G A4-> G A5 -> G B.

  (* sequence *)
  Parameter sequenceGen: forall {A : Type}, list (G A) -> G (list A).
  
  (* foldM *)
  Parameter foldGen :
    forall {A B : Type}, (A -> B -> G A) -> list B -> A -> G A.

  (* Run a generator on a particular random seed. *)
  Parameter run  : forall {A : Type}, G A -> nat -> RandomSeed -> A.

  (** =================================================================== *)
  (** Combinators borrowed from Haskell's QuickCheck.                     *)
  (** =================================================================== *)

  (* List combinators. *)
  Parameter listOf : forall {A : Type}, G A -> G (list A).
  Parameter vectorOf : forall {A : Type}, nat -> G A -> G (list A).

  (* Choose an element of a list. *)
  Parameter elements : forall {A : Type}, A -> list A -> G A.

  (* Uniformly pick a generator from a list. *)
  Parameter oneof : forall {A : Type}, G A -> list (G A) -> G A.

  (* Pick a generator based on a discrete distribution. *)
  Parameter frequency : 
    forall {A : Type}, G A -> list (nat * G A) -> G A.

  (* Same as frequency, but using generators that can fail.
     Performs local backtracking until all options are exhausted. *)
  Parameter backtrack : 
    forall {A : Type}, list (nat * G (option A)) -> G (option A).


  (* Sets QC's internal size parameter. *)
  Parameter resize : forall {A: Type}, nat -> G A -> G A.
  (* Allows a size-parametric generator access to QC's internal size. *)
  Parameter sized : forall {A: Type}, (nat -> G A) -> G A.

  (* Generate-and-test approach to generate data with preconditions. *)
  Parameter suchThatMaybe : 
    forall {A : Type}, G A -> (A -> bool) -> G (option A).
  Parameter suchThatMaybeOpt : 
    forall {A : Type}, G (option A) -> (A -> bool) -> G (option A).

  (** =================================================================== *)
  (** Choosing from intervals (choose).                                   *)
  (** =================================================================== *)

  (* OrdType : reflexive, transitive, antisymmetric predicates. *)
  Class OrdType (A: Type) :=
    {
      leq     : A -> A -> bool;
      refl    : reflexive leq;
      trans   : transitive leq;
      antisym : antisymmetric leq
    }.

  Declare Instance OrdBool : OrdType bool.
  Declare Instance OrdNat  : OrdType nat.
  Declare Instance OrdZ    : OrdType Z.

  (* OrdTypes that support choosing from an interval. *)
  Class ChoosableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       exists seed, fst (randomR (a1, a2) seed) = a)
  }.

  Declare Instance ChooseBool : ChoosableFromInterval bool.
  Declare Instance ChooseNat : ChoosableFromInterval nat. 
  Declare Instance ChooseZ : ChoosableFromInterval Z.
  
  (* Generate a value between two extremes, inclusive. 
     Causes a runtime error if the values are not ordered. *)
  Parameter choose : 
    forall {A : Type} `{ChoosableFromInterval A}, (A * A) -> G A.

  (** =================================================================== *)
  (** Notations.                                                          *)
  (** =================================================================== *)

  Module QcDefaultNotation.
   
    (** 'elems' as a shorthand for elements without a default argument *)
    Notation " 'elems' [ x ] " := 
      (elements x (cons x nil)) : qc_scope.
    Notation " 'elems' [ x ; y ] " := 
      (elements x (cons x (cons y nil))) : qc_scope.
    Notation " 'elems' [ x ; y ; .. ; z ] " :=
      (elements x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
    Notation " 'elems' ( x ;; l ) " :=
      (elements x (cons x l)) (at level 1, no associativity) : qc_scope.
     
    (** 'oneOf' as a shorthand for oneof without a default argument *)
    Notation " 'oneOf' [ x ] " := 
      (oneof x (cons x nil)) : qc_scope.
    Notation " 'oneOf' [ x ; y ] " := 
      (oneof x (cons x (cons y nil))) : qc_scope.
    Notation " 'oneOf' [ x ; y ; .. ; z ] " :=
      (oneof x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
    Notation " 'oneOf' ( x ;; l ) " :=
      (oneof x (cons x l))  (at level 1, no associativity) : qc_scope.
     
    (** 'freq' as a shorthund for frequency without a default argument *)
    Notation " 'freq' [ x ] " := 
      (frequency x (cons x nil)) : qc_scope.
    Notation " 'freq' [ ( n , x ) ; y ] " :=
      (frequency x (cons (n, x) (cons y nil))) : qc_scope.
    Notation " 'freq' [ ( n , x ) ; y ; .. ; z ] " :=
      (frequency x (cons (n, x) (cons y .. (cons z nil) ..))) : qc_scope.
    Notation " 'freq' ( ( n , x ) ;; l ) " :=
      (frequency x (cons (n, x) l)) (at level 1, no associativity) : qc_scope.
   
  End QcDefaultNotation.
  
  (* Note: These will soon be replaced by an ExtLib dependency. *)
  Module QcDoNotation.
   
    Notation "'do!' X <- A ; B" :=
      (bindGen A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
    Notation "'do\'' X <- A ; B" :=
      (bindGen' A (fun X H => B))
      (at level 200, X ident, A at level 100, B at level 200).
    Notation "'doM!' X <- A ; B" :=
      (bindGenOpt A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
   
  End QcDoNotation.

  (** =================================================================== *)
  (** Printing.                                                           *)
  (** =================================================================== *)

  (* Show typeclass. *)
  Class Show (A : Type) : Type :=
    {
      show : A -> string
    }.

  (* Instances. *)
  Declare Instance showNat    : Show nat.
  Declare Instance showBool   : Show bool.
  Declare Instance showInt    : Show Z.
  Declare Instance showString : Show string.

  Declare Instance showList : 
    forall {A : Type} `{Show A}, Show (list A).
  Declare Instance showPair :
    forall {A B : Type} `{Show A} `{Show B}, Show (A * B).
  Declare Instance showOpt :
    forall {A : Type} `{Show A}, Show (option A).
  Declare Instance showEx :
    forall {A} `{Show A} P, Show ({x : A | P x}).

  (* Newline *)
  Definition nl : string := String (ascii_of_nat 10) EmptyString.
  



End QuickChickSig.

