Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.
Require Import QuickChick ZArith Strings.Ascii Strings.String.

(* ====================================================================== *)
(* CONTENTS                                                               *)
(* ====================================================================== *)
(** Monadic operations.                                                   *)
(** Combinators borrowed from Haskell's QuickCheck.                       *)
(** Choosing from intervals (choose).                                     *)
(** Notations.                                                            *)
(** Printing.                                                             *)
(** Generation typeclasses and instances.                                 *)
(** Shrinking typeclass and instances.                                    *)
(** Arbitrary and typeclass hierarchy.                                    *)
(** Properties - Checkers                                                 *)
(** Checker combinators.                                                  *)
(** Decidability.                                                         *)
(** Decidable Equality.                                                   *)
(** QuickChick toplevel commands and arguments.                           *)
(** Generators for data satisfying inductive invariants.                  *)
(** Automatic instance derivation.                                        *)
(* ====================================================================== *)

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
(* Note: We also provide an (ext-lib) Monad instance based on these. *)

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
(*
  Class OrdType (A: Type) :=
    {
      leq     : A -> A -> bool;
      refl    : reflexive leq;
      trans   : transitive leq;
      antisym : antisymmetric leq
    }.
 *)

Declare Instance OrdBool : OrdType bool.
Declare Instance OrdNat  : OrdType nat.
Declare Instance OrdZ    : OrdType Z.

(* OrdTypes that support choosing from an interval. *)
(* 
  Class ChoosableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       exists seed, fst (randomR (a1, a2) seed) = a)
  }.
*)

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

(* Deprecated: Using the ExtLib notations is recommended. *)
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
(*
Class Show (A : Type) : Type :=
  {
    show : A -> string
  }.
 *)

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

(** =================================================================== *)
(** Generation typeclasses and instances.                               *)
(** =================================================================== *)

(*
Class GenSized (A : Type) := { arbitrarySized : nat -> G A }.
Class Gen (A : Type) := { arbitrary : G A }.
 *)

(* Automatic conversion of GenSized instances to Gen using 'sized'. *)
Declare Instance GenOfGenSized {A} `{GenSized A} : Gen A. 

(* Basic generator instances *)
Declare Instance genBoolSized : GenSized bool.
Declare Instance genNatSized  : GenSized nat.
Declare Instance genZSized    : GenSized Z.

Declare Instance genListSized :
  forall {A : Type} `{GenSized A}, GenSized (list A).
Declare Instance genList :
  forall {A : Type} `{Gen A}, Gen (list A). 
Declare Instance genOption : 
  forall {A : Type} `{Gen A}, Gen (option A).
Declare Instance genPairSized :
  forall {A B : Type} `{GenSized A} `{GenSized B}, GenSized (A*B).
Declare Instance genPair : 
  forall {A B : Type} `{Gen A} `{Gen B}, Gen (A * B).

(* TODO: Strings? *)

(** =================================================================== *)
(** Shrinking typeclass and instances.                                  *)
(** =================================================================== *)

(** Shrink class *)
(*
Class Shrink (A : Type) :=
  { 
    shrink : A -> list A 
  }.
 *)

(** Shrink instances *)
Declare Instance shrinkBool : Shrink bool.
Declare Instance shrinkNat : Shrink nat.
Declare Instance shrinkZ : Shrink Z.

Declare Instance shrinkList {A : Type} `{Shrink A} : Shrink (list A).
Declare Instance shrinkPair {A B} `{Shrink A} `{Shrink B} : Shrink (A * B).
Declare Instance shrinkOption {A : Type} `{Shrink A} : Shrink (option A).

(** =================================================================== *)
(** Arbitrary and typeclass hierarchy.                                  *)
(** =================================================================== *)

(** Arbitrary Class *)
(*
Class Arbitrary (A : Type) `{Gen A} `{Shrink A}.
 *)

(** 
                            GenSized 
                               |
                               |
                              Gen   Shrink
                                \    /
                                 \  /
                               Arbitrary
 *)


(* Automatic conversion *)
Declare Instance ArbitraryOfGenShrink : 
  forall {A} `{Gen A} `{Shrink A}, Arbitrary A.

(** =================================================================== *)
(** Properties - Checkers                                               *)
(** =================================================================== *)

(* The opaque type of QuickChick properties that can be checked. *)
Parameter Checker : Type.

(* A Class that indicates we can check a type A. *)
(* 
Class Checkable (A : Type) : Type :=
  {
    checker : A -> Checker
  }.
 *)

(* Bools signify pass/fail. *)
Declare Instance testBool : Checkable bool.
(* Units signify discarded tests. *)
Declare Instance testUnit : Checkable unit.

(* Given a generator for showable As, construct a Checker. *)
Parameter forAll : 
  forall {A prop : Type} `{Checkable prop} `{Show A} 
         (gen : G A)  (pf : A -> prop), Checker.
(* Variant of forAll that uses evidence for the generated value. *)
Parameter forAllProof : 
  forall {A prop : Type} `{Checkable prop} `{Show A}
         (gen : G A)  (pf : forall (x : A), semGen gen x -> prop), Checker.

(* Given a generator and a shrinker for showable As, construct a Checker *)
Parameter forAllShrink :
  forall {A prop : Type} `{Checkable prop} `{Show A}
         (gen : G A) (shrinker : A -> list A) (pf : A -> prop), Checker.
(* TODO: Do we need a forAllShrinkProof variant? *)

(* Typeclass magic: Lift (Show, Gen, Shrink) instances for A 
   to a Checker for functions A -> prop. *)
Declare Instance testFun : 
  forall {A prop : Type} `{Show A} `{Arbitrary A} `{Checkable prop},
    Checkable (A -> prop).

(* Typeclass magic revisited: Similar thing for products. *)
Declare Instance testProd :
  forall {A : Type} {prop : A -> Type} `{Show A} `{Arbitrary A} 
         `{forall x : A, Checkable (prop x)},
    Checkable (forall (x : A), prop x).

(* Test polymorphic functions by instantiating to 'nat'. :-) *)
Declare Instance testPolyFun :
  forall {prop : Type -> Type} `{Checkable (prop nat)}, 
    Checkable (forall T, prop T).

(** =================================================================== *)
(** Checker combinators.                                                *)
(** =================================================================== *)

(* Print a specific string if the property fails. *)
Parameter whenFail : 
  forall {prop : Type} `{Checkable prop} (str : string), prop -> Checker.

(* Signify that the property is expected to fail. *)
Parameter expectFailure :
  forall {prop: Type} `{Checkable prop} (p: prop), Checker.

(* Collect statistics across all tests. *)
Parameter collect :
  forall {A prop : Type} `{Show A} `{Checkable prop} (x : A),
    prop -> Checker.

(* Set the reason for failure. 
   Will only count shrinks as valid if they preserve the tag. *)
Parameter tag : 
  forall {prop : Type} `{Checkable prop} (t : string), prop -> Checker.

(* Take the conjunction/disjunction of all the checkers. *)
Parameter conjoin : forall (l : list Checker), Checker.
Parameter disjoin : forall (l : list Checker), Checker.

(* Conditional properties. Invalid generated inputs are discarded. *)
Parameter implication :
  forall {prop : Type} `{Checkable prop} (b : bool) (p : prop), Checker.

(* Notation for implication. Clashes a lot, so it gets its own module. *)
Module QcNotation.
  Export QcDefaultNotation.

  Notation "x ==> y" := 
    (implication x y) (at level 55, right associativity)
    : Checker_scope.
End QcNotation.

(** =================================================================== *)
(** Decidability.                                                       *)
(** =================================================================== *)

(* Decidability typeclass using ssreflect's 'decidable'. *)
(* 
Class Dec (P : Prop) : Type := { dec : decidable P }.
 *)

(* Decidable properties are Checkable. *)
Declare Instance testDec {P} `{H : Dec P} : Checkable P.

(* Logic Combinator instances. *)
Declare Instance Dec_neg {P} {H : Dec P} : Dec (~ P).
Declare Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Declare Instance Dec_disj {P Q} {H : Dec P} {I : Dec Q} : Dec (P \/ Q).

(* Convenient notation. *)
Notation "P '?'" := (match (@dec P _) with 
                     | left _ => true
                     | right _ => false
                     end) (at level 100).

(** =================================================================== *)
(** Decidable Equality.                                                 *)
(** =================================================================== *)

(*
Class Eq (A : Type) :=
  { 
    dec_eq : forall (x y : A), decidable (x = y)
  }.
*)

(* Automation and conversions for Dec. *)
Parameter dec_if_dec_eq : 
  forall {A} (x y: A),  Dec (x = y) -> {x = y} + {x <> y}.

(* TODO: How to include LTac here? *)
(* Tactic that decides equalities of the form Dec (x = y). *)
(* Ltac dec_eq. *)

Declare Instance Eq__Dec {A} `{H : Eq A} (x y : A) : Dec (x = y).

(* Lifting common decidable instances *)
Declare Instance Eq_bool : Eq bool.
Declare Instance Eq_nat  : Eq nat.
Declare Instance Eq_opt (A : Type) `{Eq A} : Eq (option A).
Declare Instance Eq_prod (A B : Type) `{Eq A} `{Eq B} : Eq (A * B).
Declare Instance Eq_sum (A B : Type) `{Eq A} `{Eq B} : Eq (A + B).
Declare Instance Eq_list (A : Type) `{Eq A} : Eq (list A).

Declare Instance Eq_ascii : Eq ascii.
Declare Instance Eq_string : Eq string.

(** =================================================================== *)
(** QuickChick toplevel commands and arguments.                         *)
(** =================================================================== *)

(* Samples a generator. 'g' is of type 'G A' for showable 'A'. *)
(** 
    Sample g.
 *)

(* Runs a test. 'prop' must be 'Checkable'. *)
(** 
     QuickChick prop. 
 *)

(* Arguments to customize execution. *)
Record Args := 
  MkArgs
    {
      (* Re-execute a test. *)
      (* Default: None *)
      replay     : option (RandomSeed * nat); 
      (* Maximum number of successful tests to run. *)
      (* Default: 10000 *)
      maxSuccess : nat;                       
      (* Maximum number of discards to accept. *)
      (* Default: 20000 *)
      maxDiscard : nat;
      (* Maximum number of shrinks to perform before terminating. *)
      (* Default : 1000 *)
      maxShrinks : nat;
      (* Maximum size of terms to generate (depth). *)
      (* Default : 7 *)
      maxSize    : nat;
      (* Verbosity. Note: Doesn't do much... *)
      (* Default true. *)
      chatty     : bool
    }.

(* Instead of record updates, you can overwrite extraction constants. *)
(*
   Extract Constant defNumTests    => "10000".
   Extract Constant defNumDiscards => "(2 * defNumTests)".
   Extract Constant defNumShrinks  => "1000".
   Extract Constant defSize        => "7".
 *)

(** =================================================================== *)
(** Generators for data satisfying inductive invariants.                *)
(** =================================================================== *)

(* Sized and unsized version, plus convenient notation. *)
(*
Class GenSizedSuchThat (A : Type) (P : A -> Prop) := 
  { 
    arbitrarySizeST : nat -> G (option A) 
  }.

Class GenSuchThat (A : Type) (P : A -> Prop) := 
  { 
    arbitraryST : G (option A)
  }.
 *)
Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

(** =================================================================== *)
(** Automatic instance derivation.                                      *)
(** =================================================================== *)

(* QuickChick allows the automatic derivation of typeclass instances 
   for simple types: 

     Derive <class> for <T>.

   <class> must be one of: GenSized , Shrink , Arbitrary , Show
   <T> must be an inductive defined datatype (think Haskell/OCaml).
 *)

(* QuickChick also allows for the automatic derivation of generators 
   satisfying preconditions in the form of inductive relations:

     Derive ArbitrarySizedSuchThat for (fun x => P x1 ... x .... xn).

   <P> must be an inductively defined relation.
   <x> is the function to be generated.
   <x1...xn> are (implicitly universally quantified) variable names. 
 *)

 (* QuickChick also allows automatic derivations of proofs of 
    correctness of its derived generators! For more, look 
    at: 
    
    - our ITP paper 
    - our POPL paper
    - examples/DependentTest.v

  *)

End QuickChickSig.

