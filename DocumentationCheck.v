Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.
Require Import QuickChick ZArith Strings.Ascii Strings.String.
Require Import QuickChickInterface.


(* This module is just to keep the BasicInterface up-to-date with the implementation. *)

Module ConsistencyCheck : QuickChickSig.

  Definition RandomSeed := RandomSeed.

  Definition G := @G.
  Definition semGen := @semProd G ProducerGen.
  Definition semGenSize := @semGenSize.
  Definition Functor_G := @Functor_Monad _ (@super _ ProducerGen). 
  Definition Applicative_G :=
    @Applicative_Monad _ (@super _ ProducerGen). 
  Definition Monad_G := @super _ ProducerGen. 
  Definition bindGen' := @bindPf G ProducerGen.
  Definition bindGenOpt := @bindOpt G ProducerGen.
  Definition run := @Generators.run.
  Definition listOf := @listOf G ProducerGen.
  Definition vectorOf := @vectorOf G ProducerGen.
  Definition elems_ := @elems_ G ProducerGen.
  Definition oneOf_ := @oneOf_ G ProducerGen.
  Definition freq_ := @freq_.
  Definition backtrack := @backtrack.
  Definition resize := @resize G ProducerGen.
  Definition sized := @sized G ProducerGen.
  Definition suchThatMaybe := @suchThatMaybe.
  Definition suchThatMaybeOpt := @suchThatMaybeOpt.

  Class OrdType (A: Type) :=
    {
      leq     : A -> A -> bool;
      refl    : reflexive leq;
      trans   : transitive leq;
      antisym : antisymmetric leq
    }.

  Definition OrdBool := OrdBool.
  Definition OrdNat := OrdNat.
  Definition OrdZ := OrdZ.

  Class ChoosableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       exists seed, fst (randomR (a1, a2) seed) = a)
  }.

  Definition ChooseNat := ChooseNat.
  Definition ChooseZ := ChooseZ.

  Definition choose := @choose G ProducerGen.

  Module QcDefaultNotation.
(*
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
  *)
  End QcDefaultNotation.

  (* Note: These will soon be replaced by an ExtLib dependency. *)
  Module QcDoNotation.

    Notation "'do!' X <- A ; B" :=
      (bindGen A (fun X => B))
      (at level 200, X name, A at level 100, B at level 200).
    Notation "'do\'' X <- A ; B" :=
      (bindGen' A (fun X H => B))
      (at level 200, X name, A at level 100, B at level 200).
    Notation "'doM!' X <- A ; B" :=
      (bindGenOpt A (fun X => B))
      (at level 200, X name, A at level 100, B at level 200).

  End QcDoNotation.


  Definition showNat := showNat    .
  Definition showBool := showBool   .
  Definition showZ := showZ    .
  Definition showString := showString .

  Definition showList := @showList .
  Definition showPair := @showPair .
  Definition showOpt := @showOpt .
  Definition showEx := @showEx .

  Definition nl := nl.

  Definition GenOfGenSized := @GenOfGenSized.

  Definition genBoolSized := @genBoolSized .
  Definition genNatSized := @genNatSized  .
  Definition genZSized := @genZSized    .

  Definition genListSized := @genListSized .
  Definition genList := @genList .
  Definition genOption := @genOption .
  Definition genPairSized := @genPairSized .
  Definition genPair := @Instances.genPair .

  (* TODO: Strings? *)

  Definition shrinkBool := shrinkBool.
  Definition shrinkNat := shrinkNat .
  Definition shrinkZ := shrinkZ .

  Definition shrinkList := @shrinkList .
  Definition shrinkPair := @shrinkPair .
  Definition shrinkOption := @shrinkOption .

  Definition ArbitraryOfGenShrink := @ArbitraryOfGenShrink.

  Definition Checker := @Checker.

  Definition testBool := testBool .
  Definition testUnit := testUnit .

  Definition forAll := @forAll.
  Definition forAllProof := @forAllProof.
  Definition forAllShrink := @forAllShrink.
  Definition testFun := @testFun .
  Definition testProd := @testProd.
  Definition testPolyFun := @testPolyFun.
  Definition whenFail := @whenFail.
  Definition expectFailure := @expectFailure.
  Definition collect := @collect.
  Definition tag := @tag.
  Definition conjoin := @conjoin.
  Definition disjoin := @disjoin.

  Definition implication := @implication.

  Module QcNotation.
    Export QcDefaultNotation.

    Notation "x ==> y" :=
      (implication x y) (at level 55, right associativity)
      : Checker_scope.
  End QcNotation.

  Definition testDec := @testDec .
  Definition Dec_neg := @Dec_neg  .
  Definition Dec_conj := @Dec_conj .
  Definition Dec_disj := @Dec_disj .

  (* Convenient notation. *)
  Notation "P '?'" := (match (@dec P _) with
                       | left _ => true
                       | right _ => false
                       end) (at level 100).

  Definition dec_if_dec_eq := @dec_if_dec_eq.
  Definition Eq__Dec     := @Eq__Dec.
  Definition Dec_eq_unit   := @Dec_eq_unit.
  Definition Dec_eq_bool   := @Dec_eq_bool.
  Definition Dec_eq_nat    := @Dec_eq_nat.
  Definition Dec_eq_Z      := @Dec_eq_Z.
  Definition Dec_eq_N      := @Dec_eq_N.
  Definition Dec_eq_opt    := @Dec_eq_opt.
  Definition Dec_eq_prod   := @Dec_eq_prod.
  Definition Dec_eq_sum    := @Dec_eq_sum.
  Definition Dec_eq_list   := @Dec_eq_list.
  Definition Dec_eq_ascii  := @Dec_eq_ascii.
  Definition Dec_eq_string := @Dec_eq_string.

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

End ConsistencyCheck.
