Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.
Require Import QuickChick ZArith Strings.Ascii Strings.String.
Require Import QuickChickInterface.


(* This module is just to keep the BasicInterface up-to-date with the implementation. *)

Module ConsistencyCheck : QuickChickSig.

  Definition RandomSeed := RandomSeed.

  Definition G := @G.
  Definition semGen := @semGen.
  Definition semGenSize := @semGenSize.
  Definition returnGen := @returnGen.
  Definition fmap := @fmap.
  Definition bindGen := @bindGen.
  Definition bindGen' := @bindGen'.
  Definition bindGenOpt := @bindGenOpt.
  Definition liftGen := @liftGen.
  Definition liftGen2 := @liftGen2.
  Definition liftGen3 := @liftGen3.
  Definition liftGen4 := @liftGen4.
  Definition liftGen5 := @liftGen5.
  Definition sequenceGen := @sequenceGen.
  Definition foldGen := @foldGen.
  Definition run := @run.
  Definition listOf := @listOf.
  Definition vectorOf := @vectorOf.
  Definition elements := @elements.
  Definition oneof := @oneof.
  Definition frequency := @frequency.
  Definition backtrack := @backtrack.
  Definition resize := @resize.
  Definition sized := @sized.
  Definition suchThatMaybe := @suchThatMaybe.
  Definition suchThatMaybeOpt := @suchThatMaybeOpt.

  Definition OrdBool := OrdBool.
  Definition OrdNat := OrdNat.
  Definition OrdZ := OrdZ.

  Definition ChooseBool := ChooseBool.
  Definition ChooseNat := ChooseNat.
  Definition ChooseZ := ChooseZ.

  Definition choose := @choose.

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
      (at level 200, X ident, A at level 100, B at level 200).
    Notation "'do\'' X <- A ; B" :=
      (bindGen' A (fun X H => B))
      (at level 200, X ident, A at level 100, B at level 200).
    Notation "'doM!' X <- A ; B" :=
      (bindGenOpt A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
   
  End QcDoNotation.


  Definition showNat := showNat    .
  Definition showBool := showBool   .
  Definition showInt := showInt    .
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
  Definition Eq_bool   := @Eq_bool.
  Definition Eq_nat    := @Eq_nat.
  Definition Eq_opt    := @Eq_opt.
  Definition Eq_prod   := @Eq_prod.
  Definition Eq_sum    := @Eq_sum.
  Definition Eq_list   := @Eq_list.
  Definition Eq_ascii  := @Eq_ascii.
  Definition Eq_string := @Eq_string.

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


  Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

End ConsistencyCheck.

