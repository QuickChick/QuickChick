(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.

From ExtLib.Structures Require Export
     Functor Applicative Monads.
Import MonadNotation.
Open Scope monad_scope.

Require Import Sets LazyList RandomQC.
(* RandomQC for OrdType. Refactor? *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Definition isNone {T : Type} (u : option T) :=
  match u with
    | Some _ => false
    | None => true
  end.

Class EnumerableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    range : A * A -> LazyList A;
    rangeCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       In_ll a (range (a1,a2)))
  }.

(* This is weird even in the gen case. *)
(*
Program Instance EnumerableBool : EnumerableFromInterval bool :=
  {
  range :=
    fun (b1,b2) =>
      
    lcons true (fun _ => lsing false)
  }.
 *)

Require Import Lia.
Program Instance RangeNat : EnumerableFromInterval nat :=
  {
    range p := lazy_seq S (fst p) (S (snd p - fst p))
  }.
Next Obligation.
Admitted.
(*  split.
  - move => /andP [/leP H1 /leP H2].
    clear H.
    move : a a1 H1 H2.
    induction a2.
    + left; lia.
    + move => a a1 H1 H2.
      destruct (Nat.eqb a1 a.+1) eqn:Eq.
      * left; apply Nat.eqb_eq in Eq; subst; reflexivity.
      * 
        -- 
        right. 
        destruct 
        assert (a1 = 0) by lia; subst.
      
      unfold In_ll.
      rewrite -> Nat.sub_0_r.
      destruct a2.
      * simpl.*)

(*
Instance ChooseZ : ChoosableFromInterval Z :=
  {
    randomR := randomRInt;
    randomRCorrect := randomRIntCorrect
  }.

Instance ChooseN : ChoosableFromInterval N :=
  {
    randomR := randomRN;
    randomRCorrect := randomRNCorrect
  }.
*)

Module Type Sig.

  (** * Type of generators *)

  Parameter E : Type -> Type.

  (** * Primitive generator combinators *)

  Parameter returnE  : forall {A : Type}, A -> E A.
  (* TODO: Add dependent combinator *)
  Parameter bindE :
    forall {A B : Type}, E A -> (A -> E B) -> E B.
  Parameter run  : forall {A : Type}, E A -> nat -> LazyList A.
  Parameter fmap :
    forall {A B : Type}, (A -> B) -> E A -> E B.
  Parameter apGen :
    forall {A B : Type}, E (A -> B) -> E A -> E B.
  Parameter sized : forall {A: Type}, (nat -> E A) -> E A.
  Parameter resize : forall {A: Type}, nat -> E A -> E A.

  (* Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A). *)
  Parameter range :
    forall {A : Type} `{EnumerableFromInterval A}, (A * A) -> E A.
  Parameter sample : forall {A : Type}, E A -> list A.
(*  Parameter sample1 : forall {A : Type}, G A -> A. *)

(*
  (* LL: The abstraction barrier is annoying :D *)
  Parameter variant : forall {A : Type}, SplitPath -> G A -> G A.
  Parameter reallyUnsafePromote : forall {r A:Type}, (r -> G A) -> G (r -> A).

  Parameter promoteVariant : forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size 
                               (r r1 r2 : RandomSeed),
                               randomSplit r = (r1,r2) ->                              
                               run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
                               run g size (varySeed (f a) r1).
*)

  (** * Semantics of enumerators *)

  (* Set of outcomes semantics definitions (repeated below) *)
  Definition semEnumSize {A : Type} (e : E A) (size : nat) : set A :=
    fun x => In_ll x (run e size).
  Definition semEnum {A : Type} (g : E A) : set A :=
    \bigcup_size semEnumSize g size.

  (* Set of outcomes semantics for generators that can fail
     (ignoring [None] as a value). *)
  Definition semEnumSizeOpt {A : Type} (g : E (option A)) (s : nat) : set A :=
    somes (semEnumSize g s).

  Definition semEnumOpt {A : Type} (g : E (option A)) : set A :=
    somes (semEnum g).

  Parameter semEnumOpt_equiv : forall {A} (g : E (option A)),
    semEnumOpt g <--> \bigcup_s semEnumSizeOpt g s.

  Parameter bindEnum' : forall {A B : Type} (g : E A), 
                       (forall (a : A), (a \in semEnum g) -> E B) -> E B. 

  Arguments bindEnum' [A] [B] _ _.

  (** * Properties of generators *)

  (** A generator is [Unsized] if its semantics does not depend on the runtime size *)
  (* begin Unsized *)
  Class UnsizedE {A} (g : E A) :=
    unsized : forall s1 s2, semEnumSize g s1 <--> semEnumSize g s2.
  (* end Unsized *)
  
  (** Sized generators monotonic in the size parameter *)
  Class SizedMonotonicE {A} (g : nat -> E A) :=
    sizeMonotonic : forall s s1 s2,
      s1 <= s2 ->
      semEnumSize (g s1) s \subset semEnumSize (g s2) s.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOptE {A} (g : nat -> E (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      s1 <= s2 ->
      semEnumSizeOpt (g s1) s \subset semEnumSizeOpt (g s2) s.
  
  (** Enumerators monotonic in the runtime size parameter *)
  Class SizeMonotonicE {A} (g : E A) :=
    monotonic : forall s1 s2,
      s1 <= s2 ->
      semEnumSize g s1 \subset semEnumSize g s2.

  (** Enumerators monotonic in the runtime size parameter *)
  Class SizeMonotonicOptE {A} (g : E (option A)) :=
    monotonicOpt : forall s1 s2,
      s1 <= s2 ->
      semEnumSizeOpt g s1 \subset semEnumSizeOpt g s2.
  
  (** Enumerators monotonic in the runtime size parameter *)
  Class SizeAntiMonotonicNone {A} (g : E (option A)) :=
    monotonicNone : forall s1 s2,
      s1 <= s2 ->
      isNone :&: semEnumSize g s2 \subset isNone :&: semEnumSize g s1.
  
  (* CH: Why does Unsized need a _ when A is marked as implict! *)
  Parameter unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semEnumSize g s <--> semEnum g.

  (* begin unsizedMonotonic *)
  Declare Instance unsizedMonotonic : forall {A} (g : G A), Unsized g -> SizeMonotonic g.
  (* end unsizedMonotonic *)
  

  (** *  Semantics of combinators *)
  
  Parameter semReturn :
    forall A (x : A), semEnum (returnEnum x) <--> [set x].
  Parameter semReturnSize :
    forall A (x : A) size, semEnumSize (returnEnum x) size <--> [set x].
  
  Declare Instance unsizedReturn {A} (x : A) : Unsized (returnEnum x).
  Declare Instance returnEnumSizeMonotonic {A} (x : A) : SizeMonotonic (returnEnum x).
  Declare Instance returnEnumSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnEnum x).

  Parameter semBindSize :
    forall A B (g : G A) (f : A -> G B) (size : nat),
      semEnumSize (bindEnum g f) size <-->
                 \bigcup_(a in semEnumSize g size) semEnumSize (f a) size.

  Parameter semBindSize_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G B),
      (forall s, semEnumSize g s \subset semEnumSize g' s) ->
      (forall x s, semEnumSize (f x) s \subset semEnumSize (f' x) s) ->
      (forall s, semEnumSize (bindEnum g f) s \subset semEnumSize (bindEnum g' f') s).

  Parameter semBindSizeOpt_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G (option B)),
      (forall s, semEnumSize g s \subset semEnumSize g' s) ->
      (forall x s, isSome :&: semEnumSize (f x) s \subset isSome :&: semEnumSize (f' x) s) ->
      (forall s, isSome :&: semEnumSize (bindEnum g f) s \subset isSome :&: semEnumSize (bindEnum g' f') s) .

  Parameter monad_leftid : 
    forall {A B : Type} (a: A) (f : A -> G B),
      semEnum (bindEnum (returnEnum a) f) <--> semEnum (f a).
  Parameter monad_rightid : 
    forall {A : Type} (g : G A),
      semEnum (bindEnum g returnEnum) <--> semEnum g.
  Parameter monad_assoc: 
    forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
      semEnum (bindEnum (bindEnum ga fb) fc) <--> 
             semEnum (bindEnum ga (fun a => bindEnum (fb a) fc)).
  
  (* I'm not sure how this universal quantifier will behave *)
  (* begin bindUnsized *)
  Declare Instance bindUnsized {A B} (g : G A) (f : A -> G B)
          `{Unsized _ g} `{forall x, Unsized (f x)} : Unsized (bindEnum g f).
  (* end bindUnsized *)

  (* XXX these will always succeed and they have the same priority *)
  Declare Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindEnum g f).

  Declare Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindEnum g f).

  Declare Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, semEnum g x -> SizeMonotonic (f x)} : 
    SizeMonotonic (bindEnum g f).

  Declare Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semEnum g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindEnum g f).
  
  Parameter semBindUnsized1 :
    forall A B (g : G A) (f : A -> G B) `{Unsized _ g},
      semEnum (bindEnum g f) <--> \bigcup_(a in semEnum g) semEnum (f a).
  
  Parameter semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B) `{forall a, Unsized (f a)},
      semEnum (bindEnum g f) <--> \bigcup_(a in semEnum g) semEnum (f a).
  
  Parameter semBindSizeMonotonic :
  forall {A B} (g : G A) (f : A -> G B)
         `{SizeMonotonic _ g} `{forall a, SizeMonotonic (f a)},
    semEnum (bindEnum g f) <--> \bigcup_(a in semEnum g) semEnum (f a).

  Parameter semBindSizeMonotonicIncl_r :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semEnum g \subset s1 ->
      (forall x, semEnum (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semEnum (bindEnum g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].

  Parameter semBindSizeMonotonicIncl_l :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (fs : A -> set B) 
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonicOpt (f a)},
    s1 \subset semEnum g ->
    (forall x, Some @: (fs x) \subset semEnum (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semEnum (bindEnum g f).

  Parameter semFmap :
    forall A B (f : A -> B) (g : G A),
      semEnum (fmap f g) <--> f @: semEnum g.

  Parameter semFmapSize :
    forall A B (f : A -> B) (g : G A) (size : nat),
      semEnumSize (fmap f g) size <--> f @: semEnumSize g size.

  Declare Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} : 
    Unsized (fmap f g).

  Declare Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).

  Parameter semChoose :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      (semEnum (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Parameter semChooseSize :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      forall size, (semEnumSize (choose (a1,a2)) size <-->
              [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Declare Instance chooseUnsized A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).

  Parameter semSized :
    forall A (f : nat -> G A),
      semEnum (sized f) <--> \bigcup_s semEnumSize (f s) s.

  Parameter semSizedSize :
    forall A (f : nat -> G A) s,
      semEnumSize (sized f) s <--> semEnumSize (f s) s.

  (* TODO change name *)

  Parameter semSized_alt :
    forall A (f : nat -> G A) `{forall n, SizeMonotonic (f n)},
      (forall n m s,  n <= m -> semEnumSize (f n) s \subset semEnumSize (f m) s) ->
      semEnum (sized f) <--> \bigcup_n (semEnum (f n)).

  Parameter semSized_opt :
    forall A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f),
      isSome :&: semEnum (sized f) <--> isSome :&: \bigcup_n (semEnum (f n)).

  Declare Instance sizedSizeMonotonic
          A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).

  Declare Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  
  Parameter semResize :
    forall A (n : nat) (g : G A),
      semEnum (resize n g) <--> semEnumSize g n.

  Parameter semSizeResize :
    forall A (s n : nat) (g : G A),
      semEnumSize (resize n g) s <--> semEnumSize g n.

  Declare Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).

  (* This (very concrete) spec is needed to prove shrinking *)
  Parameter semPromote :
    forall A (m : Rose (G A)),
      semEnum (promote m) <-->
      codom2 (fun size seed => fmapRose (fun g => run g size seed) m).

  Parameter semPromoteSize :
    forall (A : Type) (m : Rose (G A)) n,
      semEnumSize (promote m) n <-->
      (fun t : Rose A =>
         exists (seed : RandomSeed),
           fmapRose (fun g : G A => run g n seed) m = t).

  (* Those are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete. *)

  Parameter runFmap :
    forall (A B : Type) (f : A -> B) (g : G A) seed size,
      run (fmap f g) seed size = f (run g seed size).

  Parameter runPromote :
    forall A (m : Rose (G A)) seed size,
      run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  
  Parameter semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semEnum (fmap f1 (bindEnum g f2)) <-->
      semEnum (bindEnum g (fun x => fmap f1 (f2 x))).

  Instance Functor_G : Functor G := {
    fmap A B := fmap;
  }.

  Instance Applicative_G : Applicative G := {
    pure A := returnEnum;
    ap A B := apEnum;
  }.

  Instance Monad_G : Monad G := {
    ret A := returnEnum;
    bind A B := bindEnum;
  }.

  (** Delay evaluation of a generator in a CBV language. *)
  Parameter thunkEnum : forall {A}, (unit -> G A) -> G A.

  (** [thunkEnum] doesn't change semantics. *)
  Parameter semThunkEnumSize : forall A (f : unit -> G A) s,
      semEnumSize (thunkEnum f) s <--> semEnumSize (f tt) s.

  Parameter semThunkEnum : forall A (f : unit -> G A),
      semEnum (thunkEnum f) <--> semEnum (f tt).

  Declare Instance thunkEnumUnsized {A} (f : unit -> G A)
          `{Unsized _ (f tt)} : Unsized (thunkEnum f).

  Declare Instance thunkEnumSizeMonotonic {A} (f : unit -> G A)
          `{SizeMonotonic _ (f tt)} : SizeMonotonic (thunkEnum f).

  Declare Instance thunkEnumSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{SizeMonotonicOpt _ (f tt)} : SizeMonotonicOpt (thunkEnum f).

  Declare Instance thunkEnumSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{SizeAntiMonotonicNone _ (f tt)} : SizeAntiMonotonicNone (thunkEnum f).

  (** A notation around [thunkEnum] for convenience. *)
  Notation etaG g := (thunkEnum (fun _ => g)).

End Sig.
