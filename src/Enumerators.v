Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     Sets Tactics Producer LazyList RandomQC.

Set Bullet Behavior "Strict Subproofs".

Inductive EnumType (A:Type) : Type :=
  MkEnum : (nat -> LazyList A) -> EnumType A.
Arguments MkEnum {A}.
  
Definition E := EnumType.

(** * Primitive generator combinators *)
  
Definition run {A : Type} (g : E A) :=
  match g with MkEnum f => f end.
  
Definition returnEnum {A : Type} (x : A) : E A :=
  MkEnum (fun _ => retLazyList x).

Definition bindEnum {A B : Type} (g : E A) (k : A -> E B) : E B :=
  MkEnum (fun n =>
            x <- run g n;;
            run (k x) n).

Instance MonadEnum : Monad E :=
  { ret := @returnEnum
  ; bind := @bindEnum }.

Definition sizedEnum {A : Type} (f : nat -> E A) : E A :=
  MkEnum (fun n => run (f n) n).

Definition resizeEnum {A : Type} (n : nat) (g : E A) : E A :=
    match g with
    | MkEnum m => MkEnum (fun _ => m n)
    end.

Definition semEnumSize {A : Type} (g : E A) (s : nat) : set A := fun x => In_ll x (run g s).

Definition chooseEnum {A : Type} `{ChoosableFromInterval A} (range : A * A) : E A :=
    MkEnum (fun _ => enumR range). 

Definition sampleEnum (A : Type) (g : E A) : list A :=
  LazyList_to_list (run g 5).

Program Instance ProducerEnum : Producer E :=
  {
  super := MonadEnum;

  sample := sampleEnum;
  
  sized  := @sizedEnum; 
  resize := @resizeEnum;

  choose := @chooseEnum;
  
  semProdSize := @semEnumSize;

  (* Probably belongs in another class for modularity? *)
  bindPf :=
    fun {A B : Type} (g : E A)
        (k : forall (a : A),
            (fun (A : Type) (g : E A) =>
               \bigcup_(size in [set: nat]) semEnumSize g size) A g a -> E B) =>
      MkEnum (fun n => _)
  }.
Next Obligation.
  remember (run g n) as l.
  refine (bindLazyListPf l _) => x In.
  rewrite /semEnumSize /E in k.
  specialize (k x).
  assert ((\bigcup_(size in [set: nat]) In_ll^~ (run g size)) x).
  { 
    exists n; split; unfold setT; auto.
    rewrite -Heql; auto.
  }     
  specialize (k H).
  inversion k.
  apply (X n).
Defined.

(* begin semReturn *)
Lemma semReturnEnum {A} (x : A) : semProd (ret x) <--> [set x].
(* end semReturn *)
Proof.
  rewrite /semProd /semProdSize /= /semEnumSize /=
  bigcup_const ?codom_const //.
  - split; auto.
    + intros [Eq | Contra]; [subst; reflexivity | inversion Contra].
  - do 2! constructor.
Qed.
  
Lemma semReturnSizeEnum A (x : A) (s : nat) :
  semProdSize (ret x) s <--> [set x].
Proof.
  rewrite /semProdSize /= /semEnumSize.
  simpl; split; auto.
  move => [Eq | []]; subst; reflexivity.
Qed.

Lemma semBindSizeEnum A B (g : E A) (f : A -> E B) (s : nat) :
    semEnumSize (bindEnum g f) s <-->
    \bigcup_(a in semEnumSize g s) semEnumSize (f a) s.
Proof.
  rewrite /semEnumSize /bindEnum /=.
Admitted.

Lemma semChooseSize A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semProdSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
Proof.
  move=> /= le_a1a2 m n //=;
  rewrite (enumRCorrect n a1 a2) //=.
Qed.
  
Instance chooseUnsized {A} `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
Proof. by []. Qed.
  
Lemma semChoose A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
Proof.
  move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
  move => m /=. rewrite (enumRCorrect m a1 a2) //.
Qed.


Lemma semChooseEnum A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
Proof.
  move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
  move => m /=. rewrite (enumRCorrect m a1 a2) //.
Qed.
  
Lemma semChooseSizeEnum A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semEnumSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
Proof. by move=> /= le_a1a2 m n; rewrite (enumRCorrect n a1 a2). Qed.

Lemma  semChooseSizeEmptyEnum :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      ~ (RandomQC.leq a1 a2) ->
      forall size, (semProdSize (choose (a1,a2)) size <-->
                                set0).
Admitted.  


Lemma semSizedEnum A (f : nat -> E A) :
    semProd (sized f) <--> \bigcup_n semEnumSize (f n) n.
Proof. by []. Qed.

Lemma semSizedSizeEnum A (f:nat->E A) s : semEnumSize (sized f) s <--> semEnumSize (f s) s.
Proof. by []. Qed.

Lemma semResizeEnum A n (g : E A) : semProd (resize n g) <--> semEnumSize g n .
Proof.
   by case: g => g; rewrite /semProd /semProdSize /= /semEnumSize /= bigcup_const.
Qed.

Lemma semResizeSizeEnum A (s n : nat) (g : E A) :
    semEnumSize (resize n g) s <--> semEnumSize g n.
Proof. by case: g => g; rewrite /semEnumSize. Qed.

Instance ProducerSemanticsEnum :
  @ProducerSemantics E ProducerEnum :=
  {
  semReturn     := @semReturnEnum; 
  semReturnSize := @semReturnSizeEnum;
  semBindSize   := @semBindSizeEnum;
  semChoose     := @semChooseEnum;
  semChooseSize := @semChooseSizeEnum;
  semChooseSizeEmpty := @semChooseSizeEmptyEnum;
  semSized      := @semSizedEnum;
  semSizedSize  := @semSizedSizeEnum;
  semResize     := @semResizeEnum;
  semResizeSize := @semResizeSizeEnum
  }.
