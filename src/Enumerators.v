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

Definition failEnum {A : Type} : E A :=
  MkEnum (fun _ => lnil).

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

(* This should use urns! *)
Fixpoint pickDrop {A : Type}  (xs : list (E (option A))) n : E (option A) * list (E (option A)) :=
  match xs with
    | nil => (ret None, nil)
    | x :: xs =>
      match n with
      | O => (x, xs)
      | S n' => let '(x', xs') := pickDrop xs n' in
                (x', x::xs')
      end
  end.

Fixpoint enumerateFuel {A : Type} (fuel : nat) (tot : nat) (gs : list (E (option A))) : E (option A) :=
  match fuel with 
    | O => ret None
    | S fuel' =>
      bind (choose (0, tot-1)) (fun n => 
      let '(g, gs') := pickDrop gs n in
      bind g (fun ma =>
                match ma with 
                | Some a => ret (Some a)
                | None => enumerateFuel fuel' (tot - 1) gs'
                 end ))
  end.

Definition enumerate' {A : Type} (gs : list (E (option A))) : E (option A) :=
  enumerateFuel (length gs) (length gs) gs.

Definition enumerate {A : Type} (gs : list (E (option A))) : E (option A) :=
  MkEnum (fun s => join_list_lazy_list (map (fun g => run g s) gs)).

Lemma enumerate_correct_size {A} (lst : list (E (option A))) s :
  isSome :&: semProdSize (enumerate lst) s <--> \bigcup_(x in lst) (fun g => isSome :&: semProdSize g s) x.
Admitted.
(*
Proof.
  unfold enumerate.
  assert (Hret := @semReturnSize E _ _ (option A)).
  assert (Hbind := @semBindSize E _ _). simpl in *. 
  
  assert (Datatypes.length lst = Datatypes.length lst)%coq_nat by reflexivity.  
  revert H.
  generalize (Datatypes.length lst) at 2 3 4.
  intros n. generalize lst. induction n; intros l Hleq.
  - simpl. intros x; split; intros Hin.  inv Hin. 
    + eapply Hret in H0. inv H0; exfalso; eauto. 
    + inv Hin. inv H. destruct l; try (simpl in *; congruence). inv H0.
  - intros x; split; intros Hin.
    + inv Hin. destruct x; [ | now exfalso; eauto ].
      with_strategy opaque [Enumerators.pickDrop] (simpl in H0). 
      
      eapply Hbind in H0.
      inv H0. inv H1.
      
      eapply Enumerators.semChooseSize in H2; eauto. simpl in *.
      
      destruct (pickDrop_exists l x). simpl in *. now ssromega.
      destruct H1. destruct H4. destruct H4. destruct H6. destruct H7.
      
      rewrite H4 in H3.
      
      eapply Hbind in H3.
      destruct H2. destruct H3. destruct H2.
      destruct x2.
      
      
      -- eapply Hret in H3.
         inv H3.
         
         eexists. split.  eassumption.
         constructor; eauto.
         
      -- assert (Hsem : (isSome :&: semProdSize
                                (enumerateFuel n (n.+1 - 1)
                                               x1) s) (Some a)).
         { split; eauto. }
         
         assert (Heq' : (n.+1 - 1) = n).
         { ssromega. }
         
         rewrite Heq' in Hsem.
         eapply IHn in Hsem.
         inv Hsem. destruct H9.
         eexists. split.
         eapply H8. eassumption. 
         eassumption.
         ssromega. 
    + inv Hin. inv H. inv H1. destruct x; try (now exfalso; eauto).
      constructor. now eauto.
      simpl. 
      eapply Hbind.
      
      destruct (pickDrop_In _ _ H0). destruct H4.
      destruct H4.
      
      exists x. split.
      eapply Enumerators.semChooseSize; eauto.
      simpl. now ssromega. 

      rewrite H4.
      eapply Hbind.

      exists (Some a). split.
      eassumption.
      eapply Hret. reflexivity. 
Qed.       
*)
Lemma enumerate_correct {A} (lst : list (E (option A))) :
  isSome :&: semProd (enumerate lst) <--> \bigcup_(x in lst) (fun g => isSome :&: semProd g) x.
Admitted.
(*
Proof.
  split; intros H.
  - inv H. inv H1. inv H2.
    assert (Hin : (isSome :&: semProdSize (enumerate lst) x) a).
    { split; eauto. }
    eapply (@enumerate_correct_size A) in Hin.
    inv Hin. inv H5. inv H7.
    eexists. split; eauto. split; eauto.
    eexists; eauto.
  - destruct H. destruct H. destruct H0. destruct H1. destruct H1.
    assert (Hin :  (\bigcup_(x in lst) (fun g => isSome :&: semProdSize g x0) x) a).
    { eexists. split; eauto. split; eauto. }

    eapply (@enumerate_correct_size A) in Hin.
    inv Hin. split; eauto. eexists. split; eauto. 
Qed.    *)


Lemma enumerate_correct_size_opt {A} (lst : list (E (option A))) s :
  semProdSizeOpt (enumerate lst) s <--> \bigcup_(x in lst) (semProdSizeOpt x s).
Admitted.
(*
Proof.
  assert (Hc := enumerate_correct_size lst s).
  intros x. destruct (Hc (Some x)) as [H1 H2].
  split.
  - intros Hin. simpl in *.

    assert (Hin' : ((fun u : option A => u) :&: semEnumSize (enumerate lst) s) (Some x)).
    { split; eauto. }
    
    eapply Hc in Hin'. destruct Hin'. inv H. inv H3.
    eexists. split; eauto.

  - intros Hin. simpl in *.
    
    assert (Hin' : (\bigcup_(x in lst) ((fun u : option A => u) :&: semEnumSize x s)) (Some x)).
    { inv Hin. inv H. eexists; split; eauto. split; eauto. }
    
    eapply Hc in Hin'. destruct Hin'. eassumption.
Qed.       *)

Lemma enumerate_correct_opt {A} (lst : list (E (option A))) :
  semProdOpt (enumerate lst) <--> \bigcup_(x in lst) (semProdOpt x).
  Admitted.
(*
Proof.
  split; intros H.
  - inv H. inv H0.
    assert (Hin : semProdSizeOpt (enumerate lst) x a).
    { eassumption. }
    eapply (@enumerate_correct_size_opt A) in Hin.
    inv Hin. inv H3.
    eexists. split; eauto. eexists. split; eauto.
  - destruct H. destruct H. destruct H0. destruct H0.
    assert (Hin :  (\bigcup_(x in lst) (semProdSizeOpt x x0)) a).
    { eexists. split; eauto. }
    eapply (@enumerate_correct_size_opt A) in Hin.
    eexists. split; eauto. 
Qed.        *)



Lemma enumerate_SizeMonotonicOpt (A : Type) (l : list (E (option A))) :
  l \subset SizeMonotonicOpt ->
  SizeMonotonicOpt (enumerate l).
Admitted.
(*
Proof.
  intros Hin. intros s1 s2 Hleq.
  rewrite !enumerate_correct_size_opt.
  intros x Hin'.  destruct Hin' as [e [Hl Hs]].
  eexists. split; eauto. eapply Hin; eauto. 
Qed.*)

Lemma enumerate_SizeMonotonic (A : Type) (l : list (E (option A))) :
  l \subset SizeMonotonic ->
  SizeMonotonic (enumerate l).
Admitted.
(*
Proof.
  unfold enumerate. 
  assert (Datatypes.length l = Datatypes.length l)%coq_nat by reflexivity.  
  revert H.
  generalize (Datatypes.length l) at 2 3 4.
  intros n. revert l. induction n; intros l Heq Hsub.
  - simpl. now eauto with typeclass_instances.
  - simpl.
    eapply bindMonotonicStrong; eauto with typeclass_instances.
    
    intros x1 Hin. eapply Enumerators.semChoose in Hin; eauto. simpl in *. 
    
    destruct (Enumerators.pickDrop_exists l x1). simpl in *. now ssromega.
    destruct H. destruct H. destruct H0. destruct H1.

    rewrite H.

    eapply bindMonotonicStrong; eauto with typeclass_instances.
    
    intros a Hin'.

    destruct a; eauto with typeclass_instances. 

    eapply returnGenSizeMonotonic; eauto with typeclass_instances.

    assert (Heq' : (n.+1 - 1) = n). { ssromega. }

    rewrite Heq'. eapply IHn. 

    now ssromega.

    eapply subset_trans. eassumption. eassumption.
Qed.
*)

Fixpoint lazylist_backtrack {A} (l : LazyList A) (f : A -> option bool) (anyNone : bool) : option bool :=
  match l with
  | lnil  => if anyNone then None else Some false
  | lcons x xs =>
    match f x with
    | Some true  => Some true
    | Some false => lazylist_backtrack (xs tt) f anyNone
    | None       => lazylist_backtrack (xs tt) f true
    end
  end.

Definition enumerating {A} (g : E A) (f : A -> option bool) (n : nat) : option bool :=
  lazylist_backtrack (run g n) f false.

Fixpoint lazylist_backtrack_opt {A} (l : LazyList (option A)) (f : A -> option bool) (anyNone : bool) : option bool :=
  match l with
  | lnil  => if anyNone then None else Some false
  | lcons mx xs =>
    match mx with
    | Some x =>
      match f x with
      | Some true  => Some true
      | Some false => lazylist_backtrack_opt (xs tt) f anyNone
      | None       => lazylist_backtrack_opt (xs tt) f true
      end
    | None => lazylist_backtrack_opt (xs tt) f anyNone
    end
  end.

Definition enumeratingOpt {A} (g : E (option A)) (f : A -> option bool) (n : nat) : option bool :=
  lazylist_backtrack_opt (run g n) f false.

Lemma enumerating_sound A (e : E A) ch s :
  enumerating e ch s = Some true ->
  exists x, ch x = Some true.
Proof.
  unfold enumerating.
  generalize (Enumerators.run e s), false.
  induction l; intros b Heq; simpl in *.
  - destruct b; congruence.
  - destruct (ch a) as [ [| ] | ] eqn:Heq'; eauto.
Qed.    

