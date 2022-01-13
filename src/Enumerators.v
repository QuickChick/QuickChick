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
  unfold bindLazyList.
  generalize (run g s).
  induction l.
  - simpl. split; intros; try contradiction.

    inv H. destruct H0. contradiction.

  - simpl in *.
    intros z; split; intros H1.
    + eapply lazy_in_app_or in H1.
      inv H1.
      * eexists. split. left. reflexivity.
        eassumption.
      * eapply H in H0. inv H0.
        destruct H2.
        eexists. split. right. eassumption.
        eassumption.
    + inv H1. destruct H0.
      inv H0.
      * eapply lazy_append_in_l. eassumption.
      * eapply lazy_append_in_r.
        eapply H. eexists. split; eauto. 
Qed. 

Global Instance bindOptSizeFP
       {A B} (g : E (option A)) (f : A -> E (option B))
       {Hsg : SizeFP g} {Hsf : forall x, SizeFP (f x)} :
  SizeFP (bindOpt g f).
Proof.
  simpl.   
  move => s1 s2 Hs Hnin.
  specialize (Hsg _ _ Hs). simpl in *.
  rewrite !semBindSizeEnum. split.
  - intros [z [Hin1 Hin2]].
    destruct z.
    + eexists. split. eapply Hsg; [ | eassumption ].
      intros Hc1.
      eapply Hnin.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eapply semReturnSizeEnum. reflexivity.
      simpl. eapply (Hsf _ _ _ Hs); [ | eassumption ].
      intros Hc1. eapply Hnin.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eassumption.
    + exfalso. eapply Hnin.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eapply semReturnSizeEnum. reflexivity.
  - intros [z [Hin1 Hin2]].
    destruct z.
    + eexists. split. eapply Hsg; [ | eassumption ].
      intros Hc1.
      eapply Hnin.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eapply semReturnSizeEnum. reflexivity.
      simpl. eapply (Hsf _ _ _ Hs); [ | eassumption ].
      intros Hc1. eapply Hnin.
      eapply semBindSizeEnum. eexists. split.
      eapply Hsg; [| eassumption ].
      intros Hc. eapply Hnin.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eapply semReturnSizeEnum. reflexivity.
      simpl. eassumption.
    + simpl in *.
      exfalso. eapply Hnin.
      eapply Hsg in Hin1.
      eapply semBindSizeEnum. eexists. split. eassumption. 
      simpl. eapply semReturnSizeEnum. reflexivity.
      intros Hc.
      eapply Hnin. 
      eapply semBindSizeEnum. eexists. split.
      eassumption. eapply semReturnSizeEnum. reflexivity.
Qed. 


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
Proof.
  intros.
  simpl. intros x; split; intros H1; try now inv H1.
  unfold semEnumSize, chooseEnum in H1.
  exfalso. simpl in *. eapply H0.
  (* This is not provable with the current spec of choose,
     but maybe is not needed *) 
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
  isSome :&: semProdSize (enumerate lst) s <-->
  \bigcup_(x in lst) (fun g => isSome :&: semProdSize g s) x.
Proof.
  unfold enumerate.
  induction lst.
  - rewrite bigcup_nil_set0. simpl. intros x; split; intros H; inv H.
    inv H1.
  - simpl in *.
    split.
    + intros H1. inv H1. unfold semEnumSize in *.
      simpl in *.
      eapply lazy_in_app_or in H0. inv H0.
      * eexists. split. now left.
        split; eassumption.
      * assert (Hin : a0 \in \bigcup_(x in lst) ((fun u : option A => u) :&: In_ll^~ (run x s))).
        { eapply IHlst. split; eassumption. }

        inv Hin. inv H3. eexists. split. right. eassumption. eassumption.
    + intros [b [H1 H2]]. inv H2. inv H1.
      * split. eassumption. simpl. unfold semEnumSize in *. simpl in *.
        eapply lazy_append_in_l. eassumption.
      * split. eassumption.
        eapply lazy_append_in_r. eapply IHlst. eexists. split; eassumption.
Qed.

Lemma enumerate_correct {A} (lst : list (E (option A))) :
  isSome :&: semProd (enumerate lst) <--> \bigcup_(x in lst) (fun g => isSome :&: semProd g) x.
Proof.
  unfold enumerate.
  induction lst.
  - rewrite bigcup_nil_set0. simpl. intros x; split; intros H; inv H.
    inv H1. inv H2. inv H4. 
  - simpl in *.
    split.
    + intros H1. inv H1. inv H0. inv H2. unfold semEnumSize in *.
      simpl in *.
      eapply lazy_in_app_or in H4. inv H4.
      * eexists. split. now left.
        split; try eassumption. eexists; split; eauto.
      * assert (Hin : a0 \in  (\bigcup_(x0 in lst) ((fun u : option A => u) :&: semProd x0))).
        { eapply IHlst. split; eauto. eexists; split; eassumption. }
        
        inv Hin. inv H6. inv H8. eexists. split. right. eassumption. eassumption.
    + intros [b [H1 H2]]. inv H2. inv H1.
      * split. eassumption. simpl. unfold semProd in *. simpl in *.
        inv H0. inv H3. eexists. split. eassumption. eapply lazy_append_in_l. eassumption.
      * assert (Hin : a0 \in ((fun u : option A => u)
                                :&: semProd (MkEnum (fun s : nat => join_list_lazy_list (map (run^~ s) lst))))).
        { eapply IHlst. eexists. split; eauto. }
        inv Hin. inv H5. inv H6.
        split; eauto. eexists; split; eauto.
        simpl. eapply lazy_append_in_r. eassumption.
Qed.


Lemma enumerate_correct_size_opt {A} (lst : list (E (option A))) s :
  semProdSizeOpt (enumerate lst) s <--> \bigcup_(x in lst) (semProdSizeOpt x s).
Proof.
  unfold enumerate.
  induction lst.
  - rewrite bigcup_nil_set0. simpl. intros x; split; intros H; inv H.
  - simpl in *.
    split.
    + intros H1. unfold semEnumSize in *.
      simpl in *.
      eapply lazy_in_app_or in H1. inv H1.
      * eexists. split. now left. eassumption. 
      * assert (Hin : a0 \in \bigcup_(x in lst) (semProdSizeOpt x s)).
        { eapply IHlst. eassumption. }
       
        inv Hin. inv H0. eexists. split. right. eassumption. eassumption.
    + intros [b [H1 H2]]. inv H1.
      * unfold semEnumSize in *. simpl in *.
        eapply lazy_append_in_l. eassumption.
      * simpl. eapply lazy_append_in_r. eapply IHlst. eexists. split; eassumption.
Qed.
  
Lemma enumerate_correct_size' {A} (lst : list (E (option A))) s :
  semProdSize (enumerate lst) s <--> \bigcup_(x in lst) (semProdSize x s).
Proof.
  unfold enumerate.
  induction lst.
  - rewrite bigcup_nil_set0. simpl. intros x; split; intros H; inv H.
  - simpl in *.
    split.
    + intros H1. unfold semEnumSize in *.
      simpl in *.
      eapply lazy_in_app_or in H1. inv H1.
      * eexists. split. now left. eassumption. 
      * assert (Hin : a0 \in \bigcup_(x in lst) (semProdSize x s)).
        { eapply IHlst. eassumption. }
       
        inv Hin. inv H0. eexists. split. right. eassumption. eassumption.
    + intros [b [H1 H2]]. inv H1.
      * unfold semEnumSize in *. simpl in *.
        eapply lazy_append_in_l. eassumption.
      * simpl. eapply lazy_append_in_r. eapply IHlst. eexists. split; eassumption.
Qed.
  

Lemma enumerate_correct_opt {A} (lst : list (E (option A))) :
  semProdOpt (enumerate lst) <--> \bigcup_(x in lst) (semProdOpt x).
Proof.
  unfold enumerate.
  induction lst.
  - rewrite bigcup_nil_set0. simpl. intros x; split; intros H; inv H; inv H0; inv H2.
  - simpl in *.
    split.
    + intros H1. unfold semEnumSize in *.
      inv H1. inv H. simpl in *. 
      eapply lazy_in_app_or in H2. inv H2.
      * eexists. split. now left. eexists. split; eassumption. 
      * assert (Hin : a0 \in \bigcup_(x in lst) (semProdOpt x)).
        { eapply IHlst. eexists. split; eassumption. }       
        inv Hin. inv H4. eexists. split. right. eassumption. eassumption.
    + intros [b [H1 H2]]. inv H1.
      * unfold semEnumSize in *. simpl in *.
        inv H2. inv H. eexists. split. reflexivity. simpl. eapply lazy_append_in_l. simpl in *. eassumption.
      * assert (Hin :  semProdOpt (MkEnum (fun s : nat =>  join_list_lazy_list (map (run^~ s) lst))) a0).
        { eapply IHlst. inv H2. inv H0. simpl. eexists. split; eauto. }
        inv Hin. inv H0.
        simpl. eexists. split. reflexivity. simpl in *. 
        eapply lazy_append_in_r. simpl in *. eassumption.
Qed.

Lemma enumerate_SizeMonotonicOpt (A : Type) (l : list (E (option A))) :
  l \subset SizeMonotonicOpt ->
  SizeMonotonicOpt (enumerate l).
Proof.
  intros Hin. intros s1 s2 Hleq.
  rewrite !enumerate_correct_size_opt.
  intros x Hin'.  destruct Hin' as [e [Hl Hs]].
  eexists. split; eauto. eapply Hin; eauto. 
Qed.

Lemma enumerate_SizeMonotonic (A : Type) (l : list (E (option A))) :
  l \subset SizeMonotonic ->
  SizeMonotonic (enumerate l).
Proof.
  intros Hin. intros s1 s2 Hleq.
  rewrite !enumerate_correct_size'.  
  intros x Hin'.  destruct Hin' as [e [Hl Hs]].
  eexists. split; eauto. eapply Hin; eauto. 
Qed.

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
    | None => lazylist_backtrack_opt (xs tt) f true
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

