Require Import ZArith List ssreflect ssrfun ssrbool ssrnat.
Require Import Random RoseTrees.
Require Import Sets.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Lemma randomSplit_codom : codom randomSplit <--> setT.
Proof.
by apply/subset_eqP; split=> // [[s1 s2]] _; apply: randomSplitAssumption.
Qed.

(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)
Module Type GenLowInterface.
Parameter G : Type -> Type.

(* Standard (primitive) generator interface *)
Parameter returnGen  : forall {A : Type}, A -> G A.
Parameter bindGen :  forall {A B : Type}, G A -> (A -> G B) -> G B.
Parameter run  : forall {A : Type}, G A -> nat -> RandomSeed -> A.
Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
Parameter sized : forall {A: Type}, (nat -> G A) -> G A.
Parameter resize : forall {A: Type}, nat -> G A -> G A.
Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A).
Parameter suchThatMaybe : forall {A : Type}, G A -> (A -> bool) ->
                                             G (option A).
Parameter choose : forall {A : Type} `{Random A}, (A * A) -> G A.
Parameter sample : forall {A : Type}, G A -> list A.


(* LL: The abstraction barrier is annoying :D *)
Parameter variant : forall {A : Type}, SplitPath -> G A -> G A.
Parameter reallyUnsafePromote : forall {r A:Type}, (r -> G A) -> G (r -> A).

Hypothesis promoteVariant : forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size 
                            (r r1 r2 : RandomSeed),
  randomSplit r = (r1,r2) ->                              
  run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
  run g size (varySeed (f a) r1).

(* Set of outcomes semantics definitions (repeated below) *)
Definition semGenSize {A : Type} (g : G A) (size : nat) : set A :=
  codom (run g size).
Definition semGen {A : Type} (g : G A) : set A :=
  \bigcup_size semGenSize g size.

(* Definitions for size characterization of generators *)
Definition sizeMonotonic {A : Type} (g : G A) : Prop :=
  forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2.

Definition unsized {A : Type} (g : G A) : Prop :=
  forall s1 s2, (semGenSize g s1 <--> semGenSize g s2).

Hypothesis unsizedSizeMonotonic : 
  forall {A} (g : G A), unsized g -> sizeMonotonic g.

Hypothesis unsized_def2 : 
  forall A (g : G A),
    unsized g ->
    forall s, semGenSize g s <--> semGen g.

(* Set of outcomes characterization of generators *)
Hypothesis semReturn :
  forall A (x : A), semGen (returnGen x) <--> [set x].
Hypothesis semReturnSize :
  forall A (x : A) size, semGenSize (returnGen x) size <--> [set x].
Hypothesis unsizedReturn :
  forall A (x : A) , unsized (returnGen x).

Hypothesis semBindSize :
  forall A B (g : G A) (f : A -> G B) (size : nat),
    semGenSize (bindGen g f) size <-->
               \bigcup_(a in semGenSize g size) semGenSize (f a) size.

Hypothesis monad_leftid : 
  forall {A B : Type} (a: A) (f : A -> G B),
    semGen (bindGen (returnGen a) f) <--> semGen (f a).
Hypothesis monad_rightid : 
  forall {A : Type} (g : G A),
    semGen (bindGen g returnGen) <--> semGen g.
Hypothesis monad_assoc: 
  forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
    semGen (bindGen (bindGen ga fb) fc) <--> 
    semGen (bindGen ga (fun a => bindGen (fb a) fc)).


Hypothesis semBindUnsized1 :
  forall A B (g : G A) (f : A -> G B),
    unsized g ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

Hypothesis semBindUnsized2 :
  forall A B (g : G A) (f : A -> G B),
    (forall a, unsized (f a)) ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

Hypothesis semBindSizeMonotonic :
  forall {A B} (g : G A) (f : A -> G B),
    sizeMonotonic g ->
    (forall a, sizeMonotonic (f a)) ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

Hypothesis semFmap :
  forall A B (f : A -> B) (g : G A),
    semGen (fmap f g) <--> f @: semGen g.
Hypothesis semFmapSize :
  forall A B (f : A -> B) (g : G A) (size : nat),
    semGenSize (fmap f g) size <--> f @: semGenSize g size.


Hypothesis semChoose :
  forall A `{Random A} (a1 a2 : A), Random.leq a1 a2 ->
    (semGen (choose (a1,a2)) <-->
    [set a | Random.leq a1 a && Random.leq a a2]).

Hypothesis semChooseSize :
  forall A `{Random A} (a1 a2 : A), Random.leq a1 a2 ->
    forall size, (semGenSize (choose (a1,a2)) size <-->
    [set a | Random.leq a1 a && Random.leq a a2]).

Hypothesis semSized :
  forall A (f : nat -> G A),
    semGen (sized f) <--> \bigcup_s semGenSize (f s) s.

Hypothesis semSizedSize :
  forall A (f : nat -> G A) s,
    semGenSize (sized f) s <--> semGenSize (f s) s.

Hypothesis semResize :
  forall A (n : nat) (g : G A),
    semGen (resize n g) <--> semGenSize g n.
Hypothesis unsizedResize :
  forall A n (g : G A) , unsized (resize n g).

(* TODO: We need completeness as well - this is not exact *)
Hypothesis semSuchThatMaybe_sound:
  forall A (g : G A) (f : A -> bool),
    semGen (suchThatMaybe g f) \subset
    None |: some @: (semGen g :&: f).

(* This (very concrete) spec is needed to prove shrinking *)
Hypothesis semPromote : forall A (m : Rose (G A)),
  semGen (promote m) <-->
  codom2 (fun size seed => fmapRose (fun g => run g size seed) m).

Hypothesis semPromoteSize :
  forall (A : Type) (m : Rose (G A)) n,
    semGenSize (promote m) n <-->
    (fun t : Rose A =>
       exists (seed : RandomSeed),
         fmapRose (fun g : G A => run g n seed) m = t).

(* Those are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete. *)

Hypothesis runFmap : forall (A B : Type) (f : A -> B) (g : G A) seed size,
  run (fmap f g) seed size = f (run g seed size).
  
Hypothesis runPromote : forall A (m : Rose (G A)) seed size,
  run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.

Hypothesis semFmapBind :
  forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
    semGen (fmap f1 (bindGen g f2)) <-->
    semGen (bindGen g (fun x => fmap f1 (f2 x))).

End GenLowInterface.

Module GenLow : GenLowInterface.

(* begin GenType *)
Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> A) -> GenType A.
(* end GenType *)

Definition G := GenType.

(* begin run *)
Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
(* end run *)

Definition returnGen {A : Type} (x : A) : G A :=
  MkGen (fun _ _ => x).

Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
  MkGen (fun n r =>
           let (r1,r2) := randomSplit r in
            run (k (run g n r1)) n r2).

Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
  MkGen (fun n r => f (run g n r)).

Definition sized {A : Type} (f : nat -> G A) : G A :=
  MkGen (fun n r => run (f n) n r).

Definition resize {A : Type} (n : nat) (g : G A) : G A :=
  match g with
    | MkGen m => MkGen (fun _ => m n)
  end.

Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
  MkGen (fun n r => fmapRose (fun g => run g n r) m).

(* ZP: Split suchThatMaybe into two different functions
     to make a proof easier *)
Definition suchThatMaybeAux {A : Type} (g : G A) (p : A -> bool) :=
  fix aux (k : nat) (n : nat) : G (option A) :=
  match n with
    | O => returnGen None
    | S n' =>
      bindGen (resize (2 * k + n) g) (fun x =>
                                        if p x then returnGen (Some x)
                                        else aux (S k) n')
  end.

Definition suchThatMaybe {A : Type} (g : G A) (p : A -> bool)
: G (option A) :=
  sized (fun x => suchThatMaybeAux g p 0 (max 1 x)).

Fixpoint rnds (rnd : RandomSeed) (n' : nat) : list RandomSeed :=
  match n' with
    | O => nil
    | S n'' =>
      let (rnd1, rnd2) := randomSplit rnd in
      cons rnd1 (rnds rnd2 n'')
  end.

Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
  match n with
    | O => List.rev (cons O acc)
    | S n' => createRange n' (cons n acc)
  end.

Definition choose {A : Type} `{Random A} (range : A * A) : G A :=
  MkGen (fun _ r => fst (randomR range r)).

Definition sample (A : Type) (g : G A) : list A :=
  match g with
    | MkGen m =>
      let rnd := mkRandomSeed 0 in
      let l := List.combine (rnds rnd 20) (createRange 20 nil) in
      List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
  end.

(* LL : Things that need to be in GenLow because of MkGen *)

Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
  match g with 
    | MkGen f => MkGen (fun n r => f n (varySeed p r))
  end.

Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
  MkGen (fun r n g => (match g with MkGen f => f r n end)).

Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
     returnGen (fun r => eval (m r)))).

(* End Things *)

(* Set of outcomes semantics definitions (repeated above) *)
(* begin semGen *)
Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := codom (run g s).
Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.
(* end semGen *)

 
(* An important property of generators is size-monotonicity;
   sized-monotonic generators compose better *)
Definition sizeMonotonic {A : Type} (g : G A) : Prop :=
  forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2.

Definition unsized {A : Type} (g : G A) : Prop :=
  forall s1 s2, (semGenSize g s1 <--> semGenSize g s2).

(* unsizedness trivially implies size-monotonicity *)
Lemma unsizedSizeMonotonic A (g : G A) :
  unsized g -> sizeMonotonic g.
Proof.
  rewrite /unsized /sizeMonotonic => H s1 s2 H12 a.
    by destruct (H s1 s2 a) as [H1 H2].
Qed.

(* another characterization of unsized *)
Lemma unsized_def2 : forall A (g : G A),
  unsized g ->
  forall s, semGenSize g s <--> semGen g.
Proof.
  intros. unfold semGen. intros a.
  split; intros H'.
  - exists s. split; by [].
  - destruct H' as [s' [_ H']]. by rewrite (H s s' a).
Qed.

(* begin semReturnSize *)
Lemma semReturnSize A (x : A) (s : nat) : semGenSize (returnGen x) s <--> [set x].
(* end semReturnSize *)
Proof.
by rewrite /semGenSize /= codom_const //; apply: randomSeed_inhabited.
Qed.

Lemma semReturn A (x : A) : semGen (returnGen x) <--> [set x].
Proof.
rewrite /semGen /semGenSize /= bigcup_const ?codom_const //.
  exact: randomSeed_inhabited.
by do 2! constructor.
Qed.

Lemma unsizedReturn A (x : A) : unsized (returnGen x).
Proof. 
  unfold unsized. intros s1 s2 x'. by split.
Qed.


(* begin semBindSize *)
Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
  semGenSize (bindGen g f) s <--> \bigcup_(a in semGenSize g s) semGenSize (f a) s.
(* end semBindSize *)
Proof.
rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
Qed.

Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
  semGenSize (fmap f g) size <--> f @: semGenSize g size.
Proof. by rewrite /fmap /semGenSize /= codom_comp. Qed.

Lemma monad_leftid A B (a : A) (f : A -> G B) :
  semGen (bindGen (returnGen a) f) <--> semGen (f a).
Proof.
by apply: eq_bigcupr => size; rewrite semBindSize semReturnSize bigcup_set1.
Qed.

Lemma monad_rightid A (g : G A) : semGen (bindGen g returnGen) <--> semGen g.
Proof.
apply: eq_bigcupr => size; rewrite semBindSize.
by rewrite (eq_bigcupr _ (fun x => semReturnSize x size))
           /semGenSize bigcup_codom codomE.
Qed.

Lemma monad_assoc A B C (ga : G A) (fb : A -> G B) (fc : B -> G C) :
  semGen (bindGen (bindGen ga fb) fc) <--> 
  semGen (bindGen ga (fun a => bindGen (fb a) fc)).
Proof.
(* Why can't we iterate here? *)
apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
by apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
Qed.

Lemma semBindUnsized1 :
  forall A B (g : G A) (f : A -> G B),
    unsized g ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
Proof.
  move => A B g f H.
  rewrite /semGen. setoid_rewrite semBindSize. move => b; split.
  - intros [s [_ [a [H1 H2]]]].
    exists a. split; exists s; (split; first (compute; by []); first by[]).
  - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists s2. split; first (compute; by []).
    exists a. split; [| by []].
    rewrite /unsized /set_eq in H. rewrite -> H. eassumption.
Qed.  

Lemma semBindUnsized2 :
  forall A B (g : G A) (f : A -> G B),
    (forall a, unsized (f a)) ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
Proof.
  move=> A B g f H.
  rewrite /semGen. setoid_rewrite semBindSize.
  intro b. split.
  - intros [s [_ [a [H1 H2]]]].
    exists a. split; exists s; (split; first (compute; by []); first by[]).
  - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists s1. split; first (compute; by []).
    exists a. split. by []. specialize (H a).
    rewrite /unsized /set_eq in H. rewrite -> H. eassumption.
Qed.

Lemma semBindSizeMonotonic {A B} (g : G A) (f : A -> G B) :
    sizeMonotonic g ->
    (forall a, sizeMonotonic (f a)) ->
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
Proof.
  move => Hg Hf.
  rewrite /semGen. setoid_rewrite semBindSize.
  intro b. split.
  - intros [s [_ [a [H1 H2]]]].
    exists a. split; exists s; (split; first (compute; by []); first by[]).
  - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
    split; first (compute; by []).
    exists a. split.
    eapply Hg; last eassumption. by apply/leP; apply Max.le_max_l.
    eapply Hf; last eassumption. by apply/leP; apply Max.le_max_r.
Qed.


Lemma semFmap A B (f : A -> B) (g : G A) :
  semGen (fmap f g) <--> f @: semGen g.
Proof.
by rewrite imset_bigcup /semGen (eq_bigcupr _ (semFmapSize _ _)).
Qed.

Lemma semChooseSize A `{Random A} (a1 a2 : A) :
  Random.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
    [set a | Random.leq a1 a && Random.leq a a2].
Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.

Lemma semChoose A `{Random A} (a1 a2 : A) : Random.leq a1 a2 ->
  (semGen (choose (a1,a2)) <-->
  [set a | Random.leq a1 a && Random.leq a a2]).
Proof.
move=> leq_a1a2.
rewrite /semGen (eq_bigcupr _ (semChooseSize leq_a1a2)) bigcup_const //.
by do 2! constructor.
Qed.

Lemma semSized A (f : nat -> G A) :
  semGen (sized f) <--> \bigcup_n semGenSize (f n) n.
Proof. by []. Qed.

(* begin semSizedSize *)
Lemma semSizedSize A(f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
(* end semSizedSize *)
Proof. by []. Qed.

Lemma semResize A n (g : G A) : semGen (resize n g) <--> semGenSize g n .
Proof.
by case: g => g; rewrite /semGen /semGenSize /= bigcup_const.
Qed.

Lemma unsizedResize :
  forall A n (g : G A) , unsized (resize n g).
Proof.
  move=> A n g. rewrite /unsized /resize /semGenSize => s1 s2.
  destruct g; split; auto.
Qed.

Lemma semGenSuchThatMaybeAux_sound {A} : forall g p k n (a : A) size seed,
  run (suchThatMaybeAux g p k n) size seed = Some a ->
  a \in semGen g :&: p.
Proof.
case=> g p k n; elim: n k =>  [//=| n IHn] k a size seed /=.
case: (randomSplit seed) => r1 r2; case: ifP=> [/= ? [<-]|_]; last exact: IHn.
by split=> //; exists (2 * k + n.+1); split=> //; exists r1.
Qed.

(* Not an exact spec !!! *)
Lemma semSuchThatMaybe_sound A (g : G A) (f : A -> bool) :
  semGen (suchThatMaybe g f) \subset
  None |: some @: (semGen g :&: f).
Proof.
case=> [a [size [_ [x run_x]]] | ]; last by left.
by right; exists a; split=> //; apply: (semGenSuchThatMaybeAux_sound run_x).
Qed.

Lemma promoteVariant : forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
  (r r1 r2 : RandomSeed), randomSplit r = (r1, r2) ->
  run (reallyUnsafePromote (fun a => variant (f a) g)) size r a = 
  run g size (varySeed (f a) r1).
Proof. 
  move => A B a p g size r r1 r2 H.
  rewrite /reallyUnsafePromote /variant.
  destruct g. rewrite /= H. by [].
Qed.

Lemma semPromote A (m : Rose (G A)) :
  semGen (promote m) <-->
  codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
Proof. by rewrite /codom2 curry_codom2l. Qed.

Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
  semGenSize (promote m) n <-->
  codom (fun seed => fmapRose (fun g => run g n seed) m).
Proof. by []. Qed.

(* These are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete.
 *)
Lemma runFmap (A B : Type) (f : A -> B) (g : G A) seed size :
  run (fmap f g) seed size = f (run g seed size).
Proof. by []. Qed.

Lemma runPromote A (m : Rose (G A)) seed size :
  run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
Proof. by []. Qed.

Lemma semFmapBind :
  forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
    semGen (fmap f1 (bindGen g f2)) <-->
    semGen (bindGen g (fun x => fmap f1 (f2 x))).
Proof.
  intros. rewrite /semGen. setoid_rewrite semFmapSize.
  setoid_rewrite semBindSize.
  apply eq_bigcupr => s. setoid_rewrite semFmapSize.
  rewrite imset_bigcup. reflexivity.
Qed.

End GenLow.