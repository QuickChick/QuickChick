Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import String List ZArith Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype seq.

(*From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
*)
(* Import MonadNotation.
Open Scope monad_scope.
*)
From QuickChick Require Import
     RandomQC RoseTrees Sets Tactics Producer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Inductive GenType (A:Type) : Type := MkGen : (nat -> RandomSeed -> A) -> GenType A.
  
Definition G := GenType.

(** * Primitive generator combinators *)
  
Definition run {A : Type} (g : G A) := match g with MkGen f => f end.
  
Definition returnGen {A : Type} (x : A) : G A :=
  MkGen (fun _ _ => x).

Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B :=
  MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1)) n r2).

Instance MonadGen : Monad G :=
  { ret := @returnGen
  ; bind := @bindGen }.

Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => List.rev (cons O acc)
  | S n' => createRange n' (cons n acc)
  end.

Fixpoint rnds (s : RandomSeed) (n' : nat) : list RandomSeed :=
    match n' with
      | O => nil
      | S n'' =>
        let (s1, s2) := randomSplit s in
        cons s1 (rnds s2 n'')
    end.

Definition sampleGen (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.

Definition sizedGen {A : Type} (f : nat -> G A) : G A :=
  MkGen (fun n r => run (f n) n r).

Definition resizeGen {A : Type} (n : nat) (g : G A) : G A :=
    match g with
    | MkGen m => MkGen (fun _ => m n)
    end.

Definition semGenSize {A : Type} (g : G A) (s : nat) : set A := codom (run g s).

Definition chooseGen {A : Type} `{ChoosableFromInterval A} (range : A * A) : G A :=
    MkGen (fun _ r => fst (randomR range r)).

Program Instance ProducerGen : Producer G :=
  {
  super := MonadGen;

  sample := sampleGen;
  
  sized  := @sizedGen; 
  resize := @resizeGen;

  choose := @chooseGen;
  
  semProdSize := @semGenSize;

  (* Probably belongs in another class for modularity? *)
  bindPf :=
    fun {A B : Type} (g : G A)
        (k : forall (a : A),
            (fun (A : Type) (g : G A) =>
               \bigcup_(size in [set: nat]) semGenSize g size) A g a -> G B) =>
    MkGen (fun n r =>
             let (r1,r2) := randomSplit r in
             run (k (run g n r1) _) n r2)}.
Next Obligation.
  unfold semGenSize, codom, bigcup.
  exists n; split => //=.
  exists r1; auto.
Defined.

(* Generator specific sample of a single input. *)
Definition sample1 (A : Type) (g : G A) : A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        m 10 rnd
    end.

Lemma runFmap (A B : Type) (f : A -> B) (g : G A) seed size :
    run (fmap f g) size seed = f (run g size (fst (randomSplit seed))).
Proof. simpl.
       destruct (randomSplit seed).
       simpl.
       auto.
Qed.

(* Generator specific - shrinking support. *)
Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun n r => fmapRose (fun g => run g n r) m).

(* Generator specific - coarbitrary support. *)
Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.
  
Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n g => (match g with MkGen f => f r n end)).
  
Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).

Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a =
      run g size (varySeed (f a) r1).
Proof.
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
Qed.

Lemma semPromote A (m : Rose (G A)) :
    semProd (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
Proof. by rewrite /codom2 curry_codom2l. Qed.

Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semProdSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
Proof. by []. Qed.

Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
Proof. by []. Qed.


(* Generator specific - choose and its semantics. *)
Lemma semChooseSize A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semProdSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.
  
Instance chooseUnsized {A} `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
Proof. by []. Qed.
  
Lemma semChoose A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
Proof.
  move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
  move => m /=. rewrite (randomRCorrect m a1 a2) //.
Qed.

  Definition thunkGen {A} (f : unit -> G A) : G A :=
    MkGen (fun n r => run (f tt) n r).

  Lemma semThunkGenSize {A} (f : unit -> G A) s :
    semProdSize (thunkGen f) s <--> semProdSize (f tt) s.
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Lemma semThunkGen {A} (f : unit -> G A) :
    semProd (thunkGen f) <--> semProd (f tt).
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Instance thunkGenUnsized {A} (f : unit -> G A)
          `{@Unsized _ _ ProducerGen (f tt)} : Unsized (thunkGen f).
  Proof.
    intros s1 s2.
    do 2 rewrite semThunkGenSize.
    apply unsized.
  Qed.

  Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{@SizeMonotonic _ _ ProducerGen (f tt)} : SizeMonotonic (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonic.
  Qed.

  Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{@SizeMonotonicOpt _ _ ProducerGen (f tt)} : SizeMonotonicOpt (thunkGen f).
  Proof.
    intros s1 s2 Hs. unfold semProdSizeOpt.
    do 2 rewrite semThunkGenSize.
    by apply monotonicOpt.
  Qed.

  Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{@SizeAntiMonotonicNone _ _ ProducerGen (f tt)} : SizeAntiMonotonicNone (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonicNone.
  Qed.

Fixpoint pick {A : Type} (def : G A) (xs : list (nat * G A)) n : nat * G A :=
  match xs with
    | nil => (0, def)
    | (k, x) :: xs =>
      if (n < k) then (k, x)
      else pick def xs (n - k)
  end.

(* This should use urns! *)
Fixpoint pickDrop {A : Type} (xs : list (nat * G (option A))) n : nat * G (option A) * list (nat * G (option A)) :=
  match xs with
    | nil => (0, ret None, nil)
    | (k, x) :: xs =>
      if (n < k) then  (k, x, xs)
      else let '(k', x', xs') := pickDrop xs (n - k)
           in (k', x', (k,x)::xs')
  end. 

Definition sum_fst {A : Type} (gs : list (nat * A)) : nat :=
  foldl (fun t p => t + (fst p)) 0 gs.

Definition freq_ {A : Type} (def : G A) (gs : list (nat * G A))
: G A :=
  let tot := sum_fst gs in
  bindGen (choose (0, tot-1)) (fun n =>
  @snd _ _ (pick def gs n)).

(*
Definition frequency {A}:= 
  @deprecate (G A -> list (nat * G A) -> G A) "frequency" "freq_" freq_.
 *)

Fixpoint backtrackFuel {A : Type} (fuel : nat) (tot : nat) (gs : list (nat * G (option A))) : G (option A) :=
  match fuel with 
    | O => ret None
    | S fuel' => bindGen (choose (0, tot-1)) (fun n => 
                 let '(k, g, gs') := pickDrop gs n in
                 bindGen g (fun ma =>
                 match ma with 
                   | Some a => ret (Some a)
                   | None => backtrackFuel fuel' (tot - k) gs'
                 end ))
  end.

Definition backtrack {A : Type} (gs : list (nat * G (option A))) : G (option A) :=
  backtrackFuel (length gs) (sum_fst gs) gs.

Definition retryBody {A : Type}
           (retry : nat -> G (option A) -> G (option A))
           (n : nat) (g : G (option A)) : G (option A) :=
  bindGen g (fun x =>
               match x, n with
               | Some a, _ => returnGen (Some a)
               | None, O => returnGen None
               | None, S n' => retry n' g
               end).

(* Rerun a generator [g] until it returns a [Some], or stop after
     [n+1] tries. *)
Fixpoint retry {A : Type} (n : nat) (g : G (option A)) :
  G (option A) :=
  retryBody retry n g.

(* Filter the output of a generator [g], returning [None] when the
     predicate [p] is [false]. The generator is run once. *)
Definition suchThatMaybe1 {A : Type} (g : G A) (p : A -> bool) :
  G (option A) :=
  fmap (fun x => if p x then Some x else None) g.

(* Retry a generator [g : G A] until it returns a value satisfying
     the predicate, or stop after [size+1] times, where [size] is the
     current size value. *)
Definition suchThatMaybe {A : Type} (g : G A) (p : A -> bool) :
  G (option A) :=
  sized (fun n => retry n (suchThatMaybe1 g p)).

(* Retry a generator [g : G (option A)] until it returns a value
     satisfying the predicate, or stop after [size+1] times, where
     [size] is the current size value. *)
Definition suchThatMaybeOpt {A : Type} (g : G (option A))
           (p : A -> bool) : G (option A) :=
  sized (fun n => retry n (fmap (fun x =>
                                   match x with
                                   | None => None
                                   | Some a => if p a then Some a else None
                                   end) g)).

(* Retry a generator until it returns a value, or stop after
     [size+1] times. *)
Definition retrySized {A : Type} (g : G (option A)) : G (option A) :=
  sized (fun n => retry n g).

(* begin semReturn *)
Lemma semReturnGen {A} (x : A) : semProd (ret x) <--> [set x].
(* end semReturn *)
Proof.
  rewrite /semProd /semProdSize /= /semGenSize /=
  bigcup_const ?codom_const //.
  exact: randomSeed_inhabited.
    by do 2! constructor.
Qed.
  
Lemma semReturnSizeGen A (x : A) (s : nat) :
  semProdSize (ret x) s <--> [set x].
Proof.
  rewrite /semProdSize /= /semGenSize.
  rewrite codom_const; [ reflexivity | apply randomSeed_inhabited ].
Qed.

Lemma randomSplit_codom : codom randomSplit <--> setT.
Proof.
by apply/subset_eqP; split=> // [[s1 s2]] _; apply: randomSplitAssumption.
Qed.


Lemma semBindSizeGen A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
    \bigcup_(a in semGenSize g s) semGenSize (f a) s.
Proof.
    rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
    by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
Qed.

Lemma semChooseGen A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semProd (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
Proof.
  move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
  move => m /=. rewrite (randomRCorrect m a1 a2) //.
Qed.

  
Lemma semChooseSizeGen A `{ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
Proof. by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed.

Lemma  semChooseSizeEmptyGen :
    forall A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A),
      ~ (RandomQC.leq a1 a2) ->
      forall size, (semProdSize (choose (a1,a2)) size <-->
                                set0).
Admitted.  


Lemma semSizedGen A (f : nat -> G A) :
    semProd (sized f) <--> \bigcup_n semGenSize (f n) n.
Proof. by []. Qed.

Lemma semSizedSizeGen A (f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
Proof. by []. Qed.

Lemma semResizeGen A n (g : G A) : semProd (resize n g) <--> semGenSize g n .
Proof.
   by case: g => g; rewrite /semProd /semProdSize /= /semGenSize /= bigcup_const.
Qed.

Lemma semResizeSizeGen A (s n : nat) (g : G A) :
    semGenSize (resize n g) s <--> semGenSize g n.
Proof. by case: g => g; rewrite /semGenSize. Qed.

Global Instance ProducerSemanticsGen :
  @ProducerSemantics G ProducerGen :=
  {
  semReturn     := @semReturnGen; 
  semReturnSize := @semReturnSizeGen;
  semBindSize   := @semBindSizeGen;
  semChoose     := @semChooseGen;
  semChooseSize := @semChooseSizeGen;
  semChooseSizeEmpty := @semChooseSizeEmptyGen;
  semSized      := @semSizedGen;
  semSizedSize  := @semSizedSizeGen;
  semResize     := @semResizeGen;
  semResizeSize := @semResizeSizeGen
  }.

Module QcDefaultNotation.

Declare Scope qc_scope.

Notation " 'elems' [ x ] " := (elems_ x (cons x nil)) : qc_scope.
Notation " 'elems' [ x ; y ] " := (elems_ x (cons x (cons y nil))) : qc_scope.
Notation " 'elems' [ x ; y ; .. ; z ] " :=
  (elems_ x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'elems' ( x ;; l ) " :=
  (elems_ x (cons x l)) (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' [ x ] " := (oneOf_ x (cons x nil)) : qc_scope.
Notation " 'oneOf' [ x ; y ] " := (oneOf_ x (cons x (cons y nil))) : qc_scope.
Notation " 'oneOf' [ x ; y ; .. ; z ] " :=
  (oneOf_ x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'oneOf' ( x ;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'freq' [ x ] " := (freq_ x nil) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ] " :=
  (freq_ x (cons (n, x) (cons y nil))) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ; .. ; z ] " :=
  (freq_ x (cons (n, x) (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'freq' ( ( n , x ) ;; l ) " :=
  (freq_ x (cons (n, x) l)) (at level 1, no associativity) : qc_scope.

End QcDefaultNotation.

Section FrequencyProof.
(* A rather long frequency proof, probably we can do better *)

Lemma not_lt : forall n m, (false = (n < m)) -> (m <= n).
Proof.
  move => n m. by elim: n m=> [| n IHn]; case.
Qed.

Lemma sum_fstE A x (a : A) l:
  sum_fst ((x, a) :: l) = x + sum_fst l.
Proof.
rewrite /sum_fst /=.
elim: l 0 x => [n x|[n1 x1] l IHl p q] /=; first by rewrite addnC.
by rewrite -IHl; congr foldl; rewrite addnAC.
Qed.

Lemma sum_fst_eq0P {A} (l : list (nat * A)) :
  sum_fst l = 0 <->
  [seq x <- l | x.1 != 0] = [::].  
Proof.
by elim: l => [|[[|n] x] l IHl] //=; split=> //; rewrite sum_fstE.
Qed.

Lemma pick_def :
  forall {A} (l: list (nat * G A)) n def,
    sum_fst l <= n ->
    pick def l n = (0, def).
Proof.
  move=> A l n def Hleq.
  elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
  rewrite sum_fstE in Hleq.
  remember (n < i). case: b Heqb => Heqb; symmetry in Heqb.
  - have : (i + sum_fst l) < i by eapply (leq_ltn_trans); eassumption.
    rewrite -ltn_subRL. by have -> : forall i, (i - i) = 0 by elim.
  - apply IHl. rewrite -(leq_add2r i) subnK.
      by rewrite addnC. by apply/not_lt.
Qed.

Lemma pick_exists :
  forall {A} (l: list (nat * G A)) n def,
    n <  sum_fst l <->
    exists x, List.In x l /\ pick def l n = x /\ fst x <> 0.
Proof.
  move => A l n def. split.
  - move => Hlt.
    elim : l n Hlt => //. case => i p xs IHxs n Hlt.
    rewrite sum_fstE in Hlt.
    move/(_ (n-i)) : IHxs => IHxs. simpl.
    remember (n < i). case: b Heqb => [Heqb | /not_lt Heqb].
    + exists (i, p). split => //=. by left.  split => //=.
      move => contra; subst. by rewrite ltn0 in Heqb.
    + rewrite -(ltn_add2r i) [X in _  < X]addnC subnK // in IHxs.
      move/(_ Hlt) : IHxs => [x [H1 [H2 H3]]].
      by exists x; split; [right | split].
  - move => [x [HIn [Hpick Hneq]]].
    remember (n < sum_fst l).
    case: b  Heqb => //= /not_lt/pick_def H.
    rewrite H in Hpick. rewrite -Hpick //= in Hneq.
Qed.

Lemma pick_In :
  forall {A} (l: list (nat * G A)) x def,
    List.In x l /\ fst x <> 0 ->
    exists n, pick def l n = x.
Proof.
  move => A l x def [HIn Hfst].
  elim : l HIn => //=. case => //= i g xs IHxs [H1 | H2]; subst.
  + exists 0. simpl in *.
    have H : 0 < i by  elim : i Hfst IHxs => //=.
    rewrite H.
      by split => //=.
  + move/(_ H2) : IHxs => [n Hpick].
    exists (n + i). rewrite -[X in _ < X]add0n ltn_add2r ltn0.
      by rewrite  -[X in _ - X]add0n subnDr subn0.
Qed.

Lemma pick_imset A (def : G A) l :
  pick def l @: [set m | m < sum_fst l] <--> [seq x <- l | x.1 != 0]. 
Proof.
elim: l => [|[n x] l IHl] /=.
  rewrite /sum_fst /=.
  have->: (fun m => m < 0) <--> set0 by [].
  by rewrite imset0.
case: n => /= [|n].
  rewrite -IHl => t; split=> [[y []]|].
    by rewrite sum_fstE add0n subn0 => lt_y <-; exists y.
  by case=> y [lt_y <-]; exists y; split=> //; rewrite subn0.
move=> t; split=> /= [[p [lt_p]]|].
  case: ifP => [_ <-|lt_pn ?]; first by left.
    right; rewrite -(IHl t); exists (p - n.+1); split=> //.
  rewrite sum_fstE in lt_p.
  by rewrite -(ltn_add2r n.+1) subnK 1?addnC // leqNgt lt_pn.
case=> [<-|]; first by exists 0; split => //; rewrite sum_fstE.
rewrite -(IHl t); case=> p [lt_p <-]; exists (n.+1 + p); split.
  by rewrite sum_fstE ltn_add2l.
by rewrite ltnNge leq_addr addKn.
Qed.

Lemma pickDrop_def :
  forall {A} (l: list (nat * G (option A))) n,
    sum_fst l <= n ->
    pickDrop l n = (0, ret None, l).
Proof.
  move=> A l n Hleq.
  elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
  rewrite sum_fstE in Hleq.
  remember (n < i). case: b Heqb => Heqb; symmetry in Heqb.
  - have : (i + sum_fst l) < i by eapply (leq_ltn_trans); eassumption.
    rewrite -ltn_subRL. by have -> : forall i, (i - i) = 0 by elim.
  - rewrite IHl; auto. rewrite -(leq_add2r i) subnK.
      by rewrite addnC. by apply/not_lt.
Qed.

(* Probably needs something about l' and l. *)
Lemma pickDrop_exists :
  forall {A} (l: list (nat * G (option A))) n,
    n <  sum_fst l <->
    exists k g l',
      List.In (k,g) l /\ pickDrop l n = (k,g,l') /\ k <> 0 /\
      l <--> [set (k, g)] :|: l' /\
      length l' + 1 = length l /\
      sum_fst l' + k = sum_fst l.
Proof.
  move => A l n. split.
  - move => Hlt.
    elim : l n Hlt => //. case => i p xs IHxs n Hlt.
    rewrite sum_fstE in Hlt.
    move/(_ (n-i)) : IHxs => IHxs. simpl.
    remember (n < i). case: b Heqb => [Heqb | /not_lt Heqb].
    + exists i. exists p. exists xs. split => //=. by left.  split => //=.
      split. move => contra; subst. by rewrite ltn0 in Heqb.
      split. by rewrite cons_set_eq.
      split. by ssromega.
      rewrite sum_fstE. by ssromega.
    + rewrite -(ltn_add2r i) [X in _  < X]addnC subnK // in IHxs.
      move/(_ Hlt) : IHxs => [k [g [gs [H1 [H2 [H3 [H4 [H5 H6]]]]]]]].
      exists k. exists g. exists ((i,p)::gs).
      split; [right | split; [| split; [| split; [| split]]]];
      try (simpl; eauto; by rewrite H2).
      rewrite !cons_set_eq H4.
      rewrite setU_assoc (setU_comm [set (i, p)]) -setU_assoc.
      reflexivity.
      simpl. by ssromega.
      simpl. rewrite !sum_fstE. by ssromega.
  - move => [k [g [gs [HIn [Hpick [Hneq _]]]]]].
    remember (n < sum_fst l).
    case: b  Heqb => //= /not_lt/pickDrop_def H.
    rewrite H in Hpick. 
    inversion Hpick; subst; eauto.
Qed.

Lemma pickDrop_In :
  forall {A} (l: list (nat * G (option A))) k x,
    List.In (k,x) l /\ k <> 0 ->
    exists n l', pickDrop l n = (k,x,l').
Proof.
  move => A l k x [HIn Hfst].
  elim : l HIn => //=. case => //= i g xs IHxs [H1 | H2]; subst.
  + exists 0.  exists xs. simpl in *.
    inversion H1; subst; clear H1.
    have H : 0 < k by  elim : k Hfst IHxs => //=.
    rewrite H.
      by split => //=.
  + move/(_ H2) : IHxs => [n [l' Hpick]].
    exists (n + i). exists ((i,g)::l'). 
    rewrite -[X in _ < X]add0n ltn_add2r ltn0.
    rewrite  -[X in _ - X]add0n subnDr subn0.
    by rewrite Hpick.
Qed.

Lemma pickDrop_In_strong :
  forall {A} (l: list (nat * G (option A))) k x,
    List.In (k,x) l /\ k <> 0 ->
    exists n l',
      pickDrop l n = (k,x,l') /\
      n < sum_fst l /\
      length l = length l' + 1.
Proof.
  move => A l k x [HIn Hfst].
  elim : l HIn => //=. case => //= i g xs IHxs [H1 | H2]; subst.
  + exists 0.  exists xs. simpl in *.
    inversion H1; subst; clear H1.
    have H : 0 < k by  elim : k Hfst IHxs => //=.
    rewrite H. split ; [| split ]; simpl; auto.
    rewrite sum_fstE. now ssromega.
    now ssromega.
  + move/(_ H2) : IHxs => [n [l' [Hpick [Hlt Hlen]]]].
    exists (n + i). exists ((i,g)::l'). 
    rewrite -[X in _ < X]add0n ltn_add2r ltn0.
    rewrite  -[X in _ - X]add0n subnDr subn0.
    rewrite Hpick. simpl.
    split ; [| split ]; simpl; auto.
    rewrite sum_fstE. now ssromega.
    now ssromega.
Qed.

(* begin semFrequencySize *)
Lemma semFrequencySize {A}
      (l : list (nat * G A)) (def : G A) (size: nat) :
  semProdSize (freq_ def l) size <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semProdSize def size else
      \bigcup_(x in l') semProdSize x.2 size.
(* end semFrequencySize *)
Proof.
rewrite semBindSize semChooseSize //=.
case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs].
move/sum_fst_eq0P: lsupp => suml; rewrite suml.
  rewrite (@eq_bigcupl _ _ _ [set 0]) ?bigcup_set1 ?pick_def // ?leqn0 ?suml //.
  by move=> n; split; rewrite leqn0; [move/eqP|] => ->.
symmetry; apply: reindex_bigcup.
have pos_suml: 0 < sum_fst l.
  have [] := sum_fst_eq0P l.
  by rewrite lsupp; case: (sum_fst l) => // /(_ erefl).
have->: (fun a : nat => a <= sum_fst l - 1) <--> [set m | m < sum_fst l].
  by move=> m /=; rewrite -ltnS subn1 prednK.
exact: pick_imset.
Qed.

(* begin semFrequency *)
Lemma semFrequency {A} (l : list (nat * G A)) (def : G A) :
  semProd (freq_ def l) <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semProd def else
      \bigcup_(x in l') semProd x.2.
(* end semFrequency *)
Proof.
by case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs] /=;
rewrite 1?bigcupC; apply: eq_bigcupr => sz;
have := (semFrequencySize l def sz); rewrite lsupp.
Qed.

Lemma frequencySizeMonotonic {A} (g0 : G A) lg :
  SizeMonotonic g0 ->
  List.Forall (fun p => SizeMonotonic (snd p)) lg ->
  SizeMonotonic (freq_ g0 lg).
Proof.
  intros H1.  unfold freq_.
  intros Hall. eapply bindMonotonicStrong.
  - eauto with typeclass_instances.
  - apply unsizedMonotonic.
    apply chooseUnsized.
  - intros x Heq. eapply semChoose in Heq; eauto.  
  move : Heq => /andP [Hep1 Heq2]. 
  destruct (sum_fst lg) eqn:Heq.
  + rewrite pick_def. eassumption.
    subst. ssromega.
  + edestruct (pick_exists lg x g0) as [[[n' g] [Hin [Hp Hg]]] H2].
    rewrite Heq. unfold leq, RandomQC.super, ChooseNat, OrdNat in Hep1, Heq2.
    ssromega.
    eapply List.Forall_forall in Hall; [ | ].
    eassumption.
    subst. rewrite Hp. eassumption.
Qed.

Instance frequencySizeMonotonic_alt :
  forall {A : Type} (g0 : G A) (lg : seq (nat * G A)),
    SizeMonotonic g0 ->
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (freq_ g0 lg).
Proof.
  intros A g ls Hm Hin.
  eapply frequencySizeMonotonic. eassumption.
  induction ls. now constructor.
  constructor. eapply Hin.
  constructor. reflexivity.
  eapply IHls.  eapply subset_trans; eauto.
  constructor 2. eassumption.
Qed.

End FrequencyProof.  
  
(* Backwards compatibility. *)
Definition elements := @elems_ G ProducerGen.
Definition liftGen := @liftM G (@super _ ProducerGen).
Definition liftGen2 := @liftM2 G (@super _ ProducerGen).
Definition liftGen3 := @liftM3 G (@super _ ProducerGen).
Definition liftGen4 := @liftProd4 _ ProducerGen.
Definition liftGen5 := @liftProd5 _ ProducerGen.
Definition sequenceGen := @sequenceProd G ProducerGen.
Definition oneof := @oneOf_ G ProducerGen.
Definition frequency := @freq_.
Definition semGen := @semProd G ProducerGen.
