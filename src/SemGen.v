Require Import ZArith List ssreflect ssrbool ssrnat eqtype.
Require Import Axioms RoseTrees Random Gen.
Import ListNotations.

Set Implicit Arguments.

(* Set of outcomes semantics for generators *)
Require Import Ensembles.

Definition semSize {A : Type} (g : Gen A) (size : nat) : Ensemble A :=
  fun a => exists seed, (unGen g) seed size = a.

Definition semGen {A : Type} (g : Gen A) : Ensemble A :=
  fun a => exists size, semSize g size a.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Ensemble A) :=
  forall (a : A), m1 a <-> m2 a.
 
(* CH: was trying to get rewriting of <--> to work,
   but so far I didn't manage; it would be nice to make this work;
   ask Maxime? *)
(* ZP: There is a relevant conversation at CoqClub mailing list *)

Section Rel.

Variable A : Type.

Require Import RelationClasses.

Lemma set_eq_refl : Reflexive (@set_eq A).
Admitted.

Lemma set_eq_sym : Symmetric (@set_eq A).
Admitted.

Lemma set_eq_trans : Transitive (@set_eq A).
Admitted.

Global Instance set_eq_equiv : Equivalence (@set_eq A).
Proof. split; [apply set_eq_refl | apply set_eq_sym | apply set_eq_trans]. Qed.

Require Import Morphisms.

Global Instance app_Proper (a : A) :
  Proper (set_eq ==> iff) (fun x => x a).
Proof. intros s1 s2. by rewrite /set_eq. Qed.

End Rel.

Infix "<-->" := set_eq (at level 70, no associativity) : sem_gen_scope.

(* the set f outcomes m1 is a subset of m2 *)
Definition set_incl {A} (m1 m2 : Ensemble A) :=
  forall A, m1 A -> m2 A.

Infix "--->" := set_incl (at level 70, no associativity) : sem_gen_scope.

Open Scope sem_gen_scope.

Lemma semReturnSize : forall A (x : A) (size : nat),
  semSize (returnGen x) size <--> eq x.
Proof.
  move => A x a. rewrite /semSize. split.
  - move => [seed H]. by [].
  - move => H /=. rewrite H.
    exists randomSeedInhabitant. reflexivity.
Qed.

Lemma semReturn : forall A (x : A),
  semGen (returnGen x) <--> eq x.
Proof. (* this kind of proof should be "trivial by rewriting",
          but this doesn't quite work as easy at it should *)
  move => A x. rewrite /semGen.
  (* was hoping to do the rest by rewriting: setoid_rewrite semReturnSize. *)
  pose proof (semReturnSize x) as G. unfold set_eq in G.
  (* setoid_rewrite G. -- failed constraints *)
  move => a /=. split.
  - move => [size H]. (* or rewrite -> G in H. exact H. *)
    rewrite <- G. exact H.
  - move => H. exists 0. by rewrite G.
Qed.





(* For cardinality reasons this requires RandomGen to be infinite;
   this is just an abstraction of what's happening at the lower levels *)
Axiom rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).
 
Lemma semBindSize : forall A B (g : Gen A) (f : A -> Gen B) (size : nat),
  semSize (bindGen g f) size <-->
  fun b => exists a, (semSize g size) a /\
                     (semSize (f a) size) b.
Proof.
  move => A B [g] f size b. rewrite /semSize /bindGen => /=. split.
  - case => [seed H]. move : H.
    case (rndSplit seed) => [seed1 seed2] H.
    exists (g seed1 size). split; eexists. reflexivity.
    rewrite <- H. case (f (g seed1 size)). reflexivity.
  - move => [a [[seed1 H1] [seed2 H2]]].
    case (rndSplitAssumption seed1 seed2) => [seed Hseed].
    exists seed. rewrite Hseed. rewrite H1. move : H2. by case (f a).
Qed.

 
Lemma semBind : forall A B (g : Gen A) (f : A -> Gen B),
  semGen (bindGen g f) --->
  fun b => exists a, (semGen g) a /\
                     (semGen (f a)) b.
Proof.
  move => A B [g] f b [size [seed H]]. rewrite /semSize /bindGen => /=.  
  simpl in *.
  destruct (rndSplit seed) as [seed1 seed2]. 
  subst. exists (g seed1 size).
  split. by exists size; exists seed1. 
  exists size. exists seed2. by case: (f (g seed1 size)).
Qed.

Lemma semBindComb : 
  forall A B (g : Gen A) (f : A -> Gen B),
    (fun b => exists a n, (semSize g n) a /\
                        (semSize (f a) n) b) --->
  semGen (bindGen g f).
Proof.
  move => A B [g] f b [a [n [[seed1 /= H1] [seed2 H2]]]].
  exists n.
  case (rndSplitAssumption seed1 seed2) => [seed Hseed].
  exists seed. simpl. rewrite Hseed. rewrite H1. 
  by destruct (f a). 
Qed.
  
  

Lemma semFMapSize : forall A B (f : A -> B) (g : Gen A) (size : nat),
  semSize (fmap f g) size <-->
    (fun b => exists a, (semSize g size) a /\ b = f a).
Proof.
  move => A B f [g] size b. rewrite /semSize /fmap => /=. split.
  - move => [seed H]. exists (g seed size). by eauto.
  - move => [a [[seed H1] H2]].
    eexists. rewrite H2. rewrite <- H1. reflexivity.
Qed.

(* This should just use semFMapSize *)
Lemma semFMap : forall A B (f : A -> B) (g : Gen A),
  semGen (fmap f g) <-->
    (fun b => exists a, (semGen g) a /\ b = f a).
Proof.
  move => A B f [g] b. rewrite /semGen /semSize /fmap => /=. split.
  - move => [size [seed H]]. exists (g seed size). by eauto.
  - move => [a [[size [seed H1]] H2]].
    do 2 eexists. rewrite H2. rewrite <- H1. reflexivity.
Qed.

Lemma semChooseSize : forall A `{Random A} a1 a2 s,
  semSize (choose (a1,a2)) s <--> (fun a => Random.leq a1 a /\ Random.leq a a2).
Proof.
  move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
  - move => [seed H]. apply randomRCorrect. by exists seed.
  - by move => /randomRCorrect H.
Qed.  

Lemma semChoose : forall A `{Random A} a1 a2,
  semGen (choose (a1,a2)) <--> (fun a => Random.leq a1 a /\ Random.leq a a2).
Proof.
  move => A R a1 a2 a. rewrite /semGen /semSize. simpl. split.
  - by move => [_ /randomRCorrect H].
  - move => /randomRCorrect H. by exists 0.
Qed.  

Lemma semSizedSize : forall A (f : nat -> Gen A),
  semGen (sized f) <--> (fun a => exists n, semSize (f n) n a).
Proof.
  move => A f a. rewrite /semGen /semSize /sized => /=. split.
  - move => [size [seed H]]. exists size. move : H.
    case (f size) => g H. rewrite /semSize. by eauto.
  - move => [size [seed H]]. exists size. exists seed.
    move : H. case (f size) => g H. rewrite /semSize. by eauto.
Qed.


Lemma semResize : forall A (n : nat) (g : Gen A),
  semGen (resize n g) <--> semSize g n .
Proof.
  move => A n [g] a. rewrite /semGen /semSize /resize => /=. split.
  - move => [_ [seed H]]. by eauto.
  - move => [seed H]. exists 0. by eauto.
Qed.

Lemma semGenSuchThatMaybeAux_sound:
  forall {A} g p k n (a : A) seed size,
    unGen (suchThatMaybeAux g p k n) seed size = Some a ->
    (exists size seed, (unGen g) seed size = a) /\ p a.
Proof. 
  move=> /= A g p k n. elim : n k =>  [//=| n IHn] k a seed size H.
  simpl in *. unfold unGen, bindGen in H.
  remember (resize (2 * k + n.+1) g) as g'.
  case: g' H Heqg'=> /= g' H Heqg'.
  case: (rndSplit seed) H Heqg'=> /= r1 r2 H Heqg'. 
  remember (p (g' r1 size)) as b.
  case: b H Heqb => /= H Heqb. inversion H; subst.
  rewrite /resize in Heqg'.
  destruct g as [g]. inversion Heqg'; subst.
  split =>  //=. by eexists; eexists.
  eapply (IHn k.+1 a r2 size). rewrite -H.
  by destruct (suchThatMaybeAux g p k.+1 n).
Qed.
   
Lemma semSuchThatMaybe : forall A (g : Gen A) (f : A -> bool),
  semGen (suchThatMaybeG g f) --->
         (fun o => o = None \/
                   (exists y, o = Some y /\ semGen g y /\ f y)).
(* Not an exact spec !!! *)
Proof.  
  move => A g f a. rewrite /semGen /semSize. 
  - case : a => [a|] [n [s H]]; last by left. right.
    eexists; split=> //=.
    remember (match n with
                 | 0 => 1
                 | m'.+1 => m'.+1
               end) as n'.  
    apply (semGenSuchThatMaybeAux_sound g f 0 n' s n). rewrite -H /= -Heqn'.
    by destruct (suchThatMaybeAux g f 0 n').
Qed.
      

(* This is trivial, just the definition *)
Lemma semPromote : forall A (m : Rose (Gen A)),
  semGen (promote m) <--> 
         fun (t : (Rose A)) => 
           exists seed size, 
              (fmapRose (fun (g : Gen A) => unGen g seed size) m) = t.
Proof.  
  move => A rg r. split; 
  move => [size [seed H]]; exists seed; exists size=> //=. 
Qed.

(* Semantics for derived generators *)

Lemma semliftGen :
  forall {A B} (f: A -> B) (g: Gen A),
    semGen (liftGen f g) <-->
      fun b =>
      exists a, semGen g a /\ f a = b.
Proof. 
  rewrite /liftGen. move => A B f g b. split.
  - move => [size /semBindSize [a [H1 H2]]]; subst.
    exists a. apply semReturnSize in H2. 
    split => //. by exists size.
  - move => [a [[size H] Heq]]; subst.
    exists size. apply semBindSize.
    exists a. split => //. by apply semReturnSize.
Qed.


Lemma semSize_semGen: 
  forall {A} (g: Gen A) n, semSize g n ---> semGen g.
Proof.
  move => A g n a H. by exists n.
Qed.

Lemma sequenceGen_equiv :
  forall {A} (gs : list (Gen A)) n,
    semSize (sequenceGen gs) n <--> 
           fun l => length l = length gs /\
                    forall x, List.In x (combine l gs) -> 
                              semSize (snd x) n (fst x).
Proof.
  move=> A gs n la. rewrite /sequenceGen. split.
  - elim : gs la => /= [| g gs IHgs] la.
    + by move/semReturnSize => H; subst. 
    + move => /semBindSize [a [H1 /semBindSize 
                                  [la' [H2 /semReturnSize H3]]]]; subst.
      move: IHgs => /(_ la' H2) [<- HIn].
      split=> //= x [H | H]; subst => //=. by apply HIn => /=.
  - elim : gs la => /= [| g gs IHgs].
    + move => [|a la] [//= Heq H]. 
      by apply semReturnSize. 
    + move => [|a la] [//= [Heq] HIn]; subst.
      apply semBindSize. 
      exists a. split. 
      * apply (HIn (a, g)). by left.
      * apply semBindSize. exists la. 
        split => //=.
        apply IHgs. split => // x H. apply HIn; by right.
        by apply semReturnSize.
Qed.  

Lemma vectorOf_equiv: 
  forall {A : Type} (k : nat) (g : Gen A) n,
    semSize (vectorOf k g) n <--> 
    fun l => (length l = k /\ forall x, List.In x l -> semSize g n x).
Proof.
  move => A k g n la; unfold vectorOf; split.
  - elim : k la => /= [|k IHk] la.  
    + move=> /semReturnSize H; subst. by split.
    + move=> /semBindSize [a [H1 /semBindSize [la' [H2 /semReturnSize H3]]]].
      subst => /=. 
      have [<- HIn]: length la' = k /\ (forall x : A, List.In x la' -> semSize g n x)
        by apply IHk. 
      split => // x [H | H]; subst => //. 
      by apply HIn.
  - elim : k la => /= [|k IHk] la [Heq Hgen]. 
    + destruct la => //. by apply semReturnSize.
    + destruct la=> //. simpl in *.
      move: Heq => [Heq]; subst.
      apply semBindSize.
      exists a. split.
      * apply Hgen => //; by left.
      * apply semBindSize.
        exists la =>//. split => //; last by apply semReturnSize.  
        apply IHk. split => //.
        move => x HIn. apply Hgen. by right.
Qed.
 

Lemma In_nth_exists:
  forall {A} (l: list A) x def,
    List.In x l -> exists n, nth n l def = x /\ (n < length l)%coq_nat.
Proof.
   move => A l x def. elim : l => [| a l IHl]  //=. 
   move => [H | /IHl [n [H1 H2]]]; subst.
   - exists 0. split => //. omega.
   - exists n.+1. split => //. omega.
Qed.
  
Lemma oneof_equiv:
  forall {A} (l : list (Gen A)) (def : Gen A),
    (semGen (oneof def l)) <-->
    (fun e => (exists x, List.In x l /\ semGen x e) \/ 
              (l = nil /\ semGen def e)).
Proof.
  move=> A l def a. unfold oneof. split.
  - move => [s /semBindSize [n [/semChooseSize [Hleq1 Hleq2] Hnth]]]. 
    case: l Hleq2 Hnth => [| g gs] //= /leP Hleq2 Hnth.
    + rewrite sub0n in Hleq2. apply le_n_0_eq in Hleq2; subst. 
      right. split => //. by exists s.
    + left. rewrite subn1 NPeano.Nat.pred_succ in Hleq2.  
      case: n Hleq1 Hleq2 Hnth => [_ _ | n Hleq1 Hleq2] Hnth.
      * exists g. split; auto. by exists s.
      * exists (nth n gs def). split; last by exists s.
        right. by apply nth_In.
  - move => [[g [Hin [s Hsem]]] | [Heq [s Hsem]]]; subst.
    + exists s. apply semBindSize.  
      destruct (In_nth_exists _ _ def Hin) as [n [Hnth Hl]]; subst.
      exists n. split => //. apply semChooseSize. split => //.
      simpl. apply/leP.
      rewrite subn1. apply NPeano.Nat.le_succ_le_pred. omega.
    + exists s. apply semBindSize. exists 0. split => //.
      apply semChooseSize. split => //.
Qed.

Lemma elements_equiv :
  forall {A} (l: list A) (def : A),
    (semGen (elements def l)) <--> (fun e => List.In e l \/ (l = nil /\ e = def)).
Proof.
 unfold elements. move => A l def a. split.
 - move => [s /semBindSize [n [/semChooseSize [/= Hleq1 Hleq2] 
                                /semReturnSize H2]]]; subst.
   case: l Hleq1 Hleq2 => [_ _ | a l /= Hleq1 Hleq2]. 
   + right. split => //. by case: n.
   + left. case: n Hleq1 Hleq2 => [|n] _ /leP Hleq2; auto.
     right. apply nth_In. rewrite subn1 in Hleq2. omega.
 - move => [H | [H1 H2]]; subst.
   + exists 0. apply semBindSize. 
     destruct (In_nth_exists _ _ def H) as [n [Hnth Hlen]]; subst.
     exists n. split; last by apply semReturnSize.
     apply semChooseSize. split => //. apply/leP. 
     unfold lt in *. rewrite subn1. omega.
   + exists 0. apply semBindSize. exists 0.
     split; last by apply semReturnSize. apply semChooseSize. split => //. 
Qed.

(* A proof that shrinking doesn't affect the semantics of testing *)
(* This should move to the appropriate file, once we propagate the changes *)

Require Import Checker.

Definition shrinking {prop A : Type} {_: @Checkable Gen.Gen prop}
           (shrinker : A -> list A) (x0 : A) (pf : A -> prop) : Checker Gen :=
  fmap (fun x => MkProp (joinRose (fmapRose unProp x)))
        (promote (props pf shrinker x0)).

Definition resultSuccessful (r : Result) : bool :=
  match r with
    | MkResult (Some res) expected _ _ _ _ =>
      res == expected
    | _ => true
  end.

Definition success qp :=
  match qp with
    | MkProp (MkRose res _) => resultSuccessful res
  end.

(* Maps a Checker to a Prop *)
Definition semChecker (P : Checker Gen) : Prop :=
  forall qp, semGen P qp -> success qp = true.

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)
Definition semCheckable {A : Type} {_ : Checkable  A} (a : A) : Prop :=
  semChecker (checker a).

Lemma semShrinking_id:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop),
    semChecker (shrinking shrinker x0 pf) <->
    semCheckable (pf x0).
Proof.
  move => prop A HCheck sh x pf. unfold semCheckable, shrinking, semChecker.
  split. 
  - unfold props. generalize 1000. case => [| n] H qp [size [seed Hgen]]; subst.
    + apply H. exists size. exists seed. simpl.
      by destruct (checker (pf x)) as [[[res [l]]]] => /=.
    + suff :
        success
          (unGen
             (fmap
                (fun x0 => {| unProp := joinRose (fmapRose unProp x0) |})
                (promote (@props' _ _ _ HCheck n.+1 pf sh x))) seed size) = true;
      first by simpl; destruct (unGen (checker (pf x)) seed size) as [[? ?]].
      by apply H; exists size; exists seed.
  - unfold props. generalize 1000.  
    move => n H qp /semFMap [rqp [/semPromote /= [seed [size H2]] H']]; subst.
    case: n H => [| n] /(_  (unGen (checker (pf x)) seed size)) /= H;
    suff : success (unGen (@checker _ _ HCheck (pf x)) seed size) = true;
    try (by destruct (unGen (checker (pf x)) seed size) as [[res l]]);
    apply H; by exists size; exists seed.
Qed.
