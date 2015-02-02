Require Import ssreflect ssrbool eqtype.
Require Import Show GenLow GenHigh RoseTrees Checker Arbitrary.
Import GenLow GenHigh.


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
Definition semChecker (P : Checker) : Prop :=
  forall s qp, semGenSize P s qp -> success qp = true.

Definition semCheckerSize (P : Checker) (s : nat): Prop :=
  forall qp, semGenSize P s qp -> success qp = true.

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)
Definition semCheckable {A : Type} {_ : Checkable  A} (a : A) : Prop :=
  semChecker (checker a).

Definition semCheckableSize {A : Type} {_ : Checkable  A}
           (a : A) (s : nat) : Prop :=
  semCheckerSize (checker a) s.

Lemma mapTotalResult_id:
  forall {prop : Type} {H : Checkable prop} (f : Result -> Result)
         (p : prop) (s : nat),
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semCheckerSize (mapTotalResult f p) s <-> semCheckableSize p s).
Proof.
  move => prop H f p s Hyp.
  rewrite /semCheckable /mapTotalResult /mapRoseResult /mapProp /semChecker.
  split.
  - move=> H1 qp Hprop.
    set qp' :=
      match qp with
        | {| unProp := t |} => {| unProp := fmapRose f t |}
      end.
    specialize (H1 qp').
    have: success qp' = true.
    { apply H1.  apply semFmapSize. exists qp; split => //. }
    destruct qp as [[]]. simpl in *. by rewrite -Hyp.
  - move => H1 qp /semFmapSize [qp' [/H1 Hprop H2]]; subst.
    destruct qp' as [[]]. simpl in *. by rewrite -Hyp.
Qed.

Lemma semCallback_id:
  forall {prop : Type} {H : Checkable prop} (cb : Callback) (p : prop) (s : nat),
    semCheckerSize (callback cb p) s <-> semCheckableSize p s.
Proof.
  move => prop tp cb p. rewrite /callback.
  split; move => H.
  - apply mapTotalResult_id in H => //;
    by move => [? ? ? ? ? ?].
  - apply mapTotalResult_id => //;
    by move => [? ? ? ? ? ?].
Qed.

Lemma semWhenFail_id:
  forall {prop : Type} {H : Checkable prop} (s : String.string) (p : prop)
         (size : nat),
    semCheckerSize (whenFail s p) size <-> semCheckableSize p size.
Proof.
  move => prop H s p size. by rewrite /whenFail semCallback_id.
Qed.


Lemma semPrintTestCase_id:
  forall {prop: Type} {tp : Checkable prop} (s: String.string)
         (p: prop) (size : nat),
    semCheckerSize (printTestCase s p) size <-> semCheckableSize p size.
Proof.
  move => prop tp s p size. by rewrite /printTestCase semCallback_id.
Qed.


Axiom semGenSizeCorrect :
  forall A (g : G A) (x : A) size,
    semGenSize g size x <-> exists seed, run g seed size = x.


(* TODO : This proof needs refactoring! *)
Lemma semShrinking_id:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop) (s : nat),
    semCheckerSize (shrinking shrinker x0 pf) s <->
    semCheckableSize (pf x0) s.
Proof.
  move => prop A HCheck sh x pf.
  unfold semCheckableSize, shrinking, semCheckerSize.
  split.
  - unfold props. generalize 1000.
    case => [| n] H qp /semGenSizeCorrect [seed Hgen]; subst.
    + apply H. apply semFmapSize. eexists.
      split. apply semPromoteSize.
      exists seed. simpl. reflexivity.
      simpl.
      by destruct ((run (checker (pf x)) seed s)) as [[res [l]]] => /=.
    + suff :
        success
          (run
             (fmap
                (fun x0 => {| unProp := joinRose (fmapRose unProp x0) |})
                (promote (@props' _ _ HCheck (S n) pf sh x))) seed s) = true.
      remember
        (run
           (fmap
              (fun x0 : Rose QProp =>
                 {| unProp := joinRose (fmapRose unProp x0) |})
              (promote (props' (S n) pf sh x))) seed s) as b.
      symmetry in Heqb. setoid_rewrite runFmap in Heqb.
      move : Heqb => [rqp [Hrun Hb]]. simpl. rewrite Hb.
      apply runPromote in Hrun. rewrite -Hrun.
      simpl in *. by destruct ((run (checker (pf x)) seed s)) as [[res [l]]] => /=.
      apply H.
      apply semFmapSize. eexists. split => /=.
      apply semPromoteSize.  exists seed. reflexivity.
      simpl. rewrite runFmap. eexists. split => //=.
      remember ((run
                     (promote
                        (MkRose (checker (pf x))
                           {| force := List.map (props' n pf sh) (sh x) |}))
                     seed s)) as b.
      symmetry in Heqb. setoid_rewrite runPromote in Heqb. by rewrite -Heqb.
  - unfold props. generalize 1000.
    move => n H qp /semGenSizeCorrect [seed /runFmap [rqp [H1 H2]]].
    suff : success (run (@checker _ HCheck (pf x)) seed s) = true.
    + subst.
      remember (run (promote (props' n pf sh x)) seed s) as b. symmetry in Heqb.
      apply runPromote in Heqb; subst. simpl.
      case: n => [| n] /=;
      by destruct ((run (checker (pf x)) seed s)) as [[res [l]]] => //=.
      subst. apply H. apply semGenSizeCorrect.
      by eexists; eexists.
Qed.


Lemma semCover_id:
  forall {prop : Type} {H : Checkable prop} (b: bool) (n: nat)
         (s: String.string) (p : prop) (size: nat),
    semCheckerSize (cover b n s p) size <-> semCheckableSize p size.
Proof.
  move=> prop H b n s p. split.
  - rewrite /cover. case: b => //.
    move => H1. apply mapTotalResult_id in H1 => //.
      by move => [? ? ? ? ? ?].
  - move => H1. rewrite /cover. case: b => //.
    apply mapTotalResult_id => //.
      by move => [? ? ? ? ? ?].
Qed.

Lemma semClassify_id:
   forall {prop : Type} {H : Checkable prop} (b: bool) (s: String.string)
          (p : prop) (size : nat),
    semCheckerSize (classify b s p) size <-> semCheckableSize p size.
Proof.
  move=> prop H b s p size. by rewrite /classify semCover_id.
Qed.

Lemma semLabel_id:
   forall {prop : Type} {H : Checkable prop} (s: String.string)
          (p : prop) (size: nat),
    semCheckerSize (label s p) size <-> semCheckableSize p size.
Proof.
  move=> prop H s p size. by rewrite /label semClassify_id.
Qed.

Lemma semCollect_id:
   forall {prop : Type} {H : Checkable prop} (s: String.string)
          (p : prop) (size: nat),
    semCheckerSize (collect s p) size <-> semCheckableSize p size.
Proof.
  move=> prop H s p size. by rewrite /collect semLabel_id.
Qed.

Open Scope Checker_scope.

Lemma semImplication:
      forall {prop : Type} {H : Checkable prop}
             (p : prop) (b : bool) (s : nat),
        semCheckerSize (b ==> p) s <-> b = true -> semCheckableSize p s.
Proof.
  move => prop H p b. case: b.
  - split => /=; auto. apply. reflexivity.
  - split; try congruence. move => _.
    rewrite /implication.  rewrite /semChecker /checker /testResult.
    move => qp . by move=> /semReturnSize H'; subst.
Qed.


(* equivalences for other combinators *)

Lemma semReturnGen:
  forall (p : QProp) (size: nat),
    semCheckerSize (returnGen p) size <-> semCheckableSize p size.
Proof.
  move=> qp s. rewrite /semChecker. split;
  move => H qp' /semReturnSize Hprop; subst;
  apply H; by apply semReturnSize.
Qed.

Lemma semBindGen:
  forall {A } (gen : G A) (p : A -> Checker) (size: nat),
    semCheckerSize (bindGen gen p) size <->
    forall g, semGenSize gen size g -> semCheckerSize (p g) size.
Proof.
  move => A gen p. unfold semCheckerSize. split.
  - move => H g Hsize qp Hsize'. eapply H.
    apply semBindSize.  eexists; split; eassumption.
  - move => H qp /semBindSize [a [H1 H2]]. eapply H; eassumption.
Qed.

Lemma semPredQProp:
  forall (p : G QProp) (s : nat),
    semCheckableSize p s <-> (semCheckerSize p s).
Proof.
  move=> p.
  rewrite /semCheckableSize /checker
          /testChecker /checker /testProp /semCheckerSize.
  split; move => Hqp qp Hsize; auto.
Qed.

Lemma semForAll :
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : G A) (f : A -> prop) (size: nat),
    semCheckerSize (forAll gen f) size <->
    forall (a : A), semGenSize gen size a -> semCheckableSize (f a) size.
Proof.
  move => A prop Htest show gen pf. split => H'.
  - rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
    by apply semPrintTestCase_id in Hgen.
  - rewrite /forAll in H' *. apply semBindGen => g Hgen.
    rewrite semPrintTestCase_id. by apply H'.
Qed.

Lemma semForAllShrink:
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : G A) (f : A -> prop) shrinker (size: nat),
    semCheckerSize (forAllShrink gen shrinker f) size <->
    forall a : A, semGenSize gen size a -> semCheckableSize (f a) size.
Proof.
  move => A prop H show gen pf shrink. split.
  - rewrite /forAllShrink semBindGen.
    move=> H' a /H' Hgen. setoid_rewrite semShrinking_id in Hgen.
    setoid_rewrite semPredQProp in Hgen.
    by apply semPrintTestCase_id in Hgen.
  - move=> H'. rewrite /forAllShrink semBindGen. move => a g.
    rewrite semShrinking_id. apply semPredQProp.
    rewrite semPrintTestCase_id. by auto.
Qed.


(* equivalent Props for Checkables *)

Lemma semBool:
  forall (b : bool) (size: nat), semCheckableSize b size <-> b = true.
Proof.
  move => b. case: b.
  - split => // _. rewrite /semCheckableSize /semCheckerSize.
    by move => qp /semReturnSize Heq; subst.
  - split => //. rewrite /semCheckableSize /semCheckerSize.
    move => /(_ (MkProp (MkRose (liftBool false) (lazy nil)))) H.
    apply H. by apply semReturnSize.
Qed.

Lemma semResult:
  forall (res: Result) (size: nat),
    semCheckableSize res size <-> resultSuccessful res = true.
Proof.
  rewrite /semCheckableSize /checker /testResult /semCheckerSize.
  move => res. split.
  + move=> /(_ ({| unProp := returnRose res |})) /= H.
    apply H. by apply semReturnSize.
  + by move=> H [[res' l]] /semReturnSize [Heq2 Heq3]; subst.
Qed.

Lemma semUnit:
  forall (t: unit) (size: nat), semCheckableSize t size <-> True.
Proof.
  move => t. split => // _.
  by move => qp /semReturnSize Heq; subst.
Qed.

Lemma semQProp:
  forall (qp: QProp) (size: nat),
    semCheckableSize qp size <-> success qp = true.
Proof.
  move => qp.
  rewrite /semCheckableSize /semCheckerSize /checker /testProp.
  split.
  - apply. by apply semReturnSize.
  - by move => H qp' /semReturnSize Heq; subst.
Qed.

Lemma semGen:
  forall (P : Type) {H : Checkable P} (gen: G P) (size : nat),
    (semCheckableSize gen size) <->
    (forall p, semGenSize gen size p -> semCheckableSize p size).
Proof.
  move=> P H gen. unfold semCheckableSize, semCheckerSize in *. split.
  - move=> Hsem qp Hsize.
    move => qp' Hprop. simpl in *.
    apply Hsem. apply semBindSize. exists qp.
    by split => //.
  - move => Hsem qp /semBindSize [p [Hsize Hsize']].
    eapply Hsem; eassumption.
Qed.

Lemma semFun:
  forall {A prop : Type} {H1 : Show A} {H2 : Arbitrary A} {H3 : Checkable prop}
         (f : A -> prop) (size: nat),
    semCheckableSize f size <->
    forall (a : A), semGenSize arbitrary size a -> semCheckableSize (f a) size.
Proof.
  move=> A prop H1 H2 H3 f.
  rewrite /semCheckable /checker /testFun.
  split.
  - move => /semForAllShrink H' a' /H' Gen. by auto.
  - move => H'. apply semForAllShrink => a' /H' Hgen. by auto.
Qed.

Lemma semPolyFun:
  forall {prop : Type -> Type} {H : Checkable (prop nat)} (f : forall T, prop T)
         (size : nat),
    (semCheckableSize f size) <-> (semCheckableSize (f nat) size).
Proof.
  move => prop H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_id.
Qed.

Lemma semPolyFunSet:
  forall {prop : Set -> Type} {H : Checkable (prop nat)} (f : forall T, prop T) (size: nat),
    (semCheckableSize f size) <->  (semCheckableSize (f nat) size).
Proof.
  move => prop H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_id.
Qed.

(* A typeclass so we can automate the application of the previous theorems
  and get a readable Prop *)

Class Provable (A : Type) {H: Checkable A} : Type :=
 {
    proposition : nat -> A -> Prop;
    _ : forall a s, proposition s a <-> semCheckableSize a s
  }.

Program Instance proveResult : Provable Result :=
  {|
    proposition s r := resultSuccessful r
  |}.
Next Obligation.
  by rewrite semResult.
Qed.

Program Instance proveUnit : Provable unit :=
  {|
    proposition := fun _ _ => True
  |}.
Next Obligation.
  by rewrite semUnit.
Qed.

Program Instance proveQProp : Provable QProp :=
  {|
    proposition s qp := success qp = true
  |}.
Next Obligation.
  by rewrite semQProp.
Qed.

Program Instance proveBool : Provable bool :=
  {|
    proposition s b :=  b = true
  |}.
Next Obligation.
  by rewrite semBool.
Qed.

Program Instance proveGenProp {prop : Type} `{Provable prop} :
  Provable (G prop) :=
  {|
    proposition s g := (forall p, semGenSize g s p -> proposition s p)
  |}.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move => H'. apply semGen=> p Hgen. apply proof. eapply H'. eassumption.
  - move => /semGen H' p Hgen. eapply proof. apply H'. by auto.
Qed.

Program Instance proveChecker : Provable Checker :=
  {|
    proposition s g := semCheckerSize g s
  |}.
Next Obligation.
  split; intros H; by apply semPredQProp.
Qed.

Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A}
        `{Provable prop}: Provable (A -> prop) :=
  {|
    proposition s p :=
      (forall a,
         semGenSize arbitrary s a ->
         proposition s (p a))
  |}.
Next Obligation.
  destruct H2 as [semP proof]. rewrite /proposition. split.
  - move=> H'. apply semFun => a' /H' Hgen.
    by apply proof.
  - move=> H' a' Hgen. apply proof. by apply semFun.
Qed.

Program Instance provePolyFun {prop : Type -> Type} `{Provable (prop nat)} :
  Provable (forall T, prop T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFun.
  - move=> /semPolyFun H'. by apply proof.
Qed.

Program Instance provePolyFunSet {prop : Set -> Type} `{Provable (prop nat)} :
  Provable (forall T, prop T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFunSet.
  - move=> /semPolyFunSet H'. by apply proof.
Qed.
