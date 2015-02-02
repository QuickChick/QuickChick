Require Import Show RoseTrees.
Require Import AbstractGen SetOfOutcomes Arbitrary Checker.
Require Import ssreflect ssrbool eqtype.


Definition Checker := Checker Pred.

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
  forall qp, P qp -> success qp = true.

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)
Definition semCheckable {A : Type} {_ : Checkable  A} (a : A) : Prop :=
  semChecker (checker a).

Lemma mapTotalResult_id:
  forall {prop : Type} {H : Checkable prop} (f : Result -> Result) (p : prop),
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semChecker (mapTotalResult f p) <-> semCheckable p).
Proof.
  move => prop H f p Hyp.
  rewrite /semCheckable  /mapTotalResult /mapRoseResult /mapProp /semChecker.
  split.
  - move=> H1 qp Hprop.
    rewrite fmapGen_def in H1.
    set qp' :=
      match qp with
        | {| unProp := t |} => {| unProp := fmapRose f t |}
      end.
    have: success qp' = true.
    { apply H1. exists qp; split => //. }
    destruct qp as [[]]. simpl in *. by rewrite -Hyp.
  - move => H1 qp [qp' [/H1 Hprop H2]].
    rewrite /returnP in H2. subst. rewrite /success.
    destruct qp' as [[]]. simpl in *. by rewrite -Hyp.
Qed.

Lemma semCallback_id:
  forall {prop : Type} {H : Checkable prop} (cb : Callback) (p : prop),
    semChecker (callback cb p) <-> semCheckable p.
Proof.
  move => prop tp cb p. rewrite /callback.
  split; move => H.
  - apply mapTotalResult_id in H => //;
    by move => [? ? ? ? ? ?].
  - apply mapTotalResult_id => //;
    by move => [? ? ? ? ? ?].
Qed.

Lemma semWhenFail_id:
  forall {prop : Type} {H : Checkable prop} (s : String.string) (p : prop),
    semChecker (whenFail s p) <-> semCheckable p.
Proof.
  move => prop H s p. by rewrite /whenFail semCallback_id.
Qed.


Lemma semPrintTestCase_id:
  forall {prop: Type} {tp : Checkable prop} (s: String.string) (p: prop),
    semChecker (printTestCase s p) <-> semCheckable p.
Proof.
  move => prop tp s p. by rewrite /printTestCase semCallback_id.
Qed.

Lemma semShrinking_id_aux:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop) n,
    semChecker (fmapGen (fun x => MkProp (joinRose (fmapRose unProp x)))
                         (promote ((props' n pf shrinker x0)))) <->
    semCheckable (pf x0).
Proof.
  move=> prop A H shrinker x0 pf n. destruct n.
  -  rewrite /semCheckable /semChecker !fmapGen_def. split.
     + move => Hfail qp Hprop. apply Hfail. eexists.
       split. rewrite /promote /PredMonad /promoteP /=.
       exists qp. split => //. by destruct qp as [[[] []]].
     + move=> Hfail qp [rqp  [[qp' [Hprop Heq']] Heq]].
       rewrite /returnP in Heq'; subst. apply Hfail.
       by destruct qp' as [[[] []]].
  - rewrite /semCheckable fmapGen_def /semChecker /= /bindP /returnP /=.
    split.
    + move=> Hfail qp Hprop. apply Hfail. eexists.
      split. exists qp. split => //. by destruct qp as [[[] []]].
    + move=> Hfail qp [rqp [[qp' [Hprop eq]] eq']]; subst.
      apply Hfail.  by destruct qp' as [[[] []]].
Qed.

Lemma semShrinking_id:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop),
    semChecker (shrinking shrinker x0 pf) <->
    semCheckable (pf x0).
Proof.
  move=> prop A H shrinker x0 pf.
  rewrite /shrinking /props. apply semShrinking_id_aux.
Qed.

Lemma semCover_id:
  forall {prop : Type} {H : Checkable prop} (b: bool) (n: nat)
         (s: String.string) (p : prop),
    semChecker (cover b n s p) <-> semCheckable p.
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
          (p : prop),
    semChecker (classify b s p) <-> semCheckable p.
Proof.
  move=> prop H b s p. by rewrite /classify semCover_id.
Qed.

Lemma semLabel_id:
   forall {prop : Type} {H : Checkable prop} (s: String.string)
          (p : prop),
    semChecker (label s p) <-> semCheckable p.
Proof.
  move=> prop H s p. by rewrite /label semClassify_id.
Qed.

Lemma semCollect_id:
   forall {prop : Type} {H : Checkable prop} (s: String.string)
          (p : prop),
    semChecker (collect s p) <-> semCheckable p.
Proof.
  move=> prop H s p. by rewrite /collect semLabel_id.
Qed.

Open Scope Checker_scope.

Lemma semImplication:
      forall {prop : Type} {H : Checkable prop}
             (p : prop) (b : bool),
        semChecker (b ==> p) <-> b = true -> semCheckable p.
Proof.
  move => prop H p b. case: b.
  - split => /=; auto. apply. reflexivity.
  - split; try congruence. move => _.
    rewrite /implication.  rewrite /semChecker /checker /testResult.
    move => qp. rewrite returnGen_def. by move => <-.
Qed.


(* equivalences for other combinators *)

Lemma semBindGen:
  forall {A } (gen : Pred A) (p : A -> Checker),
    semChecker (bindGen gen p) <-> forall g, gen g -> semChecker (p g).
Proof.
  move=> A gen prop. rewrite /semChecker. split.
  - move => H g Hgen qp Hprop. apply H.
    eexists. split; eassumption.
  - move => H qp [a [Hgen Hprop]]. eauto.
Qed.

Lemma semReturnGen:
  forall (p : QProp),
    semChecker (returnGen p) <-> semCheckable p.
Proof.
  move=> p. rewrite /semChecker. split;
  move => H qp Hprop; auto.
Qed.

(* TODO: Zoe, I changed this proof to make it go through. I'm not sure WHY this changed by adding an extra instance, it's still true though :) *)
Lemma semPredQProp:
  forall (p : Pred QProp), semCheckable p <-> (semChecker p).
Proof.
  move=> p.
  rewrite /semCheckable /checker /testGenProp /checker /testProp.  (*semBindGen.*)
  split.
  - move => H pq /H Hgen. by apply Hgen. (*rewrite returnGen_def /semChecker in Hgen.
    by apply Hgen.*)
  - move => H pq Hgen. unfold testCheckerGen in *.
    rewrite /semChecker in H.
    by auto.
(*rewrite returnGen_def /semChecker.
    move => qp Heq; subst. rewrite /semChecker in H. by auto.*)
Qed.

Lemma semForAll :
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : Pred A) (f : A -> prop),
    semChecker (forAll gen f) <->
    forall a : A, gen a -> semCheckable (f a).
Proof.
  move => A prop Htest show gen pf. split => H'.
  - rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
    by apply semPrintTestCase_id in Hgen.
  - rewrite /forAll in H' *. apply semBindGen => g Hgen.
    rewrite semPrintTestCase_id. by apply H'.
Qed.

Lemma semForAllShrink:
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : Pred A) (f : A -> prop) shrinker,
    semChecker (forAllShrink gen shrinker f) <->
    forall a : A, gen a -> semCheckable (f a).
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
  forall (b : bool), semCheckable b <-> b = true.
Proof.
  move => b. case: b.
  - split => //. compute.
    by move => _ qp Heq; subst.
  - split => //. rewrite /semCheckable /semChecker. move => H.
    simpl in H.  rewrite /returnP /= in H.
    by specialize (H _ Logic.eq_refl).
Qed.

Lemma semResult:
  forall (res: Result), semCheckable res <-> resultSuccessful res = true.
Proof.
  rewrite /semCheckable /checker /testResult /semChecker.
  move => res. split.
  + move=> /(_ ({| unProp := returnRose res |})) /= H.
    by apply H.
  + move=> H [[res' l]] [Heq1 Heq2]; by subst.
Qed.

Lemma semUnit:
  forall (t: unit), semCheckable t <-> True.
Proof.
  move => t. split => // _. compute.
  by move => qp Heq; subst.
Qed.

Lemma semQProp:
  forall (qp: QProp), semCheckable qp <-> success qp = true.
Proof.
  move => qp. rewrite /semCheckable /semChecker /checker
                      /testProp returnGen_def.
  split.
  - auto.
  - by move => H qp' Heq; subst.
Qed.

Lemma semGen:
  forall (P : Type) {H : Checkable P} (gen: Pred P),
    (semCheckable gen) <-> (forall p, gen p -> semCheckable p).
Proof.
  move=> P H gen. split.
  - move=> Hsem qp Hgen. rewrite /semCheckable /semChecker in Hsem *.
    move => qp' Hprop. apply Hsem. rewrite /checker /testGenProp bindGen_def.
    exists qp. split => //.
  - move => H'. rewrite /semCheckable /semChecker. move=> qp prop.
    rewrite /checker /testGenProp in prop. move : prop => [p [/H' Hgen Hprop]].
    rewrite /semCheckable /semChecker in Hgen. by auto.
Qed.

Lemma semFun:
  forall {A prop : Type} {H1 : Show A} {H2 : Arbitrary A} {H3 : Checkable prop}
         (f : A -> prop),
    semCheckable f <->
    forall (a : A), (arbitrary : Pred A) a -> semCheckable (f a).
Proof.
  move=> A prop H1 H2 H3 f.
  rewrite /semCheckable /checker /testFun.
  split.
  - move => /semForAllShrink H' a' /H' Gen. by auto.
  - move => H'. apply semForAllShrink => a' /H' Hgen. by auto.
Qed.

(* I think this is the strongest checker we can get for polymorphic functions *)
Lemma semPolyFun:
  forall {prop : Type -> Type} {H : Checkable (prop nat)} (f : forall T, prop T),
    (semCheckable f) <-> (semCheckable (f nat)).
Proof.
  move => prop H f. rewrite /semCheckable {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_id.
Qed.

Lemma semPolyFunSet:
  forall {prop : Set -> Type} {H : Checkable (prop nat)} (f : forall T, prop T),
    (semCheckable f) <->  (semCheckable (f nat)).
Proof.
  move => prop H f. rewrite /semCheckable {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_id.
Qed.

(* A typeclass so we can automate the application of the previous theorems
  and get a readable Prop *)

Class Provable (A : Type) {H: Checkable A} : Type :=
 {
    proposition : A -> Prop;
    _ : forall a, proposition a <-> semCheckable a
  }.

Program Instance proveResult : Provable Result :=
  {|
    proposition := resultSuccessful
  |}.
Next Obligation.
  by rewrite semResult.
Qed.

Program Instance proveUnit : Provable unit :=
  {|
    proposition := fun _ => True
  |}.
Next Obligation.
  by rewrite semUnit.
Qed.

Program Instance proveQProp : Provable QProp :=
  {|
    proposition qp := success qp = true
  |}.
Next Obligation.
  by rewrite semQProp.
Qed.

Program Instance proveBool : Provable bool :=
  {|
    proposition b :=  b = true
  |}.
Next Obligation.
  by rewrite semBool.
Qed.

Program Instance proveGenProp {prop : Type} `{Provable prop} :
  Provable (Pred prop) :=
  {|
    proposition g := (forall p, g p -> proposition p)
  |}.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move => H'. apply semGen=> p Hgen. apply proof. by auto.
  - move => /semGen H' p Hgen. apply proof. by auto.
Qed.

Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A}
        `{Provable prop}: Provable (A -> prop) :=
  {|
    proposition p :=
      (forall a,
         @arbitrary _ _ Pred _ a ->
         proposition (p a))
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
    proposition f := proposition (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFun.
  - move=> /semPolyFun H'. by apply proof.
Qed.

Program Instance provePolyFunSet {prop : Set -> Type} `{Provable (prop nat)} :
  Provable (forall T, prop T) :=
  {
    proposition f := proposition (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFunSet.
  - move=> /semPolyFunSet H'. by apply proof.
Qed.
