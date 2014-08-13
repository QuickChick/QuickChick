Require Import Show RoseTrees.
Require Import AbstractGen SetOfOutcomes Arbitrary Property.
Require Import ssreflect ssrbool eqtype.


Definition Property := Property Pred.

Definition resultCorrect (r : Result) : bool :=
  match r with
    | MkResult (Some res) expected _ _ _ _ =>
      res == expected
    | _ => true
  end.

Definition failure qp :=
  match qp with
    | MkProp (MkRose res _) => ~~ (resultCorrect res)
  end.

(* Maps a Property to a Prop *)
Definition semProperty (P : Property) : Prop :=
  forall qp, P qp -> failure qp = false.

(* Maps a Testable to a Prop i.e. gives an equivalent proposition to the
   property under test *)

Definition semTestable {A : Type} {_ : Testable  A} (a : A) : Prop :=
  semProperty (property a).

(* Lemmas about idempotent combinators i.e. combinators that do not change
   the testing outcome *)

Lemma mapTotalResult_idemp:
  forall {prop : Type} {H : Testable prop} (f : Result -> Result) (p : prop),
    (forall res, resultCorrect res = resultCorrect (f res)) ->
    ((semTestable p) <-> (semProperty (mapTotalResult f p))).
Proof.
  move => prop H f p Hyp.
  rewrite /semTestable  /mapTotalResult /mapRoseResult /mapProp /semProperty.
  split.
  - move => H1 qp [qp' [/H1 Hprop H2]].
    rewrite /returnP in H2. subst. rewrite /failure.
    destruct qp' as [[]]. simpl in *. by rewrite -Hyp.
  - move=> H1 qp Hprop.
    set qp' :=
      match qp with
        | {| unProp := t |} => {| unProp := fmapRose f t |}
      end.
    have: failure qp' = false.
    { apply H1. rewrite fmapGen_def. exists qp; split => //. }
    destruct qp as [[]]. simpl in *. by rewrite -Hyp.
Qed.


Lemma semCallback_idemp:
  forall {prop : Type} {H : Testable prop} (cb : Callback) (p : prop),
    semProperty (callback cb p) <-> semTestable p.
Proof.
  move => prop tp cb p. rewrite /callback.
  split; move => H.
  - apply mapTotalResult_idemp in H => //;
    by move => [? ? ? ? ? ?].
  - apply mapTotalResult_idemp => //;
    by move => [? ? ? ? ? ?].
Qed.

Lemma semWhenFail_idemp:
  forall {prop : Type} {H : Testable prop} (s : String.string) (p : prop),
    semProperty (whenFail s p) <-> semTestable p.
Proof.
  move => prop H s p. by rewrite /whenFail semCallback_idemp.
Qed.


Lemma semPrintTestCase_idemp:
  forall {prop: Type} {tp : Testable prop} (s: String.string) (p: prop),
    semProperty (printTestCase s p) <-> semTestable p.
Proof.
  move => prop tp s p. by rewrite /printTestCase semCallback_idemp.
Qed.

Lemma semShrinking_idemp_aux:
  forall {prop A : Type} {H : Testable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop) n,
    semProperty (fmapGen (fun x => MkProp (joinRose (fmapRose unProp x)))
                         (promote ((props' n pf shrinker x0)))) <->
    semTestable (pf x0).
Proof.
  move=> prop A H shrinker x0 pf n. destruct n.
  -  rewrite /semTestable /semProperty !fmapGen_def. split.
     + move => Hfail qp Hprop. apply Hfail. eexists.
       split. rewrite /promote /PredMonad /promoteP /=.
       exists qp. split => //. by destruct qp as [[[] []]].
     + move=> Hfail qp [rqp  [[qp' [Hprop Heq']] Heq]].
       rewrite /returnP in Heq'; subst. apply Hfail.
       by destruct qp' as [[[] []]].
  - rewrite /semTestable fmapGen_def /semProperty /= /bindP /returnP /=.
    split.
    + move=> Hfail qp Hprop. apply Hfail. eexists.
      split. exists qp. split => //. by destruct qp as [[[] []]].
    + move=> Hfail qp [rqp [[qp' [Hprop eq]] eq']]; subst.
      apply Hfail.  by destruct qp' as [[[] []]].
Qed.


Lemma semShrinking_idemp:
  forall {prop A : Type} {H : Testable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop),
    semProperty (shrinking shrinker x0 pf) <->
    semTestable (pf x0).
Proof.
  move=> prop A H shrinker x0 pf.
  rewrite /shrinking /props. apply semShrinking_idemp_aux.
Qed.

Lemma semCover_idemp:
  forall {prop : Type} {H : Testable prop} (b: bool) (n: nat)
         (s: String.string) (p : prop),
    semProperty (cover b n s p) <-> semTestable p.
Proof.
  move=> prop H b n s p. split.
  - rewrite /cover. case: b => //.
    move => H1. apply mapTotalResult_idemp in H1 => //.
      by move => [? ? ? ? ? ?].
  - move => H1. rewrite /cover. case: b => //.
    apply mapTotalResult_idemp => //.
      by move => [? ? ? ? ? ?].
Qed.

Lemma semClassify_idemp:
   forall {prop : Type} {H : Testable prop} (b: bool) (s: String.string)
          (p : prop),
    semProperty (classify b s p) <-> semTestable p.
Proof.
  move=> prop H b s p. by rewrite /classify semCover_idemp.
Qed.

Lemma semLabel_idemp:
   forall {prop : Type} {H : Testable prop} (s: String.string)
          (p : prop),
    semProperty (label s p) <-> semTestable p.
Proof.
  move=> prop H s p. by rewrite /label semClassify_idemp.
Qed.

Lemma semCollect_idemp:
   forall {prop : Type} {H : Testable prop} (s: String.string)
          (p : prop),
    semProperty (collect s p) <-> semTestable p.
Proof.
  move=> prop H s p. by rewrite /collect semLabel_idemp.
Qed.


(* equivalences for other combinators *)

Lemma semBindGen:
  forall {A} (gen : Pred A) (p : A -> Property),
    semProperty (bindGen gen p) <-> forall g, gen g -> semProperty (p g).
Proof.
  move=> A gen prop. rewrite /semProperty. split.
  - move => H g Hgen qp Hprop. apply H.
    rewrite bindGen_def. exists g. split => //.
  - move => H qp [a [Hgen Hprop]]. eauto.
Qed.

Definition promotePt {M : Type -> Type} {A : Type}
           (m : Rose (Pred A)) : Pred (Rose A) :=
  fun (ma : Rose A) =>
    match m with
        | MkRose pred _ =>
          match ma with
            | MkRose a _ => pred a
          end
    end.

Lemma semReturnGen:
  forall (p : QProp),
    semProperty (returnGen p) <-> semProperty (property p).
Proof.
  move=> p. rewrite /semProperty. split;
  move => H qp Hprop; auto.
Qed.

Lemma semForAll :
  forall {A prop : Type} {H : Testable prop}
         show (gen : Pred A) (pf : A -> prop),
  semProperty (forAll show gen pf) <->
  (forall a : A, gen a -> (semTestable (pf a))).
Proof.
  move => A prop Htest show gen pf. split => H'.
  - rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
    by apply semPrintTestCase_idemp in Hgen.
  - rewrite /forAll in H' *. apply semBindGen => g Hgen.
    rewrite semPrintTestCase_idemp. by apply H'.
Qed.

Lemma semPredQProp:
  forall (p : Pred QProp), semTestable p <-> (semProperty p).
Proof.
(*  by *) move=> p.
  rewrite /semTestable /property /testGenProp /property /testProp semBindGen.
  split.
  - move => H pq /H Hgen. rewrite returnGen_def /semProperty in Hgen.
    by apply Hgen.
  - move => H pq Hgen. rewrite returnGen_def /semProperty.
    move => qp Heq; subst. rewrite /semProperty in H. by auto.
Qed.

Lemma semForAllShrink:
  forall {A prop : Type} {H : Testable prop}
         show (gen : Pred A) (pf : A -> prop) shrink,
    semProperty (forAllShrink  show gen shrink pf) <->
    (forall a : A, gen a -> (semTestable (pf a))).
Proof.
  move => A prop H show gen pf shrink. split.
  - rewrite /forAllShrink semBindGen.
    move=> H' a /H' Hgen. setoid_rewrite semShrinking_idemp in Hgen.
    setoid_rewrite semPredQProp in Hgen.
    by apply semPrintTestCase_idemp in Hgen.
  - move=> H'. rewrite /forAllShrink semBindGen. move => a g.
    rewrite semShrinking_idemp. apply semPredQProp.
    rewrite semPrintTestCase_idemp. by auto.
Qed.

(* equivalent Props for Testables *)

Lemma semBool:
  forall (b : bool), (b = true) <-> semTestable b.
Proof.
  move => b. case: b.
  - split => //. compute.
    by move => _ qp Heq; subst.
  - split => //. compute.
    set qp := {| unProp := returnRose (updReason failed "Falsifiable") |}.
    move/(_ qp) => H. symmetry. apply H. reflexivity.
Qed.

Lemma semResult:
  forall (res: Result), resultCorrect res = true <-> semTestable res.
Proof.
  rewrite /semTestable /property /testResult /semProperty.
  move => res. split.
  + move=> H [[res' l]] [Heq1 Heq2]; subst. by rewrite /failure H.
  + move=> /(_ ({| unProp := returnRose res |})) /= H.
    apply Bool.negb_false_iff. by apply H.
Qed.

Lemma semUnit:
  forall (t: unit), True <-> semTestable t.
Proof.
  move => t. split => // _. compute.
  by move => qp Heq; subst.
Qed.

Lemma semQProp:
  forall (qp: QProp),
    failure qp = false <-> semTestable qp.
Proof.
  move => qp. rewrite /semTestable /semProperty /property
                      /testProp returnGen_def.
  split.
  - by move => H qp' Heq; subst.
  - auto.
Qed.

Lemma semGen:
  forall (P : Type) {H : Testable P} (gen: Pred P),
    (forall p, gen p -> semTestable p) <-> (semTestable gen).
Proof.
  move=> P H gen. split.
  - move => H'. rewrite /semTestable /semProperty. move=> qp prop.
    rewrite /property /testGenProp in prop. move : prop => [p [/H' Hgen Hprop]].
    rewrite /semTestable /semProperty in Hgen. by auto.
  - move=> Hsem qp Hgen. rewrite /semTestable /semProperty in Hsem *.
    move => qp' Hprop. apply Hsem. rewrite /property /testGenProp bindGen_def.
    exists qp. split => //.
Qed.

Lemma semFun:
  forall {A prop : Type} {H1 : Show A} {H2 : Arbitrary A} {H3 : Testable prop}
         (f : A -> prop),
    semTestable f <->
    (forall (a : A), @arbitrary _ _ Pred _ a -> semTestable (f a)).
Proof.
  move=> A prop H1 H2 H3 f.
  rewrite /semTestable /property /testFun.
  split.
  - move => /semForAllShrink H' a' /H' Gen. by auto.
  - move => H'. apply semForAllShrink => a' /H' Hgen. by auto.
Qed.

(* I think this is the strongest property we can get for polymorphic functions *)
Lemma semPolyFun:
  forall {prop : Type -> Type} {H : Testable (prop nat)} (f : forall T, prop T),
    (semTestable (f nat)) <-> (semTestable f).
Proof.
  move => prop H f. rewrite /semTestable {2}/property /testPolyFun.
  by rewrite semPrintTestCase_idemp.
Qed.

Lemma semPolyFunSet:
  forall {prop : Set -> Type} {H : Testable (prop nat)} (f : forall T, prop T),
    (semTestable (f nat)) <-> (semTestable f).
Proof.
  move => prop H f. rewrite /semTestable {2}/property /testPolyFun.
  by rewrite semPrintTestCase_idemp.
Qed.

(* A typeclass so we can automate the application of the previous theorems
  and get a readable Prop *)

Class Provable (A : Type) {H: Testable A} : Type :=
 {
    semProp : A -> Prop;
    _ : forall a, semProp a <-> semTestable a
  }.

Program Instance proveResult : Provable Result :=
  {|
    semProp := resultCorrect
  |}.
Next Obligation.
  by apply semResult.
Qed.

Program Instance proveUnit : Provable unit :=
  {|
    semProp := fun _ => True
  |}.
Next Obligation.
  by apply semUnit.
Qed.

Program Instance proveQProp : Provable QProp :=
  {|
    semProp qp := failure qp = false
  |}.
Next Obligation.
  by apply semQProp.
Qed.

Program Instance proveBool : Provable bool :=
  {|
    semProp b :=  b = true
  |}.
Next Obligation.
  by apply semBool.
Qed.

Program Instance proveGenProp {prop : Type} `{Provable prop} :
  Provable (Pred prop) :=
  {|
    semProp g := (forall p, g p -> semProp p)
  |}.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /semProp. split.
  - move => H'. apply semGen=> p Hgen. apply proof. by auto.
  - move => /semGen H' p Hgen. apply proof. by auto.
Qed.

Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A}
        `{Provable prop}: Provable (A -> prop) :=
  {|
    semProp p :=
      (forall a,
         @arbitrary _ _ Pred _ a ->
         semProp (p a))
  |}.
Next Obligation.
  destruct H2 as [semP proof]. rewrite /semProp. split.
  - move=> H'. apply semFun => a' /H' Hgen.
    by apply proof.
  - move=> H' a' Hgen. apply proof. by apply semFun.
Qed.

Program Instance provePolyFun {prop : Type -> Type} `{Provable (prop nat)} :
  Provable (forall T, prop T) :=
  {
    semProp f := semProp (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /semProp. split.
  - move=> /proof H'. by apply semPolyFun.
  - move=> /semPolyFun H'. by apply proof.
Qed.

Program Instance provePolyFunSet {prop : Set -> Type} `{Provable (prop nat)} :
  Provable (forall T, prop T) :=
  {
    semProp f := semProp (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /semProp. split.
  - move=> /proof H'. by apply semPolyFunSet.
  - move=> /semPolyFunSet H'. by apply proof.
Qed.
