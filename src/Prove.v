Require Import Show.
Require Import AbstractGen SetOfOutcomes Arbitrary Property.
Require Import ssreflect ssrbool eqtype.

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

Definition semProperty (P : Pred QProp) : Prop :=
  forall qp, P qp -> failure qp = false.

Definition semTestable {A : Type} {_ : @Testable Pred A} (a : A) : Prop :=
  semProperty (property a).

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
  destruct res as [[[|] |] exp reas inter stamps callb] => /=. 
  - split; auto. 
    + move => /eqP Heq. compute. 
      by move => qp eq; subst.  
    + set qp := 
      {| unProp := returnRose 
                    (MkResult (Some true) exp reas inter stamps callb) |}.
      move => /(_ qp)  H. compute in H. 
      destruct exp. reflexivity. symmetry. by auto.  
  - split. 
    + move => /eqP Heq. compute. 
      by move => qp eq; subst. 
    + set qp := 
      {| unProp := returnRose 
                     (MkResult (Some false) exp reas inter stamps callb) |}.
      move => /(_ qp)  H. compute in H. 
      destruct exp. symmetry. by auto. reflexivity.
  - split; auto. intros _. compute. 
    by move => qp eq; subst. 
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
   

Lemma semPrintTestCase_idemp:
  forall {prop: Type} {tp : Testable prop} (s: String.string) (p: prop),
    semProperty (printTestCase s p) <-> semTestable p.
Proof.
  move => prop tp s p. rewrite /semTestable /printTestCase /semProperty. 
  split.
  - move => H qp Hprop. 
    set qp' :=  
      match qp with
        | {| unProp := t |} =>
          {| unProp := fmapRose
                         (fun r : Result =>
                            addCallback r
                                        (PostFinalFailure Counterexample
                                                          (fun _  _  =>
                                                             0))) t |} end.
    move /(_ qp') : H => H.  
    have: failure qp' = false.
    { apply H.  rewrite /bindP. compute. exists qp. split => //. }
    rewrite /qp'. destruct qp as [[[]]]. by auto.
  - move => H qp H'. move : H' => [qp' [Hprop Hret]].
    rewrite /returnP in Hret. apply H in Hprop. 
    destruct qp' as [[[]]]. subst.
    by auto.  
Qed.

Lemma semBindGen: 
  forall {A} (gen : Pred A) (p : A -> @Property Pred),
    semProperty (bindGen gen p) <-> forall g, gen g -> semProperty (p g).
Proof.
  move=> A gen prop. rewrite /semProperty. split.
  - move => H g Hgen qp Hprop. apply H. 
    rewrite bindGen_def. exists g. split => //.
  - move => H qp [a [Hgen Hprop]]. eauto.
Qed.

Lemma semForAll : 
  forall {A prop : Type} {H : Testable prop} 
         show (gen : Pred A) (pf : A -> prop),
  (forall a : A, gen a -> (semTestable (pf a))) <->
  semProperty (@forAll Pred _ _ _ H show gen pf).
Proof.  
  move => A prop Htest show gen pf. split => H'.  
  - rewrite /forAll in H' *. apply semBindGen => g Hgen.
    rewrite semPrintTestCase_idemp. by apply H'.
  - rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
    by apply semPrintTestCase_idemp in Hgen.
Qed.

Lemma forAll_forAllShrink: 
  forall {A prop : Type} {H : Testable prop}
    show (gen : Pred A) (pf : A -> prop) shrink,
    semProperty (@forAllShrink Pred _ _ _ H show gen shrink pf) <->
    semProperty (@forAll Pred _ _ _ H show gen pf).
Proof.
  admit.
Qed.

Lemma semForAllShrink: 
  forall {A prop : Type} {H : Testable prop}
         show (gen : Pred A) (pf : A -> prop) shrink,
    (forall a : A, gen a -> (semTestable (pf a))) <-> 
    semProperty (@forAllShrink Pred _ _ _ H show gen shrink pf).
Proof.
  move => A prop H show gen pf shrink.
  rewrite forAll_forAllShrink. split; by move /semForAll => H'.
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


Class Provable (A : Type) {H: Testable A} : Type :=
 {
    semProp : A -> Prop;
    _ : forall a, semProp a <-> semTestable a 
  }.

Opaque semProp semTestable.

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

Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A}
        `{Provable prop}: Provable (A -> prop) :=
  {|
    semProp p := 
      (forall a, 
         @arbitrary _ _ Pred _ a -> 
         semProp (p a))
  |}.
Next Obligation. 
 rewrite /semProp. case: H2 => semP proof. rewrite /semTestable /property /testFun.
 split.
 - move => H'. apply semForAllShrink => a' Hgen. apply proof. by auto.
 - move => /semForAllShrink H' => a' Gen. apply proof. by auto.
Qed.
