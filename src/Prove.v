Require Import Show.
Require Import AbstractGen SetOfOutcomes Arbitrary Property.
Require Import ssreflect.

Definition semProperty (P : Pred QProp) : Prop :=
  forall qp, P qp -> failure qp = false.


Class Provable (A : Type) {H: Testable A} : Type :=
 {
    semProp : A -> Prop;
    _ : forall A, semProp A <-> semProperty (@property Pred _ _ A) 
  }.

Program Instance proveResult : Provable Result :=
  {|
    semProp r := 
      match r with
        | MkResult (Some false) _ _ _ _ _ => False 
        | _ => True
      end
  |}.
Next Obligation.
  destruct A as [[[|] |] exp reas inter stamps callb] => /=. 
  - split; auto. intros _. compute. 
    by move => qp eq; subst. 
  - split; try contradiction. 
    set qp := 
      {| unProp := returnRose 
                    (MkResult (Some false) exp reas inter stamps callb) |}.
    compute. move => /(_ qp)  H. compute in H. 
    have contra: true = false by auto. discriminate.
  - split; auto. intros _. compute. 
    by move => qp eq; subst. 
Qed.


Program Instance proveUnit : Provable unit :=
  {|
    semProp := fun _ => True
  |}.
Next Obligation.
  split; auto. intros _. compute. 
  by move => qp Heq; subst.
Qed.

Program Instance proveProp : Provable QProp :=
  {|
    semProp qp := failure qp = false
  |}.
Next Obligation.
  split. 
  - case: A => [[res l]] //=. compute. 
    by move => H qp Heq; subst.
  - compute. eauto.
Qed.

Program Instance proveBool : Provable bool :=
  {|
    semProp b :=  b = true
  |}.
Next Obligation.
  case : A.
  - split => // _. compute. 
    by move => qp Heq; subst.
  - split => //. compute.
    set qp := {| unProp := returnRose (updReason failed "Falsifiable") |}.
    move/(_ qp) => H. symmetry. apply H. reflexivity.
Qed.
  


Lemma semForAll : forall {A prop : Type} {H : Testable prop}
    show (gen : Pred A) (pf : A -> prop),
  semProperty (@forAll Pred _ _ _ H show gen pf) <->
  (forall a : A, gen a -> (semProperty (property (pf a)))).
Proof. 
  move => A prop Htest show gen pf. split => H'.  
  - move => a Hgen.
    unfold bindP, semProperty, forAll in * . move=> qp. simpl in *.
    set qp' :=  
      match qp with
        | {| unProp := t |} =>
          {| unProp := fmapRose
                         (fun r : Result =>
                            addCallback r
                                        (PostFinalFailure Counterexample
                                                          (fun _  _  =>
                                                             0))) t |} end.
    move /(_ qp') : H' => H' H''. 
    have: failure qp' = false.
    { apply H'.  rewrite /bindP.  exists a. split => //.
      exists qp. split => //. }
    rewrite /qp'. destruct qp as [[[]]]. compute. auto.
  - unfold semProperty in * => qp Hforall.
    unfold forAllShrink in Hforall. 
    rewrite /forAll /= /fmapP /returnP in Hforall.
    move : Hforall => [a [Hgen [qp' [Hprop Hret]]]]. 
    apply H' in Hprop => //. subst. 
    destruct qp' as [[[]]]. compute. auto.
 Qed.

Lemma semForAllShrink : forall {A prop : Type} {H : Testable prop}
    show (gen : Pred A) (pf : A -> prop) shrink,
  semProperty (@forAllShrink Pred _ _ _ H show gen shrink pf) <->
  (forall a : A, gen a -> (semProperty (property (pf a)))).
Proof.
  admit.
Qed.

Lemma forAll_forAllShrink : forall {A prop : Type} {H : Testable prop}
    show (gen : Pred A) (pf : A -> prop) shrink,
  semProperty (@forAllShrink Pred _ _ _ H show gen shrink pf) <->
  semProperty (@forAll Pred _ _ _ H show gen pf).
Proof.
  admit.
Qed.

Opaque forAllShrink. 
Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A}
        `{Provable prop}: Provable (A -> prop) :=
  {|
    semProp p := 
      (forall a, 
         @arbitrary _ _ Pred _ a -> 
         semProp (p a))
  |}.
Next Obligation.
  split. 
  - move => H'. apply forAll_forAllShrink. 
    destruct H2 as [proposition Proof]. destruct H1 as [property1].
    unfold bindP, semProperty, forAll in * . move=> qp. 
    rewrite bindGen_def. move => [a [Harb Hpr]].
    move/(_ (A0 a)): (Proof) => Hequiv. move/Hequiv: (H' a Harb) => {Hequiv} Hequiv. 
    move: Hpr => [qp' [/Hequiv H1 H2]]. rewrite /returnP in H2. subst.
    by destruct qp' as [[[[|] ? ? ? ? ?] l]]. 
  - move => /forAll_forAllShrink H' a Harb. 
    destruct H2 as [proposition Proof]. destruct H1 as [property1].
    unfold semProperty, semProp, forAll in * . 
    rewrite /semProp. apply Proof. move => qp Hprop.
    set qp' :=  match qp with
        | {| unProp := t |} =>
          {| unProp := fmapRose
                         (fun r : Result =>
                            addCallback r
                                        (PostFinalFailure Counterexample
                                                          (fun _  _  =>
                                                             0))) t |} end.
    rewrite bindGen_def in H'.
    move /(_ qp') : H' => H'. 
    have: failure qp' = false.
    { apply H'.  rewrite /bindP.  exists a. split => //.
      exists qp. split => //. }
    rewrite /qp'. destruct qp as [[[]]]. compute. auto.
Qed.