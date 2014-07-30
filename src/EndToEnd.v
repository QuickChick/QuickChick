Require Import List seq ssreflect ssrbool ssrnat ZArith eqtype.

Require Import AbstractGen Property SetOfOutcomes.

Definition semProperty (P : Pred QProp) : Prop :=
  forall qp, P qp -> failure qp = false.

Definition semTestable {A : Type} {_ : @Testable Pred A} (a : A) : Prop :=
  semProperty (property a).

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
