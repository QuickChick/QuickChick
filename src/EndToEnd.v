Require Import List seq ssreflect ssrbool ssrnat ZArith eqtype.

Require Import AbstractGen Property SetOfOutcomes.

Definition semProperty (P : Pred QProp) : Prop :=
  forall qp, P qp -> failure qp = false.

Definition semTestable {A : Type} {_ : @Testable Pred A} (a : A) : Prop :=
  semProperty (property a).

Lemma semForAllShrink : forall {A prop : Type} {H : Testable prop}
    show (gen : Pred A) shrink (pf : A -> prop),
  semProperty (@forAllShrink Pred _ _ _ H show gen shrink pf) <->
  (forall a : A, gen a -> (semProperty (property (pf a)))).
Proof.
  move => A prop Htest show gen shrink pf. split => H'.
  - move => a Hgen. simpl in H'.
    unfold bindP, semProperty in * => qp H''.
    move /(_ qp) : H' => H'. apply : H'.
    exists a. split => //=.
    unfold fmapP, bindP. exists (MkRose qp (lazy nil)).
    split. Focus 2. compute. destruct qp as [[[? ? ? ? ? ?] []]]. reflexivity.
    unfold promoteP.
    exists qp. admit. (* unfold fmapRose, props. *)
    (* this seems to need some generalization 1000 -> n + induction *)
  - unfold semProperty in * => qp Hforall.
    unfold forAllShrink in Hforall. rewrite bindGen_def in Hforall.
    move : Hforall => [a [Hgen H]]. apply : H' => //=.
    unfold shrinking in H. rewrite fmapGen_def in H.
    move : H => [rqp [H1 H2]]. subst qp.
    unfold promote, PredMonad, promoteP in H1.
    move : H1 => [qp H]. subst rqp.
    (* this is wrong ... probably the semantics of promoteP *)
Abort.
