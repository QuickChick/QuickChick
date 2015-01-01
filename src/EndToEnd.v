Require Import Show RoseTrees.
Require Import ModuleGen GenCombinators Arbitrary Checker.
Require Import ssreflect ssrbool eqtype.

Import Gen GenComb.

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
  forall qp, semGen P qp -> success qp = true.

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
    set qp' :=
      match qp with
        | {| unProp := t |} => {| unProp := fmapRose f t |}
      end.
    specialize (H1 qp'). 
    have: success qp' = true.
    { apply H1.  apply semFmap. exists qp; split => //. }
    destruct qp as [[]]. simpl in *. by rewrite -Hyp.
  - move => H1 qp /semFmap [qp' [/H1 Hprop H2]]; subst.
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




(* TODO : This proof needs refactoring! *)
Lemma semShrinking_id:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop),
    semChecker (shrinking shrinker x0 pf) <->
    semCheckable (pf x0).
Proof.
  move => prop A HCheck sh x pf. unfold semCheckable, shrinking, semChecker.
  split. 
  - unfold props. generalize 1000.  
    case => [| n] H qp /semGenCorrect [size [seed Hgen]]; subst. 
    + apply H. apply semFmap. eexists.
      split. apply semPromote.  
      exists seed. exists size. simpl. reflexivity.
      simpl.
      by destruct ((run (checker (pf x)) seed size)) as [[res [l]]] => /=.
    + suff :
        success
          (run
             (fmap
                (fun x0 => {| unProp := joinRose (fmapRose unProp x0) |})
                (promote (@props' _ _ HCheck (S n) pf sh x))) seed size) = true.
      remember 
        (run
           (fmap
              (fun x0 : Rose QProp =>
                 {| unProp := joinRose (fmapRose unProp x0) |})
              (promote (props' (S n) pf sh x))) seed size) as b.  
      symmetry in Heqb. setoid_rewrite runFmap in Heqb.
      move : Heqb => [rqp [Hrun Hb]]. simpl. rewrite Hb. 
      apply runPromote in Hrun. rewrite -Hrun. 
      simpl in *. by destruct ((run (checker (pf x)) seed size)) as [[res [l]]] => /=.
      apply H; exists size. 
      apply semFmapSize. eexists. split => /=.
      apply semPromoteSize.  exists seed. reflexivity.
      simpl. rewrite runFmap. eexists. split => //=.
      remember ((run
                     (promote
                        (MkRose (checker (pf x))
                           {| force := List.map (props' n pf sh) (sh x) |}))
                     seed size)) as b.
      symmetry in Heqb. setoid_rewrite runPromote in Heqb. by rewrite -Heqb.
  - unfold props. generalize 1000.  
    move => n H qp /semGenCorrect [size [seed /runFmap [rqp [H1 H2]]]].
    suff : success (run (@checker _ HCheck (pf x)) seed size) = true.
    + subst.
      remember (run (promote (props' n pf sh x)) seed size) as b. symmetry in Heqb.
      apply runPromote in Heqb; subst. simpl.
      case: n => [| n] /=;
      by destruct ((run (checker (pf x)) seed size)) as [[res [l]]] => //=.
      subst. apply H. apply semGenCorrect.
      by eexists; eexists.
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
    move => qp. by move=> /semReturn H'; subst. 
Qed.
  

(* equivalences for other combinators *)

Lemma semReturnGen:
  forall (p : QProp),
    semChecker (returnGen p) <-> semCheckable p.
Proof.
  move=> p. rewrite /semChecker. split;
  move => H qp Hprop; auto.
Qed.

(* Not provable *)
(* Lemma semBindGen: *)
(*   forall {A } (gen : G A) (p : A -> Checker), *)
(*     semChecker (bindGen gen p) <->  *)
(*     forall g, semGen gen g -> semChecker (p g). *)
(* Proof.  *)
(*   move => A gen p. unfold semChecker; split.  *)
(* Abort. *)


Lemma semPredQProp:
  forall (p : G QProp), semCheckable p <-> (semChecker p).
Proof.
   move=> p.
  rewrite /semCheckable /checker /testGenProp /checker /testProp /semChecker.
  split.
  - move => Hqp qp [s Hsize]. apply Hqp. exists s.
    apply semBindSize. exists qp. split => //.
    by apply semReturnSize.
  - move => H pq [s /semBindSize [qp [H1 /semReturnSize H2]]]; subst.
    apply H. by exists s.
Qed.

Lemma semForAll :
  forall {A prop : Type} {H : Checkable prop} `{Show A} 
         (gen : G A) (f : A -> prop),
    semChecker (forAll gen f) <->
    forall (a : A) s, semSize gen s a -> semCheckable (f a).
Proof.
  (* move => A prop Htest show gen pf. split => H'. *)
  (* - rewrite /forAll  /semCheckable /semChecker in H'.  *)
  (*   move : H' => H' a S Hgen. *)
  (*   rewrite /semCheckable /semChecker => qp [s' Hgen']. *)
  (*   apply H'. eexists. apply semBindSize. eexists; split => //. *)
  (*   apply Hgen. apply semPrintTestCase_id. *)
  (*   apply semPrintTestCase_id in Hgen. *)
  (* - rewrite /forAll in H' *. apply semBindGen => g Hgen. *)
  (*   rewrite semPrintTestCase_id. by apply H'. *)
Abort.

Lemma semForAllShrink:
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : G A) (f : A -> prop) shrinker,
    semChecker (forAllShrink gen shrinker f) <->
    forall a : A, semGen gen a -> semCheckable (f a).
Proof.
  (* move => A prop H show gen pf shrink. split. *)
  (* - rewrite /forAllShrink semBindGen. *)
  (*   move=> H' a /H' Hgen. setoid_rewrite semShrinking_id in Hgen. *)
  (*   setoid_rewrite semPredQProp in Hgen. *)
  (*   by apply semPrintTestCase_id in Hgen. *)
  (* - move=> H'. rewrite /forAllShrink semBindGen. move => a g. *)
  (*   rewrite semShrinking_id. apply semPredQProp. *)
  (*   rewrite semPrintTestCase_id. by auto. *)
Abort.

(* equivalent Props for Checkables *)

Lemma semBool:
  forall (b : bool), semCheckable b <-> b = true.
Proof.  
  move => b. case: b. 
  - split => //. rewrite /semCheckable /semChecker.
    by move => _ qp [size /semReturnSize Heq]; subst.
  - split => //. rewrite /semCheckable /semChecker. 
    move => /(_ (MkProp (MkRose (liftBool false) (lazy nil)))) H.
    apply H. by apply semReturn. 
Qed.

Lemma semResult:
  forall (res: Result), semCheckable res <-> resultSuccessful res = true.
Proof.
  rewrite /semCheckable /checker /testResult /semChecker.
  move => res. split.
  + move=> /(_ ({| unProp := returnRose res |})) /= H.
    apply H. by apply semReturn.
  + by move=> H [[res' l]] [Heq1 /semReturnSize [Heq2 Heq3]]; subst. 
Qed.

Lemma semUnit:
  forall (t: unit), semCheckable t <-> True.
Proof.
  move => t. split => // _.
  by move => qp /semReturn Heq; subst. 
Qed.

Lemma semQProp:
  forall (qp: QProp), semCheckable qp <-> success qp = true.
Proof.
  move => qp. 
  rewrite /semCheckable /semChecker /checker /testProp.
  split. 
  - apply. by apply semReturn.
  - by move => H qp' /semReturn Heq; subst.
Qed.

Lemma semGen:
  forall (P : Type) {H : Checkable P} (gen: G P),
    (semCheckable gen) <-> (forall p, semGen gen p -> semCheckable p).
Proof.
  move=> P H gen. split.
  - move=> Hsem qp [n1 Hgen]. rewrite /semCheckable /semChecker in Hsem *.
    move => qp' [n2 Hprop]. simpl in *.
    apply Hsem. exists n1. apply semBindSize. exists qp.
    split => //.
Abort.

Lemma semFun:
  forall {A prop : Type} {H1 : Show A} {H2 : Arbitrary A} {H3 : Checkable prop}
         (f : A -> prop),
    semCheckable f <->
    forall (a : A), semGen arbitrary a -> semCheckable (f a).
Proof.
  (* move=> A prop H1 H2 H3 f. *)
  (* rewrite /semCheckable /checker /testFun. *)
  (* split. *)
  (* - move => /semForAllShrink H' a' /H' Gen. by auto. *)
  (* - move => H'. apply semForAllShrink => a' /H' Hgen. by auto. *)
Abort.

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

(* Program Instance proveGenProp {prop : Type} `{Provable prop} : *)
(*   Provable (G prop) := *)
(*   {| *)
(*     proposition g := (forall p, semGen g p -> proposition p) *)
(*   |}. *)
(* Next Obligation. *)
  (* destruct H0 as [semP proof]. rewrite /proposition. split. *)
  (* - move => H'. apply semGen=> p Hgen. apply proof. by auto. *)
  (* - move => /semGen H' p Hgen. apply proof. by auto. *)
(* Abort. *)

(* Program Instance proveFun {A prop: Type} `{Arbitrary A} `{Show A} *)
(*         `{Provable prop}: Provable (A -> prop) := *)
(*   {| *)
(*     proposition p := *)
(*       (forall a, *)
(*          semGen arbitrary a -> *)
(*          proposition (p a)) *)
(*   |}. *)
(* Next Obligation. *)
(*   destruct H2 as [semP proof]. rewrite /proposition. split. *)
(*   - move=> H'. apply semFun => a' /H' Hgen. *)
(*     by apply proof. *)
(*   - move=> H' a' Hgen. apply proof. by apply semFun. *)
(* Qed. *)

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