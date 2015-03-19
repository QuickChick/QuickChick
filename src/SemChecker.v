Require Import ssreflect ssrbool eqtype.
Require Import Show Sets GenLow GenHigh RoseTrees Checker Arbitrary.

Import GenLow GenHigh.


Definition resultSuccessful (r : Result) : bool :=
  match r with
    | MkResult (Some res) expected _ _ _ _ =>
      res == expected
    | _ => true
  end.

Definition successful qp :=
  match qp with
    | MkProp (MkRose res _) => resultSuccessful res
  end.

(* CH: The forall+implications in semCheckerSize and semChecker_def2
   are just set inclusions ... wouldn't it be more convenient to treat
   them that way? *)

(* Maps a Checker to a Prop *)
(* begin semCheckerSize *)
Definition semCheckerSize (c : Checker) (s : nat): Prop :=
  forall res, res \in semGenSize c s -> successful res = true.
(* end semCheckerSize *)
(* begin semChecker *) 
Definition semChecker (c : Checker) : Prop := forall s, semCheckerSize c s.
(* end semChecker *)
(* another characterization of semChecker *)
Lemma semChecker_def2 : forall c,
  semChecker c <-> (forall qp, semGen c qp -> successful qp = true).
Proof.
  intro c. rewrite /semChecker /semCheckerSize /semGen. split; intro H.
  - intros. destruct H0 as [s H0]. eapply (H s). tauto.
  - intros. apply H. exists s. by split.
Qed.

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)
(* begin semCheckable *)
Definition semCheckable {A} `{Checkable A} (a : A) : Prop := semChecker (checker a).
(* end semCheckable *)
(* begin semCheckableSize *)
Definition semCheckableSize {A : Type} {_ : Checkable  A}
           (a : A) (s : nat) : Prop :=
  semCheckerSize (checker a) s.
(* end semCheckableSize *)

Lemma mapTotalResult_id {prop : Type} {H : Checkable prop} (f : Result -> Result)
         (p : prop) (s : nat) :
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semCheckerSize (mapTotalResult f p) s <-> semCheckableSize p s).
Proof.
move=> eq_res.
rewrite /mapTotalResult /mapRoseResult /mapProp.
split=> [check_map [[res l]] sem_checker|] /=.
  rewrite eq_res.
  pose qp := {| unProp := MkRose res l |}.
  pose qp' := {| unProp := fmapRose f (MkRose res l) |}.
  by apply/(check_map qp')/semFmapSize; exists qp.
move=> sem_p qp /semFmapSize [[[res l]] [? <-]] /=; rewrite -eq_res.
by pose qp' := {| unProp := MkRose res l |}; apply: (sem_p qp').
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


(* TODO : This proof needs refactoring! *)
Lemma semShrinking_id:
  forall {prop A : Type} {H : Checkable prop}
         (shrinker : A -> list A) (x0 : A) (pf : A -> prop) (s : nat),
    semCheckerSize (shrinking shrinker x0 pf) s <->
    semCheckableSize (pf x0) s.
Proof.
admit.
(*
  move => prop A HCheck sh x pf.
  unfold semCheckableSize, shrinking, semCheckerSize, semGenSize.
  split.
  - unfold props. generalize 1000.
    case => [| n] H qp [seed Hgen]; subst.
    + apply H. apply semFmapSize. eexists.
      split. apply semPromoteSize.
      exists seed. simpl. reflexivity.
      simpl.
      by destruct ((run (checker (pf x)) s seed)) as [[res [l]]] => /=.
    + suff :
        success
          (run
             (fmap
                (fun x0 => {| unProp := joinRose (fmapRose unProp x0) |})
                (promote (@props' _ _ HCheck (S n) pf sh x))) s seed) = true.
      remember
        (run
           (fmap
              (fun x0 : Rose QProp =>
                 {| unProp := joinRose (fmapRose unProp x0) |})
              (promote (props' (S n) pf sh x))) s seed) as b.
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
  - unfold props, semGenSize. generalize 1000.
    move => n H qp [seed /runFmap [rqp [H1 H2]]].
    suff : success (run (@checker _ HCheck (pf x)) seed s) = true.
    + subst.
      remember (run (promote (props' n pf sh x)) seed s) as b. symmetry in Heqb.
      apply runPromote in Heqb; subst. simpl.
      case: n => [| n] /=;
      by destruct ((run (checker (pf x)) seed s)) as [[res [l]]] => //=.
      subst. apply H.
      by eexists; eexists.
*)
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

Lemma semImplicationSize {prop : Type} {H : Checkable prop} p b s :
  semCheckerSize (b ==> p) s <-> (b -> semCheckableSize p s).
Proof.
case: b; split=> //=; first by move/(_ refl_equal).
by move=> ? ?; rewrite (semReturnSize _ _ _) => <-.
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

Lemma semPredQPropSize :
  forall (p : G QProp) (s : nat),
    semCheckableSize p s <-> (semCheckerSize p s).
Proof.
  move=> p.
  rewrite /semCheckableSize /checker
          /testChecker /checker /testProp /semCheckerSize.
  split; move => Hqp qp Hsize; auto.
Qed.

(* begin semForAllSize *)
Lemma semForAllSize :
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : G A) (f : A -> prop) (size: nat),
    semCheckerSize (forAll gen f) size <->
    forall (a : A), a \in semGenSize gen size -> semCheckableSize (f a) size.
(* end semForAllSize *)
Proof.
  move => A prop Htest show gen pf. split => H'.
  - rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
    by apply semPrintTestCase_id in Hgen.
  - rewrite /forAll in H' *. apply semBindGen => g Hgen.
    rewrite semPrintTestCase_id. by apply H'.
Qed.

Definition unsizedChecker (c : Checker) : Prop :=
  forall s1 s2, semCheckerSize c s1 <-> semCheckerSize c s2.

(* another characterization of unsizedChecker *)
Lemma unsizedChecker_def2 {A : Type} : forall (c : Checker),
  unsizedChecker c ->
  forall s, semCheckerSize c s <-> semChecker c.
Admitted.

Lemma semPrintTestCase_id':
  forall {prop: Type} {tp : Checkable prop} (s: String.string) (p: prop),
    semGen (printTestCase s p) <--> semGen (checker p).
Admitted.

Lemma aux : forall {A prop : Type} {H : Checkable prop} `{Show A}
    (c : A -> prop),
  (forall a, unsizedChecker (checker (c a))) ->
  (forall a, unsized (printTestCase (String.append (Show.show a) newline) (c a))).
Admitted.

(* CH: We could create a super class UCheckable that includes the
       unsized assumption. And we could use sections to hide all the
       type class stuff from the paper. *)
(* begin semForAll *)
Lemma semForAll : forall {A C:Type} `{Show A, Checkable C} (g : G A) (f : A->C),
    (forall a, unsizedChecker (checker (f a))) ->
    (semChecker (forAll g f) <-> forall (a : A), semGen g a -> semCheckable (f a)).
(* end semForAll *)
Proof.
  move => A C Htest show gen pf uc.
  rewrite /semCheckable semChecker_def2. setoid_rewrite semChecker_def2.
  split => H'.
  - rewrite /forAll in H'.
    intros.  specialize (H' qp). apply H'. clear H'.
    pose proof (semBindUnsized2 gen (aux pf uc) qp) as H1. rewrite H1. clear H1.
    exists a. split. by [].
    by rewrite (semPrintTestCase_id' _ _ qp).
  - rewrite /forAll in H' *. intro qp.
    pose proof (semBindUnsized2 gen (aux pf uc) qp) as H1. rewrite H1. clear H1.
    intros [a [H1 H2]]. eapply H'. eassumption.
    move : H2. by rewrite (semPrintTestCase_id' _ _ qp).
Qed.

(* begin semImplication *)
Lemma semImplication : forall {C : Type} `{Checkable C} (b : bool) (c : C),
  semChecker (b ==> c) <-> (b -> semCheckable c).
(* end semImplication *)
Admitted.

Lemma semPredQPropNew:
  forall (p : G QProp),
    semCheckable p <-> (semChecker p).
Admitted.

(* begin semCheckableBool *)
Lemma semCheckableBool : forall (b:bool), semCheckable b <-> b.
(* end semCheckableBool *)
Admitted.

Lemma mergeForAlls :
  forall {A B prop : Type} {H : Checkable prop} `{Show A} `{Show B}
         (ga : G A) (gb : G B) (f : A -> B -> prop),
     semChecker (forAll ga (fun a => forAll gb (f a))) <->
     semChecker (forAll (genPair ga gb) (curry f)).
Proof.
  pose proof mergeBinds as mb.
Admitted.

Lemma semForAllShrink:
  forall {A prop : Type} {H : Checkable prop} `{Show A}
         (gen : G A) (f : A -> prop) shrinker (size: nat),
    semCheckerSize (forAllShrink gen shrinker f) size <->
    forall a : A, semGenSize gen size a -> semCheckableSize (f a) size.
Proof.
  move => A prop H show gen pf shrink. split.
  - rewrite /forAllShrink semBindGen.
    move=> H' a /H' Hgen. setoid_rewrite semShrinking_id in Hgen.
    setoid_rewrite semPredQPropSize in Hgen.
    by apply semPrintTestCase_id in Hgen.
  - move=> H'. rewrite /forAllShrink semBindGen. move => a g.
    rewrite semShrinking_id. apply semPredQPropSize.
    rewrite semPrintTestCase_id. by auto.
Qed.


(* equivalent Props for Checkables *)

Lemma semBool (b : bool) size : semCheckableSize b size <-> b.
Proof.
case: b; split=> //.
  by move=> _ ?; rewrite (semReturnSize _ _ _)  => <-.
move=> /(_ (MkProp (MkRose (liftBool false) (lazy nil)))).
by apply; rewrite (semReturnSize _ _ _).
Qed.

Lemma semResult:
  forall (res: Result) (size: nat),
    semCheckableSize res size <-> resultSuccessful res.
Proof.
  rewrite /semCheckableSize /checker /testResult /semCheckerSize.
  move => res. split.
  + move=> /(_ ({| unProp := returnRose res |})) /= H.
    apply H. by apply semReturnSize.
  + by move=> H [[res' l]] /semReturnSize [Heq2 Heq3]; subst.
Qed.

Lemma semUnit (t : unit) size : semCheckableSize t size <-> True.
Proof.
by split=> // _ qp /semReturnSize <-.
Qed.

Lemma semQProp (qp : QProp) size :
  semCheckableSize qp size <-> successful qp.
Proof.
by split=> [|? qp' /semReturnSize <-] //; apply; apply/semReturnSize.
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
    proposition_equiv : forall a s, proposition s a <-> semCheckableSize a s
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
    proposition s qp := successful qp = true
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
  split; intros H; by apply semPredQPropSize.
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
