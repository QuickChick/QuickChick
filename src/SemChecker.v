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
Lemma semChecker_def2 c :
  semChecker c <-> (forall qp, semGen c qp -> successful qp = true).
Proof.
  rewrite /semChecker /semCheckerSize /semGen. split; intro H.
  - intros. destruct H0 as [s H0]. eapply (H s). tauto.
  - intros. apply H. exists s. by split.
Qed.

Lemma one_more_for_maximes_library a b x (f : a -> b) (A : set a) :
  x \in A -> f x \in (f @: A).
Proof.
  intros. unfold imset. exists x. split; by [].
Qed.

(* CH: This is the definition of Checker I would like to use *)
Lemma semChecker_def3 c :
  semChecker c <-> (successful @: semGen c \subset [set true]).
Proof.
  rewrite semChecker_def2. split; intro H.
(*  CH: why can't I rewrite with semFmap directly? See tentative instances below *)
  - intros b H'. unfold imset, bigcup in H'.
    destruct H' as [qp [H1 H2]]. apply H in H1. by rewrite H1 in H2.
  - intros. unfold set_incl in H. specialize (H (successful qp)).
    unfold set1 in H. symmetry. apply H. clear H.
    by apply one_more_for_maximes_library.
Qed.

(* Maps a Checkable to a Prop i.e. gives an equivalent proposition to the
   property under test *)
(* begin semCheckable *)
Definition semCheckable {A} `{Checkable A} (a : A) : Prop := semChecker (checker a).
(* end semCheckable *)
(* begin semCheckableSize *)
Definition semCheckableSize {A} `{Checkable A} (a : A) (s : nat) : Prop :=
  semCheckerSize (checker a) s.
(* end semCheckableSize *)

Lemma mapTotalResult_id {C} `{Checkable C} (f : Result -> Result) (c : C) s :
    (forall res, resultSuccessful res = resultSuccessful (f res)) ->
    (semCheckerSize (mapTotalResult f c) s <-> semCheckableSize c s).
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

Lemma semCallback_id {C} `{Checkable C} (cb : Callback) (c : C) (s : nat) :
    semCheckerSize (callback cb c) s <-> semCheckableSize c s.
Proof.
  rewrite /callback.
  split; move => H'.
  - apply mapTotalResult_id in H' => //;
    by move => [? ? ? ? ? ?].
  - apply mapTotalResult_id => //;
    by move => [? ? ? ? ? ?].
Qed.

Lemma semWhenFail_id {C} `{Checkable C} (str : String.string) (c : C) s :
    semCheckerSize (whenFail str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /whenFail semCallback_id.
Qed.

Lemma semPrintTestCase_id {C} `{Checkable C} (str : String.string) (c : C) s :
    semCheckerSize (printTestCase str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /printTestCase semCallback_id.
Qed.

(* TODO : This proof needs refactoring! *)
Lemma semShrinking_id {C A} {HCheck : Checkable C}
         (sh : A -> list A) (x : A) (pf : A -> C) (s : nat) :
    semCheckerSize (shrinking sh x pf) s <->
    semCheckableSize (pf x) s.
Proof.
Admitted.
(*
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

Lemma semCover_id {C} `{Checkable C} (b: bool) (n: nat)
                       (str : String.string) (c : C) (s : nat) :
    semCheckerSize (cover b n str c) s <-> semCheckableSize c s.
Proof.
  split.
  - rewrite /cover. case: b => //.
    move => H1. apply mapTotalResult_id in H1 => //.
      by move => [? ? ? ? ? ?].
  - move => H1. rewrite /cover. case: b => //.
    apply mapTotalResult_id => //.
      by move => [? ? ? ? ? ?].
Qed.

Lemma semClassify_id {C} `{Checkable C} (b: bool) (str : String.string)
          (c : C) (s : nat) :
    semCheckerSize (classify b str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /classify semCover_id.
Qed.

Lemma semLabel_id {C} `{Checkable C} (str : String.string) (c : C) (s : nat) :
    semCheckerSize (label str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /label semClassify_id.
Qed.

Lemma semCollect_id {C} `{Checkable C} (str : String.string) (c : C) (s : nat) :
    semCheckerSize (collect str c) s <-> semCheckableSize c s.
Proof.
  by rewrite /collect semLabel_id.
Qed.

Open Scope Checker_scope.

Lemma semImplicationSize {C} `{Checkable C} (c : C) (b : bool) s :
  semCheckerSize (b ==> c) s <-> (b -> semCheckableSize c s).
Proof.
  case: b; split=> //=; first by move/(_ refl_equal).
  by move=> ? ?; rewrite (semReturnSize _ _ _) => <-.
Qed.

(* equivalences for other combinators *)

Lemma semReturnGen (qp : QProp) (s: nat) :
    semCheckerSize (returnGen qp) s <-> semCheckableSize qp s.
Proof.
  rewrite /semChecker. split;
  move => H qp' /semReturnSize Hprop; subst;
  apply H; by apply semReturnSize.
Qed.

Lemma semBindGen {A} (gen : G A) (f : A -> Checker) (s: nat):
    semCheckerSize (bindGen gen f) s <->
    forall a, semGenSize gen s a -> semCheckerSize (f a) s.
Proof.
  unfold semCheckerSize. split.
  - move => H a Hsize qp Hsize'. eapply H.
    apply semBindSize.  eexists; split; eassumption.
  - move => H qp /semBindSize [a [H1 H2]]. eapply H; eassumption.
Qed.

Lemma semPredQPropSize (c : Checker) (s : nat) :
    semCheckableSize c s <-> (semCheckerSize c s).
Proof.
  rewrite /semCheckableSize /checker
          /testChecker /checker /testProp /semCheckerSize.
  split; move => Hqp qp Hsize; auto.
Qed.

(* begin semForAllSize *)
Lemma semForAllSize {A C} `{Show A, Checkable C} (g : G A) (f : A -> C) (s:nat) :
  semCheckerSize (forAll g f) s <->
  forall (a : A), a \in semGenSize g s -> semCheckableSize (f a) s.
(* end semForAllSize *)
Proof.
split=> H'.
- rewrite /forAll in H'. move/semBindGen : H' => H' a /H' Hgen.
  by apply semPrintTestCase_id in Hgen.
- rewrite /forAll in H' *. apply semBindGen => g' Hgen.
  rewrite semPrintTestCase_id. by apply H'.
Qed.

(* CH: any way to relate this to generators and unsizedness of generators?
   Yes, unsizedChecker should be defined in terms of unsized and semChecker' *)

Definition genChecker c := fmap successful c.

Definition unsizedChecker (c : Checker) : Prop := unsized (genChecker c).

(* alternative definitions
Definition unsizedChecker (c : Checker) : Prop :=
  forall s1 s2, semCheckerSize c s1 <-> semCheckerSize c s2.

(* another characterization of unsizedChecker *)
Lemma unsizedChecker_def2 {A : Type} : forall (c : Checker),
  unsizedChecker c ->
  forall s, semCheckerSize c s <-> semChecker c.
Proof.
  intros. split; intro H'.
  - intro s'. rewrite H. eassumption.
  - by apply H'.
Qed.
*)

Lemma imset_id' T (A : set T) f : (forall x, f x = x) -> f @: A <--> A.
Proof.
  rewrite /imset /bigcup => H x. split.
  - move => [y [H1 H2]]. rewrite H in H2. inversion H2. subst. assumption.
  - move => H1. eexists. split. eassumption. by rewrite H.
Qed.

Lemma semMapTotalResult_id {C} `{Checkable C} f (c : C) :
    (forall r, f r = r) ->
    (semGen (mapTotalResult f c) <--> semGen (checker c)).
Proof.
  intros.
  rewrite /mapTotalResult /mapRoseResult /mapProp.
  rewrite semFmap. apply imset_id'. intros [?]. by rewrite fmapRose_id.
Qed.

Lemma another_one_for_maxime a b (f g : a -> b) (A : set a) :
  (forall x, f x = g x) ->
  f @: A <--> g @: A.
Proof.
  rewrite /imset /bigcup /set1. move => H x.
  split => [[i [H1 H2]] | [i [H1 H2]]]; eexists; split;
           try eassumption. congruence. congruence.
Qed.  

Lemma semPrintTestCase_id' {C} `{Checkable C} (s: String.string) (c : C) :
    successful @: semGen (printTestCase s c) <--> successful @: semGen (checker c).
Proof.
  intros. unfold printTestCase, callback.
  rewrite /mapTotalResult /mapRoseResult /mapProp.
  rewrite semFmap. rewrite -imset_comp. apply another_one_for_maxime.
  simpl. move => [[[? ? ? ? ? ?] ?]]. reflexivity.
Qed.

(* CH: almost the same as before, should refactor at some point *)
Lemma semPrintTestCase_id'' {C} `{Checkable C} (str : String.string) (c : C) s :
    successful @: semGenSize (printTestCase str c) s <-->
    successful @: semGenSize (checker c) s.
Proof.
  intros. unfold printTestCase, callback.
  rewrite /mapTotalResult /mapRoseResult /mapProp.
  rewrite semFmapSize. rewrite -imset_comp. apply another_one_for_maxime.
  simpl. move => [[[? ? ? ? ? ?] ?]]. reflexivity.
Qed.

Lemma unsized_printTestCase {A C} `{Checkable C} `{Show A} (c : A -> C) :
  (forall a, unsizedChecker (checker (c a))) ->
  (forall a, unsizedChecker
               (printTestCase (String.append (Show.show a) newline) (c a))).
Proof.
  rewrite /unsizedChecker /unsized /genChecker. setoid_rewrite semFmapSize.
  move => H' a s1 s2. specialize (H' a s1 s2).
  by do 2 rewrite semPrintTestCase_id''.
Qed.

(* This seems like a better way to prove semForAll *)
Lemma semForAll_aux {A C} `{Show A, Checkable C} (g : G A) (f : A->C):
    (forall a, unsizedChecker (checker (f a))) ->
  successful @: semGen (forAll g f) <-->
  (\bigcup_(a in semGen g) successful @: (semGen (checker (f a)))).
Proof.
  intros. rewrite /forAll.
  rewrite -semFmap. rewrite semFmapBind.
  rewrite semBindUnsized2.
  apply eq_bigcupr => a.
  rewrite semFmap.
  apply semPrintTestCase_id'.
  by apply unsized_printTestCase.
Qed.

Lemma subset_trans a (A1 A2 A3 : set a) :
  A1 \subset A2 ->
  A2 \subset A3 ->
  A1 \subset A3.
Proof.
  rewrite /set_incl. move => H12 H23. by eauto 3.
Qed.

Instance xxx a (x:set a) : Morphisms.Proper (Morphisms.respectful set_eq
                                     (Basics.flip Basics.impl))
                                  (set_incl x).
Admitted.

Require Import Relations.
Instance yyy a (x: relation (set a)) : Morphisms.Proper
               (Morphisms.respectful set_eq
                  (Morphisms.respectful x (Basics.flip Basics.impl)))
               set_incl.
Admitted.

Lemma here_is_one_more a b (x:a) (A : set a) (f:a->set b) :
  x \in A ->
  f x \subset \bigcup_(x in A) f x.
Proof.
  rewrite /set_incl /bigcup. by eauto 3.
Qed.

(* CH: We could create a super class UCheckable that includes the
       unsized assumption. And we could use sections to hide all the
       type class stuff from the paper. *)
(* CH: This will be affected by upcoming refactoring;
       proving it like this only because it appears in ITP submission *)
(* begin semForAll *)
Lemma semForAll {A C:Type} `{Show A, Checkable C} (g : G A) (f : A->C) :
    (forall a, unsizedChecker (checker (f a))) ->
    (semChecker (forAll g f) <-> forall (a : A), semGen g a -> semCheckable (f a)).
(* end semForAll *)
Proof.
  move=> uc.
  rewrite /semCheckable semChecker_def3. setoid_rewrite semChecker_def3.
  rewrite /genChecker.
  split => H'.
  - intros. move : H'. apply subset_trans.
    rewrite semForAll_aux; [| by []].
    by apply here_is_one_more with
       (f:= fun x => successful @: semGen (checker (f x))).
  - rewrite semForAll_aux; [| by []].
    unfold set_incl in *. intros b [x [H1 H2]].
    eapply H'; eassumption.
Qed.

Lemma subset_refl T (A : set T) : A \subset A.
Proof. by rewrite /set_incl. Qed.

(* begin semImplication *)
Lemma semImplication {C} `{Checkable C} (b : bool) (c : C) :
  semChecker (b ==> c) <-> (b -> semCheckable c).
(* end semImplication *)
Proof.
  rewrite /semCheckable !semChecker_def3.
  split => [H' b'|].
  - by rewrite b' in H'.
  - case b; simpl => H'. by apply H'.
    rewrite semReturn /imset bigcup_set1. by apply subset_refl.
Qed.

Lemma semPredQPropNew:
  forall (p : G QProp),
    semCheckable p <-> (semChecker p).
Proof. by rewrite /semCheckable /checker. Qed.

(* begin semCheckableBool *)
Lemma semCheckableBool (b : bool) : semCheckable b <-> b.
(* end semCheckableBool *)
Proof. (* CH: brute-force, please fix *)
  rewrite /semCheckable /checker semChecker_def3 /checker. simpl.
  split; setoid_rewrite semReturn.
    rewrite /imset bigcup_set1. simpl.
    destruct b. by []. simpl; move => H. unfold set_incl in H.
      unfold set1 in H. specialize (H false Coq.Init.Logic.eq_refl).
      inversion H.
    intro Hb. rewrite Hb. simpl. rewrite /imset bigcup_set1.
      by apply subset_refl.
Qed.

Definition uncurry {A B C : Type} (f : A * B -> C) (a : A) (b : B) := f (a,b).

Lemma mergeBinds' :
  forall A B C (ga : G A) (gb : G B) (f : A * B -> G C),
    semGen (bindGen ga (fun x => bindGen gb ((uncurry f) x))) <-->
    semGen (bindGen (genPair ga gb) f).
Admitted. (* should be immediate from mergeBinds and curry-uncurry iso *)

Lemma mergeForAlls {A B C : Type} `{Checkable C} `{Show A} `{Show B}
         (ga : G A) (gb : G B) (f : A -> B -> C) :
     semChecker (forAll ga (fun a => forAll gb (f a))) <->
     semChecker (forAll (genPair ga gb) (curry f)).
Proof.
  rewrite /forAll.
  do 2 rewrite semChecker_def3.
  split; rewrite -mergeBinds'. (* would like to rewrite before split though *)
Admitted.

Lemma semForAllShrink:
  forall {A C} `{Checkable C} `{Show A}
         (gen : G A) (f : A -> C) shrinker (size: nat),
    semCheckerSize (forAllShrink gen shrinker f) size <->
    forall a : A, semGenSize gen size a -> semCheckableSize (f a) size.
Proof.
  move => A C H show gen pf shrink. split.
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
  forall {A C} {H1 : Show A} {H2 : Arbitrary A} {H3 : Checkable C}
         (f : A -> C) (size: nat),
    semCheckableSize f size <->
    forall (a : A), semGenSize arbitrary size a -> semCheckableSize (f a) size.
Proof.
  move=> A C H1 H2 H3 f.
  rewrite /semCheckable /checker /testFun.
  split.
  - move => /semForAllShrink H' a' /H' Gen. by auto.
  - move => H'. apply semForAllShrink => a' /H' Hgen. by auto.
Qed.

Lemma semPolyFun:
  forall {C : Type -> Type} {H : Checkable (C nat)} (f : forall T, C T)
         (size : nat),
    (semCheckableSize f size) <-> (semCheckableSize (f nat) size).
Proof.
  move => C H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
  by rewrite semPrintTestCase_id.
Qed.

Lemma semPolyFunSet:
  forall {C : Set -> Type} {H : Checkable (C nat)} (f : forall T, C T) (size: nat),
    (semCheckableSize f size) <->  (semCheckableSize (f nat) size).
Proof.
  move => C H f s. rewrite /semCheckableSize {2}/checker /testPolyFun.
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

Program Instance proveGenProp {C} `{Provable C} :
  Provable (G C) :=
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

Program Instance proveFun {A C: Type} `{Arbitrary A} `{Show A}
        `{Provable C}: Provable (A -> C) :=
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

Program Instance provePolyFun {C : Type -> Type} `{Provable (C nat)} :
  Provable (forall T, C T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFun.
  - move=> /semPolyFun H'. by apply proof.
Qed.

Program Instance provePolyFunSet {C : Set -> Type} `{Provable (C nat)} :
  Provable (forall T, C T) :=
  {
    proposition s f := proposition s (f nat)
  }.
Next Obligation.
  destruct H0 as [semP proof]. rewrite /proposition. split.
  - move=> /proof H'. by apply semPolyFunSet.
  - move=> /semPolyFunSet H'. by apply proof.
Qed.
