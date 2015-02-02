Require Import ZArith List ssreflect ssrbool ssrnat.

Require Import Axioms Random ModuleGen.
Require Import Ensembles.

Import Gen ListNotations.

Module Type GenDerivedInterface.

  Parameter liftGen : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter liftGen2 : forall {A1 A2 B : Type},
                         (A1 -> A2 -> B) -> G A1 -> G A2 -> G B.
  Parameter liftGen3 : forall {A1 A2 A3 B : Type},
                         (A1 -> A2 -> A3 -> B) -> G A1 -> G A2 -> G A3 -> G B.
  Parameter liftGen4 : forall {A1 A2 A3 A4 B : Type},
                         (A1 -> A2 -> A3 -> A4 -> B) ->
                         G A1 -> G A2 -> G A3 -> G A4 -> G B.
  Parameter liftGen5 : forall {A1 A2 A3 A4 A5 B : Type},
                         (A1 -> A2 -> A3 -> A4 -> A5 -> B) ->
                         G A1 -> G A2 -> G A3 -> G A4-> G A5 -> G B.
  Parameter sequenceGen: forall {A : Type}, list (G A) -> G (list A).
  Parameter foldGen :
    forall {A B : Type}, (A -> B -> G A) -> list B -> A -> G A.
  Parameter oneof : forall {A : Type}, G A -> list (G A) -> G A.
  Parameter frequency : forall {A : Type}, G A -> list (nat * G A) -> G A.
  Parameter vectorOf : forall {A : Type}, nat -> G A -> G (list A).
  Parameter listOf : forall {A : Type}, G A -> G (list A).
  Parameter elements : forall {A : Type}, A -> list A -> G A.

  (* Correctness for derived generators *)
  (* We should prove the Hypotheses in comments -
     In some of them we may need semSize instead of semGen *)

  Hypothesis semLiftGen :
    forall {A B} (f: A -> B) (g: G A),
      semGen (liftGen f g) <-->
      fun b =>
        exists a, semGen g a /\ f a = b.

  Hypothesis semLiftGenSize :
    forall {A B} (f: A -> B) (g: G A) size,
      semGenSize (liftGen f g) size <-->
      fun b =>
      exists a, semGenSize g size a /\ f a = b.

  Hypothesis semLiftGen2Size :
    forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
      semGenSize (liftGen2 f g1 g2) s <-->
      fun b =>
        exists a1,
          semGenSize g1 s a1 /\ exists a2, semGenSize g2 s a2 /\ f a1 a2 = b.

  Hypothesis semLiftGen3Size :
  forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) size,
    semGenSize (liftGen3 f g1 g2 g3) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (f a1 a2 a3) = b)).

  Hypothesis semLiftGen4Size :
  forall {A1 A2 A3 A4 B} (f:A1 -> A2 -> A3 -> A4 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) size,
    semGenSize (liftGen4 f g1 g2 g3 g4) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (exists a4, semGenSize g4 size a4 /\
                                                     (f a1 a2 a3 a4) = b))).

  Hypothesis semLiftGen5Size :
  forall {A1 A2 A3 A4 A5 B} (f: A1 -> A2 -> A3 -> A4 -> A5 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) (g5: G A5) size,
    semGenSize (liftGen5 f g1 g2 g3 g4 g5) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (exists a4, semGenSize g4 size a4 /\
                                                     (exists a5, semGenSize g5 size a5 /\
                                                                 (f a1 a2 a3 a4 a5) = b)))).

  Hypothesis semSequenceGenSize:
    forall {A} (gs : list (G A)) n,
      semGenSize (sequenceGen gs) n <-->
      fun l => length l = length gs /\
               forall x, List.In x (combine l gs) ->
                         semGenSize (snd x) n (fst x).

  (* Hypothesis semFoldGen_left : *)
  (*   forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A), *)
  (*     semGen (foldGen f bs a0) <--> *)
  (*     fold_left (fun g b => fun x => exists a, g a /\ semGen (f a b) x) bs (eq a0). *)

  (* Hypothesis semFoldGen_right : *)
  (*       forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A), *)
  (*         semGen (foldGen f bs a0) <--> *)
  (*         fun an =>  *)
  (*           fold_right (fun b p => fun a_prev => exists a, semGen (f a_prev b) a /\ p a)  *)
  (*                      (eq an) bs a0. *)

  Hypothesis semOneof:
    forall {A} (l : list (G A)) (def : G A),
      (semGen (oneof def l)) <-->
      (fun e => (exists x, List.In x l /\ semGen x e) \/
                (l = nil /\ semGen def e)).
  Hypothesis semOneofSize:
    forall {A} (l : list (G A)) (def : G A) s,
      (semGenSize (oneof def l) s) <-->
      (fun e => (exists x, List.In x l /\ semGenSize x s e) \/
                (l = nil /\ semGenSize def s e)).

  Hypothesis semFrequency:
    forall {A} (l : list (nat * G A)) (def : G A),
      semGen (frequency def l) <-->
      (fun e => (exists n, exists g, (List.In (n, g) l /\ semGen g e /\ n <> 0)) \/
                ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\ semGen def e)).
  Hypothesis semFrequencySize:
    forall {A} (l : list (nat * G A)) (def : G A) (size: nat),
      semGenSize (frequency def l) size <-->
      (fun e => (exists n, exists g, (List.In (n, g) l /\ semGenSize g size e /\ n <> 0)) \/
                ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\ semGenSize def size e)).

  Hypothesis semVectorOfSize:
    forall {A : Type} (k : nat) (g : G A) size,
      semGenSize (vectorOf k g) size <-->
      fun l => (length l = k /\ forall x, List.In x l -> semGenSize g size x).

  Hypothesis semListOfSize:
    forall (A : Type) (g : G A) (size : nat),
      semGenSize (listOf g) size <-->
      (fun l : list A =>
         length l <= size /\ (forall x : A, List.In x l -> semGenSize g size x)).

  Hypothesis semElements:
    forall {A} (l: list A) (def : A),
      (semGen (elements def l)) <--> (fun e => List.In e l \/ (l = nil /\ e = def)).
  Hypothesis semElementsSize:
    forall {A} (l: list A) (def : A) s,
      (semGenSize (elements def l) s) <--> (fun e => List.In e l \/ (l = nil /\ e = def)).

End GenDerivedInterface.

Module GenComb : GenDerivedInterface.


  Definition liftGen {A B} (f: A -> B) (a : G A)
  : G B := nosimpl
               (bindGen a (fun x =>
                returnGen (f x))).

  Definition liftGen2 {A1 A2 B}
             (C : A1 -> A2 -> B) (m1 : G A1) (m2  : G A2)
  : G B:=
    nosimpl (bindGen m1 (fun x1 => bindGen m2 (fun x2 => returnGen (C x1 x2)))).

  Definition liftGen3 {A1 A2 A3 R} (F : A1 -> A2 -> A3 -> R)
           (m1 : G A1) (m2 : G A2) (m3 : G A3)

  : G R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    returnGen (F x1 x2 x3))))).

  Definition liftGen4 {A1 A2 A3 A4 R}
             (F : A1 -> A2 -> A3 -> A4 -> R)
             (m1 : G A1) (m2 : G A2) (m3 : G A3) (m4: G A4)
  : G R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    bindGen m4 (fun x4 =>
    returnGen (F x1 x2 x3 x4)))))).

  Definition liftGen5 {A1 A2 A3 A4 A5 R}
             (F : A1 -> A2 -> A3 -> A4 -> A5 -> R)
             (m1 : G A1) (m2 : G A2) (m3 : G A3) (m4: G A4) (m5 : G A5)
  : G R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    bindGen m4 (fun x4 =>
    bindGen m5 (fun x5 =>
    returnGen (F x1 x2 x3 x4 x5))))))).


  Definition sequenceGen {A : Type} (ms : list (G A)) : G (list A) :=
    fold_right (fun m m' => bindGen m  (fun x =>
                            bindGen m' (fun xs =>
                            returnGen (x :: xs)))) (returnGen []) ms.

  Fixpoint foldGen {A B : Type} (f : A -> B -> G A) (l : list B) (a : A)
  : G A := nosimpl(
    match l with
      | [] => returnGen a
      | (x :: xs) => bindGen (f a x) (foldGen f xs)
    end).

  Definition oneof {A : Type} (def: G A) (gs : list (G A)) : G A :=
    bindGen (choose (0, length gs - 1))
            (fun n => nth n gs def).

  Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
    match n with
      | O    => nil
      | S n' => cons x (replicate n' x)
    end.

  Fixpoint pick {A : Type} (def : G A) (n : nat) (xs : list (nat * G A))
  : nat * G A :=
    match xs with
      | nil => (0, def)
      | (k, x) :: xs =>
        if (n < k) then (k, x)
        else pick def (n - k) xs
    end.

  Definition sum_fst {A : Type} (gs : list (nat * A)) : nat :=
    fold_left (fun t p => t + (fst p)) gs 0.

  Definition frequency {A : Type} (def : G A) (gs : list (nat * G A))
  : G A :=
    let tot := sum_fst gs in
    bindGen (choose (0, tot-1)) (fun n =>
    @snd _ _ (pick def n gs)).

  Definition vectorOf {A : Type} (k : nat) (g : G A)
  : G (list A) :=
    fold_right (fun m m' =>
                  bindGen m (fun x =>
                  bindGen m' (fun xs => returnGen (cons x xs)))
               ) (returnGen nil) (replicate k g).

  Definition listOf {A : Type} (g : G A) : G (list A) :=
    sized (fun n => bindGen (choose (0, n)) (fun k => vectorOf k g)).

  Definition elements {A : Type} (def : A) (l : list A) := nosimpl(
    let n := length l in
    bindGen (choose (0, n - 1)) (fun n' =>
    returnGen (List.nth n' l def))).

  Lemma semLiftGen :
    forall {A B} (f: A -> B) (g: G A),
      semGen (liftGen f g) <-->
      fun b =>
      exists a, semGen g a /\ f a = b.
  Proof.
    rewrite /liftGen. move => A B f g b. split.
    - move => [size /semBindSize [a [H1 H2]]]; subst.
      exists a. apply semReturnSize in H2.
      split => //. by exists size.
   - move => [a [[size H] Heq]]; subst.
     exists size. apply semBindSize.
     exists a. split => //. by apply semReturnSize.
  Qed.

Ltac solveLiftGenX :=
  intros; split; intros;
  repeat
    match goal with
      | [ H : exists _, _ |- _ ] => destruct H as [? [? ?]]
      | [ H : semGenSize _ _ _ |- _ ] =>
        try (apply semBindSize in H; destruct H as [? [? ?]]);
        try (apply semReturnSize in H; subst)
    end;
    [ by repeat (eexists; split; [eassumption |])
    | repeat (apply semBindSize; eexists; split; try eassumption);
        by apply semReturnSize ].

  Lemma semLiftGenSize :
    forall {A B} (f: A -> B) (g: G A) size,
      semGenSize (liftGen f g) size <-->
      fun b =>
      exists a, semGenSize g size a /\ f a = b.
  Proof. solveLiftGenX. Qed.

  Lemma semLiftGen2Size :
    forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
      semGenSize (liftGen2 f g1 g2) s <-->
      fun b =>
        exists a1,
          semGenSize g1 s a1 /\ exists a2, semGenSize g2 s a2 /\ f a1 a2 = b.
  Proof. solveLiftGenX. Qed.

  Lemma semLiftGen3Size :
  forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) size,
    semGenSize (liftGen3 f g1 g2 g3) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (f a1 a2 a3) = b)).
  Proof. solveLiftGenX. Qed.

  Lemma semLiftGen4Size  :
  forall {A1 A2 A3 A4 B} (f:A1 -> A2 -> A3 -> A4 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) size,
    semGenSize (liftGen4 f g1 g2 g3 g4) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (exists a4, semGenSize g4 size a4 /\
                                                     (f a1 a2 a3 a4) = b))).
  Proof. solveLiftGenX. Qed.


  Lemma semLiftGen5Size :
  forall {A1 A2 A3 A4 A5 B} (f: A1 -> A2 -> A3 -> A4 -> A5 -> B)
         (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) (g5: G A5) size,
    semGenSize (liftGen5 f g1 g2 g3 g4 g5) size <-->
    fun b =>
      exists a1, semGenSize g1 size a1 /\
                 (exists a2, semGenSize g2 size a2 /\
                             (exists a3, semGenSize g3 size a3 /\
                                         (exists a4, semGenSize g4 size a4 /\
                                                     (exists a5, semGenSize g5 size a5 /\
                                                                 (f a1 a2 a3 a4 a5) = b)))).
  Proof. solveLiftGenX. Qed.

  Lemma semSequenceGenSize :
    forall {A} (gs : list (G A)) n,
      semGenSize (sequenceGen gs) n <-->
           fun l => length l = length gs /\
                    forall x, List.In x (combine l gs) ->
                              semGenSize (snd x) n (fst x).
  Proof.
    move=> A gs n la. rewrite /sequenceGen. split.
    - elim : gs la => /= [| g gs IHgs] la.
      + by move/semReturnSize => H; subst.
      + move => /semBindSize [a [H1 /semBindSize
                                  [la' [H2 /semReturnSize H3]]]]; subst.
        move: IHgs => /(_ la' H2) [<- HIn].
        split=> //= x [H | H]; subst => //=. by apply HIn => /=.
    - elim : gs la => /= [| g gs IHgs].
      + move => [|a la] [//= Heq H].
          by apply semReturnSize.
      + move => [|a la] [//= [Heq] HIn]; subst.
        apply semBindSize.
        exists a. split.
        * apply (HIn (a, g)). by left.
        * apply semBindSize. exists la.
          split => //=.
          apply IHgs. split => // x H. apply HIn; by right.
            by apply semReturnSize.
  Qed.

  Lemma semVectorOfSize:
    forall {A : Type} (k : nat) (g : G A) n,
      semGenSize (vectorOf k g) n <-->
              fun l => (length l = k /\ forall x, List.In x l -> semGenSize g n x).
  Proof.
    move => A k g n la; unfold vectorOf; split.
    - elim : k la => /= [|k IHk] la.
      + move=> /semReturnSize H; subst. by split.
      + move=> /semBindSize [a [H1 /semBindSize [la' [H2 /semReturnSize H3]]]].
        subst => /=.
        have [<- HIn]: length la' = k /\
                       (forall x : A, List.In x la' -> semGenSize g n x)
          by apply IHk.
      split => // x [H | H]; subst => //.
      by apply HIn.
   - elim : k la => /= [|k IHk] la [Heq Hgen].
     + destruct la => //. by apply semReturnSize.
     + destruct la=> //. simpl in *.
       move: Heq => [Heq]; subst.
       apply semBindSize.
       exists a. split.
       * apply Hgen => //; by left.
       * apply semBindSize.
         exists la =>//. split => //; last by apply semReturnSize.
         apply IHk. split => //.
         move => x HIn. apply Hgen. by right.
  Qed.

  Lemma semListOfSize:
    forall {A : Type} (g : G A) size,
      semGenSize (listOf g) size <-->
      fun l => length l <= size /\ (forall x, List.In x l -> semGenSize g size x).
  Proof.
    move => A g size la; unfold listOf; split.
    - move => /semSizedSize /semBindSize
               [n' [/semChooseSize [/= H1 H2] /semVectorOfSize [Heq H3]]]; subst.
      by intros; split; auto.
    - move => [H1 H2]. apply semSizedSize. apply semBindSize.
      exists (length la).
      split; first by apply semChooseSize => //=.
      apply semVectorOfSize. split => //.
  Qed.

  Lemma In_nth_exists:
    forall {A} (l: list A) x def,
      List.In x l -> exists n, nth n l def = x /\ (n < length l)%coq_nat.
  Proof.
    move => A l x def. elim : l => [| a l IHl] //=.
    move => [H | /IHl [n [H1 H2]]]; subst.
    - exists 0. split => //. omega.
    - exists n.+1. split => //. omega.
  Qed.

  Lemma semOneof:
    forall {A} (l : list (G A)) (def : G A),
      (semGen (oneof def l)) <-->
      (fun e => (exists x, List.In x l /\ semGen x e) \/
                (l = nil /\ semGen def e)).
  Proof.
    move=> A l def a. unfold oneof. split.
    - move => [s /semBindSize [n [/semChooseSize [Hleq1 Hleq2] Hnth]]].
      case: l Hleq2 Hnth => [| g gs] //= /leP Hleq2 Hnth.
      + rewrite sub0n in Hleq2. apply le_n_0_eq in Hleq2; subst.
        right. split => //. by exists s.
      + left. rewrite subn1 NPeano.Nat.pred_succ in Hleq2.
        case: n Hleq1 Hleq2 Hnth => [_ _ | n Hleq1 Hleq2] Hnth.
        * exists g. split; auto. by exists s.
        * exists (nth n gs def). split; last by exists s.
          right. by apply nth_In.
    - move => [[g [Hin [s Hsem]]] | [Heq [s Hsem]]]; subst.
      + exists s. apply semBindSize.
        destruct (In_nth_exists _ _ def Hin) as [n [Hnth Hl]]; subst.
        exists n. split => //. apply semChooseSize. split => //.
        simpl. apply/leP.
        rewrite subn1. apply NPeano.Nat.le_succ_le_pred. omega.
      + exists s. apply semBindSize. exists 0. split => //.
        apply semChooseSize. split => //.
  Qed.

  Lemma semOneofSize:
    forall {A} (l : list (G A)) (def : G A) s,
      (semGenSize (oneof def l) s) <-->
      (fun e => (exists x, List.In x l /\ semGenSize x s e) \/
                (l = nil /\ semGenSize def s e)).
  Proof.
    move => A l def s a.  unfold oneof. split.
    - move => /semBindSize [n [/semChooseSize [Hleq1 Hleq2] Hnth]].
      case: l Hleq2 Hnth => [| g gs] //= /leP Hleq2 Hnth.
      + rewrite sub0n in Hleq2. apply le_n_0_eq in Hleq2; subst.
        right. by split => //.
      + left. rewrite subn1 NPeano.Nat.pred_succ in Hleq2.
        case: n Hleq1 Hleq2 Hnth => [_ _ | n Hleq1 Hleq2] Hnth.
        * exists g. split => //; by auto.
        * exists (nth n gs def). split; last by auto.
          right. by apply nth_In.
    - move => [[g [Hin Hsem]] | [Heq Hsem]]; subst.
      +apply semBindSize.
        destruct (In_nth_exists _ _ def Hin) as [n [Hnth Hl]]; subst.
        exists n. split => //. apply semChooseSize. split => //.
        simpl. apply/leP.
        rewrite subn1. apply NPeano.Nat.le_succ_le_pred. omega.
      + apply semBindSize. exists 0. split => //.
        apply semChooseSize. split => //.
  Qed.


  Lemma semElements :
    forall {A} (l: list A) (def : A),
      (semGen (elements def l)) <-->
      (fun e => List.In e l \/ (l = nil /\ e = def)).
  Proof.
    unfold elements. move => A l def a. split.
    - move => [s /semBindSize [n [/semChooseSize [/= Hleq1 Hleq2]
                                   /semReturnSize H2]]]; subst.
      case: l Hleq1 Hleq2 => [_ _ | a l /= Hleq1 Hleq2].
      + right. split => //. by case: n.
      + left. case: n Hleq1 Hleq2 => [|n] _ /leP Hleq2; auto.
        right. apply nth_In. rewrite subn1 in Hleq2. omega.
    - move => [H | [H1 H2]]; subst.
      + exists 0. apply semBindSize.
        destruct (In_nth_exists _ _ def H) as [n [Hnth Hlen]]; subst.
        exists n. split; last by apply semReturnSize.
        apply semChooseSize. split => //. apply/leP.
        unfold lt in *. rewrite subn1. omega.
     + exists 0. apply semBindSize. exists 0.
       split; last by apply semReturnSize. apply semChooseSize. split => //.
  Qed.

  Lemma semElementsSize :
    forall {A} (l: list A) (def : A) s,
      (semGenSize (elements def l) s) <-->
      (fun e => List.In e l \/ (l = nil /\ e = def)).
  Proof.
    move => A l def a. split.
    - move => Hsize. apply semElements. eexists; eassumption.
    - move => [HIn | [Hemp Heq]]; unfold elements.
      + apply semBindSize.
        destruct (In_nth_exists _ _ def HIn) as [n [Hnth Hlen]]; subst.
        exists n. split; last by apply semReturnSize.
        apply semChooseSize. split => //. apply/leP.
        unfold lt in *. rewrite subn1. omega.
     + subst; apply semBindSize. exists 0.
       split; last by apply semReturnSize. apply semChooseSize. split => //.
  Qed.


(* A rather long frequency proof, probably we can do better *)

  Lemma not_lt : forall n m, (false = (n < m)) -> (m <= n).
  Proof.
    move => n m. by elim: n m=> [| n IHn]; case.
  Qed.

  Lemma sum_fst_unfold:
    forall A x (a : A) l,
      sum_fst ((x, a) :: l) = x + sum_fst l.
  Proof.
    unfold sum_fst. generalize 0.
    move=> n A x a l.
    elim : l n x a =>  [|y ys IHxs] n x a.
    - by rewrite addnC.
    - simpl. specialize (IHxs (n + fst y) x a). simpl in IHxs.
        by rewrite -IHxs addnAC.
  Qed.

  Lemma sum_fst_zero:
    forall {A} (l: list (nat * A)),
      sum_fst l = 0 <->
      (forall x, List.In x l -> fst x = 0).
  Proof.
    move=> A l.
    split.
    { elim : l => //= x xs IHxs Heq. destruct x as [a n].
      rewrite sum_fst_unfold in Heq.
      move/plus_is_O : Heq => [H1 /IHxs H2]; subst.
      move => x [Heq | HIn]; subst => //; auto. }
    { elim l => // x xs IHxs H. destruct x as [a n].
      rewrite sum_fst_unfold. apply NPeano.Nat.eq_add_0. split.
      - apply (H (a, n)). by constructor.
      - apply IHxs. move=> x' HIn. apply H. constructor(exact HIn). }
  Qed.

  Lemma pick_def :
    forall {A} (l: list (nat * G A)) n def,
      sum_fst l <= n ->
      pick def n l = (0, def).
  Proof.
    move=> A l n def Hleq.
    elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
    rewrite sum_fst_unfold in Hleq.
    remember (n < i). case: b Heqb => Heqb; symmetry in Heqb.
    - have : (i + sum_fst l) < i by eapply (leq_ltn_trans); eassumption.
      rewrite -ltn_subRL. by have -> : forall i, (i - i) = 0 by elim.
    - apply IHl. rewrite -(leq_add2r i) subnK.
        by rewrite addnC. by apply/not_lt.
  Qed.


  Lemma pick_exists :
    forall {A} (l: list (nat * G A)) n def,
      n <  sum_fst l <->
      exists x, List.In x l /\ pick def n l = x /\ fst x <> 0.
  Proof.
    move => A l n def. split.
    - move => Hlt.
      elim : l n Hlt => //. case => i p xs IHxs n Hlt.
      rewrite sum_fst_unfold in Hlt.
      move/(_ (n-i)) : IHxs => IHxs. simpl.
      remember (n < i). case: b Heqb => [Heqb | /not_lt Heqb].
      + exists (i, p). split => //=. by left.  split => //=.
        move => contra; subst. by rewrite ltn0 in Heqb.
      + rewrite -(ltn_add2r i) [X in _  < X]addnC subnK // in IHxs.
        move/(_ Hlt) : IHxs => [x [H1 [H2 H3]]].
        by exists x; split; [right | split].
    - move => [x [HIn [Hpick Hneq]]].
      remember (n < sum_fst l).
      case: b  Heqb => //= /not_lt/pick_def H.
      rewrite H in Hpick. rewrite -Hpick //= in Hneq.
  Qed.

  Lemma pick_In :
    forall {A} (l: list (nat * G A)) x def,
      List.In x l /\ fst x <> 0 ->
      exists n, pick def n l = x.
  Proof.
    move => A l x def [HIn Hfst].
    elim : l HIn => //=. case => //= i g xs IHxs [H1 | H2]; subst.
    + exists 0. simpl in *.
      have H : 0 < i by  elim : i Hfst IHxs => //=.
      rewrite H.
        by split => //=.
    + move/(_ H2) : IHxs => [n Hpick].
      exists (n + i). rewrite -[X in _ < X]add0n ltn_add2r ltn0.
        by rewrite  -[X in _ - X]add0n subnDr subn0.
  Qed.

  Lemma semFrequencySize:
    forall {A} (l : list (nat * G A)) (def : G A) (size: nat),
      semGenSize (frequency def l) size <-->
      (fun e =>
         (exists n, exists g,
                      (List.In (n, g) l /\ semGenSize g size e /\ n <> 0)) \/
         ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\
          semGenSize def size e)).
  Proof.
    move=> A l def s a.
    rewrite /frequency //=.
    split =>
    [ /semBindSize [n [/semChooseSize /= [_ Hleq] Hsize]]
    | H ].
    { destruct (sum_fst l) eqn:Heq.
      - right.
        have Heq2: (pick def n l) = (0, def) by apply pick_def; rewrite Heq.
        rewrite Heq2 /= in Hsize. move/sum_fst_zero : Heq => HIn.
        destruct n as [| n]; try discriminate; clear Hleq.
        split => //. by right.
      - rewrite subn1 -pred_Sn in Hleq.
        have /(pick_exists _ _ def) [[n' g] [H1 [H2 H3]]] : n < sum_fst l
          by rewrite Heq; move: Hleq => /leP Hleq; apply/ltP; omega.
        left. exists n'. exists g. repeat split => //. by rewrite H2 in Hsize. }
    { move : H => [[n [g [H1 [H2 H3]]]] | [[H1 | H1] H2]].
      - apply semBindSize.
        have [m H] : exists m : nat, pick def m l = (n, g)
                       by apply pick_In; split => //.
        exists m. rewrite H. split => //.
        apply semChooseSize; split => //=.
        have Hlt: m < sum_fst l
        by apply/(pick_exists _ _ def)=> //=; exists (n, g).
        rewrite -(leq_add2r 1) addn1 subnK. by auto.
        by case: (sum_fst l) Hlt => //=.
     - subst. rewrite sub0n. apply semBindSize; exists 0. split => //=.
       apply semChooseSize => //.
     - apply semBindSize. exists 0. split; first by apply semChooseSize.
        elim: l H1 => //=. case => n p l IHl H1.
        move/(_ (n, p)): (H1) => //= H. rewrite H => //=.
        rewrite subn0; auto. by left. }
  Qed.

  Lemma semFrequency:
    forall {A} (l : list (nat * G A)) (def : G A),
      semGen (frequency def l) <-->
      (fun e => (exists n, exists g,
                             (List.In (n, g) l /\ semGen g e /\ n <> 0)) \/
                ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\
                 semGen def e)).
  Proof.
    move => A l def a. split.
    - move => [s /semFrequencySize [[n [g [H1 [H2 H3]]]] | [H1 H2]]].
      + left. exists n. exists g. repeat split => //. eexists; eassumption.
      + right. split => //. eexists; eassumption.
    - move => [[n [g [H1 [[s H2] H3]]]] | [[H1 | H1] [s H2]]]; subst;
              exists s; apply semFrequencySize.
      + left. exists n; exists g. split => //.
      + right. split => //. by left.
      + right. split => //. by right.
Qed.

End GenComb.
