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
  (* We should/(hope to) prove the Axioms in comments - 
     In some of them we may need semSize instead of semGen *)
  
  Axiom semLiftGen :
    forall {A B} (f: A -> B) (g: G A),
      semGen (liftGen f g) <-->
      fun b =>
        exists a, semGen g a /\ f a = b.
  
  Axiom semLiftGen2 :
    forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
      semSize (liftGen2 f g1 g2) s <-->
      fun b =>
        exists a1,
          exists a2, semSize g1 s a1 /\ semSize g2 s a2 /\ f a1 a2 = b.

  (* Axiom semLiftGen3 : *)
  (* forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) *)
  (*        (g1: G A1) (g2: G A2) (g3: G A3), *)
  (*   semGen (liftGen3 f g1 g2 g3) <--> *)
  (*   fun b => *)
  (*     exists a1, semGen g1 a1 /\ *)
  (*                (exists a2, semGen g2 a2 /\ *)
  (*                            (exists a3, semGen g3 a3 /\ (f a1 a2 a3) = b)). *)

  (* Axiom liftGen4_def : *)
  (* forall {A1 A2 A3 A4 B} (f:A1 -> A2 -> A3 -> A4 -> B) *)
  (*        (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4), *)
  (*   semGen (liftGen4 f g1 g2 g3 g4) <--> *)
  (*   fun b => *)
  (*     exists a1, semGen g1 a1 /\ *)
  (*                (exists a2, semGen g2 a2 /\ *)
  (*                            (exists a3, semGen g3 a3 /\ *)
  (*                                        (exists a4, semGen g4 a4 /\ *)
  (*                                                    (f a1 a2 a3 a4) = b))). *)

  (* Axiom liftGen5_def : *)
  (* forall {A1 A2 A3 A4 A5 B} (f: A1 -> A2 -> A3 -> A4 -> A5 -> B) *)
  (*        (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) (g5: G A5), *)
  (*   semGen (liftGen5 f g1 g2 g3 g4 g5) = *)
  (*   fun b => *)
  (*     exists a1, semGen g1 a1 /\ *)
  (*                (exists a2, semGen g2 a2 /\ *)
  (*                            (exists a3, semGen g3 a3 /\ *)
  (*                                        (exists a4, semGen g4 a4 /\ *)
  (*                                                    (exists a5, semGen g5 a5 /\ *)
  (*                                                                (f a1 a2 a3 a4 a5) = b)))). *)

  Axiom semSequenceGenSize:
    forall {A} (gs : list (G A)) n,
      semSize (sequenceGen gs) n <--> 
      fun l => length l = length gs /\
               forall x, List.In x (combine l gs) -> 
                         semSize (snd x) n (fst x).

  (* Axiom semFoldGen_left : *)
  (*   forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A), *)
  (*     semGen (foldGen f bs a0) <--> *)
  (*     fold_left (fun g b => fun x => exists a, g a /\ semGen (f a b) x) bs (eq a0). *)
  
  (* Axiom semFoldGen_right : *)
  (*       forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A), *)
  (*         semGen (foldGen f bs a0) <--> *)
  (*         fun an =>  *)
  (*           fold_right (fun b p => fun a_prev => exists a, semGen (f a_prev b) a /\ p a)  *)
  (*                      (eq an) bs a0. *)

  Axiom semOneof:
    forall {A} (l : list (G A)) (def : G A),
      (semGen (oneof def l)) <-->
      (fun e => (exists x, List.In x l /\ semGen x e) \/ 
                (l = nil /\ semGen def e)).

  (* Axiom semFrequency: *)
  (*   forall {A} (l : list (nat * G A)) (def : G A), *)
  (*     semGen (frequency def l) <--> *)
  (*     (fun e => (exists n, exists g, (List.In (n, g) l /\ semGen g e /\ n <> 0)) \/ *)
  (*               ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\ semGen def e)). *)

  Axiom semVectorOfSize: 
    forall {A : Type} (k : nat) (g : G A) n,
      semSize (vectorOf k g) n <--> 
      fun l => (length l = k /\ forall x, List.In x l -> semSize g n x).
  
  (* Axiom semListOf: *)
  (*   forall {A : Type} (g : G A), *)
  (*     semGen (listOf g) <--> fun l => (forall x, List.In x l -> semGen g x). *)
    
  Axiom semElements:
    forall {A} (l: list A) (def : A),
      (semGen (elements def l)) <--> (fun e => List.In e l \/ (l = nil /\ e = def)).
  
  
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

  Definition frequency {A : Type} (def : G A) (gs : list (nat * G A))
  : G A :=
    let tot := fold_left (fun t p => t + (fst p)) gs 0 in
    bindGen (choose (0, tot-1)) (fun n =>
    @snd _ _ (pick def n gs)).

  Definition vectorOf {A : Type} (k : nat) (g : G A)
  : G (list A) :=
    fold_right (fun m m' =>
                  bindGen m (fun x =>
                  bindGen m' (fun xs => returnGen (cons x xs)))
               ) (returnGen nil) (replicate k g).

  Definition listOf {A : Type} (g : G A) : G (list A) := nosimpl
    (sized (fun n => bindGen (choose (0, n)) (fun k => vectorOf k g))).

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

  Lemma semLiftGen2 :
    forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
      semSize (liftGen2 f g1 g2) s <-->
      fun b =>
        exists a1,
          exists a2, semSize g1 s a1 /\ semSize g2 s a2 /\ f a1 a2 = b.
  Proof.
    rewrite /liftGen. move => A1 A2 B f g gb b. split.
    - move => /semBindSize 
               [a1 [H1 /semBindSize [a2 [H2 /semReturnSize H3]]]]; subst.
      exists a1. exists a2. repeat split => //. 
    - move => [a1 [a2 [H [H' Heq]]]]; subst.
      apply semBindSize.
      exists a1. split => //. 
      apply semBindSize. exists a2. split => //. by apply semReturnSize.
Qed.
 

  Lemma semSequenceGenSize :
    forall {A} (gs : list (G A)) n,
      semSize (sequenceGen gs) n <--> 
           fun l => length l = length gs /\
                    forall x, List.In x (combine l gs) -> 
                              semSize (snd x) n (fst x).
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
      semSize (vectorOf k g) n <--> 
              fun l => (length l = k /\ forall x, List.In x l -> semSize g n x).
  Proof.
    move => A k g n la; unfold vectorOf; split.
    - elim : k la => /= [|k IHk] la.  
      + move=> /semReturnSize H; subst. by split.
      + move=> /semBindSize [a [H1 /semBindSize [la' [H2 /semReturnSize H3]]]].
        subst => /=. 
        have [<- HIn]: length la' = k /\ 
                       (forall x : A, List.In x la' -> semSize g n x)
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

  Lemma semFrequency:
    forall {A} (l : list (nat * G A)) (def : G A),
      semGen (frequency def l) <--> 
      (fun e => (exists n, exists g, (List.In (n, g) l /\ semGen g e /\ n <> 0)) \/
                ((l = nil \/ (forall x, List.In x l -> fst x = 0)) /\ semGen def e)).
  Proof.
    move => A l def a. unfold frequency. split.
    - move => [s /semBindSize [n [/semChooseSize /= [_ Hleq] Hsize]]].
      case: l Hleq Hsize =>  [| [n1 a1] xs] //= Hleq Hsize. 
      + right. split; auto. by exists s.
      + left. rewrite add0n in Hleq. 
        remember (n < n1) as b. destruct b. simpl in *.
  Abort.

End GenComb.