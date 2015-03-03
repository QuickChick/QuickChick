Require Import ZArith.
Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq bigop.

Require Import Random GenLow.
Require Import Sets.

Import GenLow.

(* High-level Generators *)

Module Type GenHighInterface.

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
    semGen (liftGen f g) <--> f @: semGen g.

Hypothesis semLiftGenSize :
  forall {A B} (f: A -> B) (g: G A) size,
    semGenSize (liftGen f g) size <--> f @: semGenSize g size.

Hypothesis semLiftGen2Size :
  forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
    semGenSize (liftGen2 f g1 g2) s <-->
    f @2: (semGenSize g1 s, semGenSize g2 s).

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
    [set l | length l = length gs /\
      List.Forall2 (fun y => semGenSize y n) gs l].

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
      if l is nil then semGen def else \bigcup_(x in l) semGen x.

Hypothesis semOneofSize:
  forall {A} (l : list (G A)) (def : G A) s,
    (semGenSize (oneof def l) s) <-->
      if l is nil then semGenSize def s else \bigcup_(x in l) semGenSize x s.

Hypothesis semFrequency:
  forall {A} (l : list (nat * G A)) (def : G A),
    semGen (frequency def l) <-->
      let l' := [seq x <- l | x.1 != 0] in
      if l' is nil then semGen def else
      \bigcup_(x in l') semGen x.2.

Hypothesis semFrequencySize:
  forall {A} (l : list (nat * G A)) (def : G A) (size: nat),
    semGenSize (frequency def l) size <-->
      let l' := [seq x <- l | x.1 != 0] in
      if l' is nil then semGenSize def size else
      \bigcup_(x in l') semGenSize x.2 size.

Hypothesis semVectorOfSize:
  forall {A : Type} (k : nat) (g : G A) size,
    semGenSize (vectorOf k g) size <-->
    [set l | length l = k /\ l \subset semGenSize g size].

Hypothesis semListOfSize:
  forall (A : Type) (g : G A) (size : nat),
    semGenSize (listOf g) size <-->
    [set l | length l <= size /\ l \subset semGenSize g size].

Hypothesis semElements:
  forall {A} (l: list A) (def : A),
    (semGen (elements def l)) <--> if l is nil then [set def] else l.

Hypothesis semElementsSize:
  forall {A} (l: list A) (def : A) s,
    (semGenSize (elements def l) s) <--> if l is nil then [set def] else l.

End GenHighInterface.

Module GenHigh : GenHighInterface.


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
  foldr (fun m m' => bindGen m  (fun x =>
                          bindGen m' (fun xs =>
                          returnGen (x :: xs)))) (returnGen [::]) ms.

Fixpoint foldGen {A B : Type} (f : A -> B -> G A) (l : list B) (a : A)
: G A := nosimpl(
  match l with
    | [::] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end).

Definition oneof {A : Type} (def: G A) (gs : list (G A)) : G A :=
  bindGen (choose (0, length gs - 1)) (nth def gs).

Fixpoint pick {A : Type} (def : G A) (xs : list (nat * G A)) n : nat * G A :=
  match xs with
    | nil => (0, def)
    | (k, x) :: xs =>
      if (n < k) then (k, x)
      else pick def xs (n - k)
  end.

Definition sum_fst {A : Type} (gs : list (nat * A)) : nat :=
  foldl (fun t p => t + (fst p)) 0 gs.

Definition frequency {A : Type} (def : G A) (gs : list (nat * G A))
: G A :=
  let tot := sum_fst gs in
  bindGen (choose (0, tot-1)) (fun n =>
  @snd _ _ (pick def gs n)).

Definition vectorOf {A : Type} (k : nat) (g : G A)
: G (list A) :=
  foldr (fun m m' =>
                bindGen m (fun x =>
                bindGen m' (fun xs => returnGen (cons x xs)))
             ) (returnGen nil) (nseq k g).

Definition listOf {A : Type} (g : G A) : G (list A) :=
  sized (fun n => bindGen (choose (0, n)) (fun k => vectorOf k g)).

Definition elements {A : Type} (def : A) (l : list A) := nosimpl(
  let n := length l in
  bindGen (choose (0, n - 1)) (fun n' =>
  returnGen (List.nth n' l def))).

Lemma semLiftGen {A B} (f: A -> B) (g: G A) :
  semGen (liftGen f g) <--> f @: semGen g.
Proof.
rewrite imset_bigcup; apply: eq_bigcupr => size.
by rewrite semBindSize (eq_bigcupr _ (fun a => semReturnSize size (f a))).
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

Lemma semLiftGen2Size {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s :
  semGenSize (liftGen2 f g1 g2) s <-->
  f @2: (semGenSize g1 s, semGenSize g2 s).
Proof. admit. Qed.

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

Lemma Forall2_cons T U (P : T -> U -> Prop) x1 s1 x2 s2 : List.Forall2 P (x1 :: s1) (x2 :: s2) <-> P x1 x2 /\ List.Forall2 P s1 s2.
Proof. admit. Qed.

Lemma semSequenceGenSize A (gs : list (G A)) n :
  semGenSize (sequenceGen gs) n <-->
  [set l | length l = length gs /\
    List.Forall2 (fun y => semGenSize y n) gs l].
  (*
  semGenSize (sequenceGen gs) n <-->
  [set l | List.Forall2 (fun x s => x \in s) l [seq semGenSize g n | g <- gs]].
*)
Proof.
elim: gs => [|g gs IHgs].
  by rewrite semReturnSize /set1; case=> // a l; split=> // [[]].
rewrite /= semBindSize; setoid_rewrite semBindSize; setoid_rewrite semReturnSize.
setoid_rewrite IHgs; case=> [| x l].
  split; first by case=> ? [? [? [?]]].
  by move=> H; inversion H.
rewrite Forall2_cons; split; first by case=> y [gen_y [s [[<- ?]]]] [<- <-].
by case=> [[<-] [? ?]]; exists x; split => //; exists l; split.
Qed.
  (*
elim: gs => [|g gs IHgs] /=.
  by rewrite semReturnSize /set1 => l; split=> [<-|] // meml; inversion meml.
rewrite semBindSize; setoid_rewrite semBindSize; setoid_rewrite semReturnSize.
setoid_rewrite IHgs; case=> [| x l].
  split; first by case=> ? [? [? [?]]].
  by move=> H; inversion H.
rewrite Forall2_cons; split; first by case=> y [gen_y [s []]] ? [<- <-].
by case=> ? ?; exists x; split => //; exists l; split.
*)

Lemma semVectorOfSize {A : Type} (k : nat) (g : G A) n :
  semGenSize (vectorOf k g) n <-->
  [set l | length l = k /\ l \subset (semGenSize g n)].
Proof.
elim: k => [|k IHk].
  rewrite /vectorOf /= semReturnSize.
  by move=> s; split=> [<-|[] /size0nil ->] //; split.
rewrite /vectorOf /= semBindSize; setoid_rewrite semBindSize.
setoid_rewrite semReturnSize; setoid_rewrite IHk.
case=> [|x l]; first by split=> [[? [? [? [?]]]] | []].
split=> [[y [gen_y [l' [[length_l' ?] [<- <-]]]]]|] /=.
  split; first by rewrite length_l'.
  exact/subconsset.
by case=> [[?]] /subconsset [? ?]; exists x; split => //; exists l.
Qed.

Lemma semListOfSize {A : Type} (g : G A) size :
  semGenSize (listOf g) size <-->
  [set l | length l <= size /\ l \subset (semGenSize g size)].
Proof.
rewrite /listOf semSizedSize semBindSize; setoid_rewrite semVectorOfSize.
rewrite semChooseSize => l; split=> [[n [[_ ?] [-> ?]]] | [? ?]] //.
by exists (length l).
Qed.

Lemma In_nth_exists {A} (l: list A) x def :
  List.In x l -> exists n, nth def l n = x /\ (n < length l)%coq_nat.
Proof.
elim : l => [| a l IHl] //=.
move => [H | /IHl [n [H1 H2]]]; subst.
  exists 0; split => //; omega.
exists n.+1; split => //; omega.
Qed.

Lemma semOneofSize {A} (l : list (G A)) (def : G A) s :
  semGenSize (oneof def l) s <-->
  if l is nil then semGenSize def s else \bigcup_(x in l) semGenSize x s.
Proof.
case: l => [|g l].
  rewrite semBindSize semChooseSize.
  rewrite (@eq_bigcupl _ _ _ [set 0]) ?bigcup_set1 // => a; split=> [[? ?]|<-] //.
  by apply/antisym/andP.
rewrite semBindSize semChooseSize.
set X := (fun a : nat => _ /\ _).
rewrite (reindex_bigcup (nth def (g :: l)) X) // => i; split.
admit.
admit.
Qed.

Lemma semOneof {A} (l : list (G A)) (def : G A) :
  semGen (oneof def l) <-->
  if l is nil then semGen def else \bigcup_(x in l) semGen x.
Proof.
by case: l => [|g l]; rewrite 1?bigcupC; apply: eq_bigcupr => sz;
  apply: semOneofSize.
Qed.

Lemma semElements {A} (l: list A) (def : A) :
  (semGen (elements def l)) <--> if l is nil then [set def] else l.
Proof.
  admit.
(*
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
*)
Qed.

Lemma semElementsSize {A} (l: list A) (def : A) s :
  (semGenSize (elements def l) s) <--> if l is nil then [set def] else l.
Proof.
  admit.
(*
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
*)
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

Lemma sum_fst_eq0P {A} (l : list (nat * A)) :
  sum_fst l = 0 <-> [seq x <- l | x.1 != 0] = [::].
Proof.
admit.
Qed.

Lemma pick_def :
  forall {A} (l: list (nat * G A)) n def,
    sum_fst l <= n ->
    pick def l n = (0, def).
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
    exists x, List.In x l /\ pick def l n = x /\ fst x <> 0.
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
    exists n, pick def l n = x.
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

Lemma set0mE m : [set n | 0 <= n /\ n <= m] <--> [set n | n <= m].
Proof.
admit.
Qed.

Lemma pick_imset A (def : G A) l :
  pick def l @: [set m | m < sum_fst l] <--> [seq x <- l | x.1 != 0].
Proof.
admit.
Qed.

Lemma semFrequencySize {A} (l : list (nat * G A)) (def : G A) (size: nat) :
  semGenSize (frequency def l) size <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semGenSize def size else
    \bigcup_(x in l') semGenSize x.2 size.
Proof.
rewrite semBindSize semChooseSize /=.
case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs].
move/sum_fst_eq0P: lsupp => suml; rewrite suml.
  rewrite (@eq_bigcupl _ _ _ [set 0]) ?bigcup_set1 ?pick_def // ?leqn0 ?suml //.
  by move=> n; split=> [[_]|<-] //; rewrite leqn0; move/eqP.
symmetry; apply: reindex_bigcup.
have pos_suml: 0 < sum_fst l.
  have [] := sum_fst_eq0P l.
  by rewrite lsupp; case: (sum_fst l) => // /(_ erefl).
have->: (fun a : nat => 0 <= a /\ a <= sum_fst l - 1) <--> [set m | m < sum_fst l].
  move=> m /=; split=> [[_]|]; first by rewrite -ltnS subn1 prednK.
  by rewrite -{1}(prednK pos_suml) ltnS subn1.
exact: pick_imset.
Qed.

Lemma semFrequency {A} (l : list (nat * G A)) (def : G A) :
  semGen (frequency def l) <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semGen def else
    \bigcup_(x in l') semGen x.2.
Proof.
by case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs] /=;
rewrite 1?bigcupC; apply: eq_bigcupr => sz;
have := (semFrequencySize l def sz); rewrite lsupp.
Qed.

End GenHigh.
