Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype seq.

Require Import Random GenLow.
Require Import Tactics Sets.

Import GenLow.

Set Bullet Behavior "Strict Subproofs".

Lemma nthE T (def : T) s i : List.nth i s def = nth def s i.
Proof.
elim: s i => [|x s IHs i]; first by case.
by case: i.
Qed.

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
Parameter backtrack : forall {A : Type}, list (nat * G (option A)) -> G (option A).
Parameter vectorOf : forall {A : Type}, nat -> G A -> G (list A).
Parameter listOf : forall {A : Type}, G A -> G (list A).
Parameter elements : forall {A : Type}, A -> list A -> G A.

(* Correctness for derived generators *)
Parameter semLiftGen :
  forall {A B} (f: A -> B) (g: G A),
    semGen (liftGen f g) <--> f @: semGen g.

Parameter semLiftGenSize :
  forall {A B} (f: A -> B) (g: G A) size,
    semGenSize (liftGen f g) size <--> f @: semGenSize g size.

Declare Instance liftGenUnsized {A B} (f : A -> B) (g : G A) 
        `{Unsized _ g} : Unsized (liftGen f g).

Parameter semLiftGen2Size :
  forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s,
    semGenSize (liftGen2 f g1 g2) s <-->
    f @2: (semGenSize g1 s, semGenSize g2 s).

Parameter semLiftGen2Unsized1 :
  forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2),
    Unsized g1 ->
    semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).

Parameter semLiftGen2Unsized2 :
  forall {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) `{Unsized _ g2},
    semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).

Parameter semLiftGen2SizeMonotonic :
  forall {A1 A2 B} (f: A1 -> A2 -> B)
         (g1 : G A1) (g2 : G A2) `{SizeMonotonic _ g1} `{SizeMonotonic _ g2},
  semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).

Declare Instance liftGen2Unsized {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{Unsized _ g1} (g2 : G A2) `{Unsized _ g2} : Unsized (liftGen2 f g1 g2).

Declare Instance liftGen2Monotonic {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{SizeMonotonic _ g1} (g2 : G A2) `{SizeMonotonic _ g2} : SizeMonotonic (liftGen2 f g1 g2).


Parameter semLiftGen3Size :
forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B)
       (g1: G A1) (g2: G A2) (g3: G A3) size,
  semGenSize (liftGen3 f g1 g2 g3) size <-->
  [set b : B | exists a1, semGenSize g1 size a1 /\
                          (exists a2, semGenSize g2 size a2 /\
                                      (exists a3, semGenSize g3 size a3 /\
                                                  (f a1 a2 a3) = b))].

Parameter semLiftGen4Size : forall A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
       (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4) s,
  semGenSize (liftGen4 f g1 g2 g3 g4) s <-->
  [set b : B | exists a1 a2 a3 a4, semGenSize g1 s a1 /\ semGenSize g2 s a2 /\
                 semGenSize g3 s a3 /\ semGenSize g4 s a4 /\ f a1 a2 a3 a4 = b].

Parameter semLiftGen4SizeMonotonic :
  forall A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
         (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4) 
  `{SizeMonotonic _ g1} `{SizeMonotonic _ g2}
  `{SizeMonotonic _ g3} `{SizeMonotonic _ g4},
  semGen (liftGen4 f g1 g2 g3 g4) <-->
  [set b : B | exists a1 a2 a3 a4, semGen g1 a1 /\ semGen g2 a2 /\
                 semGen g3 a3 /\ semGen g4 a4 /\ f a1 a2 a3 a4 = b].

Declare Instance liftGen4Monotonic {A B C D E} 
        (f : A -> B -> C -> D -> E)
        (g1 : G A) (g2 : G B) (g3 : G C) (g4 : G D) 
        `{ SizeMonotonic _ g1} `{ SizeMonotonic _ g2}
        `{ SizeMonotonic _ g3} `{ SizeMonotonic _ g4} 
: SizeMonotonic (liftGen4 f g1 g2 g3 g4). 


Parameter semLiftGen5Size :
forall {A1 A2 A3 A4 A5 B} (f: A1 -> A2 -> A3 -> A4 -> A5 -> B)
       (g1: G A1) (g2: G A2) (g3: G A3) (g4: G A4) (g5: G A5) size,
  semGenSize (liftGen5 f g1 g2 g3 g4 g5) size <-->
  [set b : B |
   exists a1, semGenSize g1 size a1 /\
              (exists a2, semGenSize g2 size a2 /\
                          (exists a3, semGenSize g3 size a3 /\
                                      (exists a4, semGenSize g4 size a4 /\
                                                  (exists a5, semGenSize g5 size a5 /\
                                                              (f a1 a2 a3 a4 a5) = b))))].

Parameter semSequenceGenSize:
  forall {A} (gs : list (G A)) n,
    semGenSize (sequenceGen gs) n <-->
    [set l | length l = length gs /\
      List.Forall2 (fun y => semGenSize y n) gs l].

Parameter semSequenceGenSizeMonotonic : 
  forall A (gs : list (G A)),
    (gs \subset SizeMonotonic) ->
    semGen (sequenceGen gs) <-->
           [set l | length l = length gs /\
                    List.Forall2 semGen gs l].


Parameter semFoldGen_right :
  forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A) (s : nat),
    semGenSize (foldGen f bs a0) s <-->
    [ set an |
      foldr (fun b p => [set a_prev | exists a, a \in (semGenSize (f a_prev b) s :&: p)]) 
            [set an] bs a0 ].


Parameter semOneof:
  forall {A} (l : list (G A)) (def : G A),
    (semGen (oneof def l)) <-->
      if l is nil then semGen def else \bigcup_(x in l) semGen x.

Parameter semOneofSize:
  forall {A} (l : list (G A)) (def : G A) s,
    (semGenSize (oneof def l) s) <-->
      if l is nil then semGenSize def s else \bigcup_(x in l) semGenSize x s.

Declare Instance oneofMonotonic {A} (x : G A) (l : list (G A))
        `{ SizeMonotonic _ x} `(l \subset SizeMonotonic) : SizeMonotonic (oneof x l). 

Parameter semFrequency:
  forall {A} (l : list (nat * G A)) (def : G A),
    semGen (frequency def l) <-->
      let l' := [seq x <- l | x.1 != 0] in
      if l' is nil then semGen def else
        \bigcup_(x in l') semGen x.2.

Parameter frequencySizeMonotonic:
  forall {A} (g0 : G A) lg,
  SizeMonotonic g0 ->
  List.Forall (fun p => SizeMonotonic (snd p)) lg ->
  SizeMonotonic (frequency g0 lg).

Parameter semFrequencySize:
  forall {A} (l : list (nat * G A)) (def : G A) (size: nat),
    semGenSize (frequency def l) size <-->
      let l' := [seq x <- l | x.1 != 0] in
      if l' is nil then semGenSize def size else
      \bigcup_(x in l') semGenSize x.2 size.

(** [backtrack] generates Some's unless all of the input generators are empty *)
Parameter semBacktrackSize:
  forall {A} (l : list (nat * G (option A))) size,
  semGenSize (backtrack l) size <--> 
  (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGenSize x.2 size))) :|:
  ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGenSize x.2 size))).

Parameter backtrackSizeMonotonic: 
  forall {A : Type} (lg : seq (nat * G (option A))),
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (backtrack lg).

Parameter semVectorOfSize:
  forall {A : Type} (k : nat) (g : G A) size,
    semGenSize (vectorOf k g) size <-->
    [set l | length l = k /\ l \subset semGenSize g size].

Parameter semVectorOfUnsized : 
  forall {A} (g : G A) (k : nat) `{Unsized _ g}, 
    semGen (vectorOf k g) <--> [set l | length l = k /\ l \subset semGen g ]. 

Declare Instance vectorOfUnsized {A} (k : nat) (g : G A) 
        `{Unsized _ g } : Unsized (vectorOf k g).

Declare Instance vectorOfMonotonic {A} (k : nat) (g : G A) 
        `{SizeMonotonic _ g } : SizeMonotonic (vectorOf k g).

Parameter semListOfSize:
  forall (A : Type) (g : G A) (size : nat),
    semGenSize (listOf g) size <-->
    [set l | length l <= size /\ l \subset semGenSize g size].

Parameter semListOfUnsized: 
  forall {A} (g : G A) (k : nat) `{Unsized _ g}, 
    semGen (listOf g) <--> [set l | l \subset semGen g ]. 

Declare Instance listOfMonotonic {A} (g : G A) 
        `{SizeMonotonic _ g } : SizeMonotonic (listOf g).

Parameter semElements:
  forall {A} (l: list A) (def : A),
    (semGen (elements def l)) <--> if l is nil then [set def] else l.

Parameter semElementsSize:
  forall {A} (l: list A) (def : A) s,
    (semGenSize (elements def l) s) <--> if l is nil then [set def] else l.

Declare Instance elementsUnsized {A} {def : A} (l : list A)  : Unsized (elements def l).

Definition genPair {A B : Type} (ga : G A) (gb : G B) : G (A * B) :=
  liftGen2 pair ga gb.

Definition uncurry {A B C : Type} (f : A -> B -> C) (ab : A * B) :=
  match ab with
  | (a,b) => f a b
  end.

Definition curry {A B C : Type} (f : A * B -> C) (a : A) (b : B) := f (a,b).

Parameter mergeBinds :
  forall A B C (ga : G A) (gb : G B) (f : A -> B -> G C),
    semGen (bindGen ga (fun x => bindGen gb (f x))) <-->
    semGen (bindGen (genPair ga gb) (uncurry f)).

Module QcDefaultNotation.

Notation " 'elems' [ x ] " := (elements x (cons x nil)) : qc_scope.
Notation " 'elems' [ x ; y ] " := (elements x (cons x (cons y nil))) : qc_scope.
Notation " 'elems' [ x ; y ; .. ; z ] " :=
  (elements x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'elems' ( x ;; l ) " :=
  (elements x (cons x l)) (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' [ x ] " := (oneof x (cons x nil)) : qc_scope.
Notation " 'oneOf' [ x ; y ] " := (oneof x (cons x (cons y nil))) : qc_scope.
Notation " 'oneOf' [ x ; y ; .. ; z ] " :=
  (oneof x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'oneOf' ( x ;; l ) " :=
  (oneof x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'freq' [ x ] " := (frequency x (cons x nil)) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ] " :=
  (frequency x (cons (n, x) (cons y nil))) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ; .. ; z ] " :=
  (frequency x (cons (n, x) (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'freq' ( ( n , x ) ;; l ) " :=
  (frequency x (cons (n, x) l)) (at level 1, no associativity) : qc_scope.

End QcDefaultNotation.

Module QcDoNotation.

Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do\'' X <- A ; B" :=
  (bindGen' A (fun X H => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'doM!' X <- A ; B" :=
  (bindGenOpt A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

End QcDoNotation.

Import QcDefaultNotation. Open Scope qc_scope.

Parameter semElemsSize : forall A (x : A) xs s,
  semGenSize (elems (x ;; xs)) s <--> x :: xs.

Parameter semElems : forall A (x : A) xs,
  semGen (elems (x ;; xs)) <--> x :: xs.

Parameter semOneOfSize : forall A (g0 : G A) (gs : list (G A)) s,
  semGenSize (oneOf (g0 ;; gs)) s  <--> \bigcup_(g in (g0 :: gs)) semGenSize g s.

Parameter semOneOf : forall A (g0 : G A) (gs : list (G A)),
  semGen (oneOf (g0 ;; gs))  <--> \bigcup_(g in (g0 :: gs)) semGen g.

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

(* This should use urns! *)
Fixpoint pickDrop {A : Type} (xs : list (nat * G (option A))) n : nat * G (option A) * list (nat * G (option A)) :=
  match xs with
    | nil => (0, returnGen None, nil)
    | (k, x) :: xs =>
      if (n < k) then  (k, x, xs)
      else let '(k', x', xs') := pickDrop xs (n - k)
           in (k', x', (k,x)::xs')
  end. 

Definition sum_fst {A : Type} (gs : list (nat * A)) : nat :=
  foldl (fun t p => t + (fst p)) 0 gs.

Definition frequency {A : Type} (def : G A) (gs : list (nat * G A))
: G A :=
  let tot := sum_fst gs in
  bindGen (choose (0, tot-1)) (fun n =>
  @snd _ _ (pick def gs n)).

Fixpoint backtrackFuel {A : Type} (fuel : nat) (tot : nat) (gs : list (nat * G (option A))) : G (option A) :=
  match fuel with 
    | O => returnGen None
    | S fuel' => bindGen (choose (0, tot-1)) (fun n => 
                 let '(k, g, gs') := pickDrop gs n in
                 bindGen g (fun ma =>
                 match ma with 
                   | Some a => returnGen (Some a)
                   | None => backtrackFuel fuel' (tot - k) gs'
                 end ))
  end.

Definition backtrack {A : Type} (gs : list (nat * G (option A))) : G (option A) :=
  backtrackFuel (length gs) (sum_fst gs) gs.

Definition vectorOf {A : Type} (k : nat) (g : G A)
: G (list A) :=
  foldr (fun m m' =>
                bindGen m (fun x =>
                bindGen m' (fun xs => returnGen (cons x xs)))
             ) (returnGen nil) (nseq k g).

Definition listOf {A : Type} (g : G A) : G (list A) :=
  sized (fun n => bindGen (choose (0, n)) (fun k => vectorOf k g)).

Definition elements {A : Type} (def : A) (l : list A) :=
  let n := length l in
  bindGen (choose (0, n - 1)) (fun n' =>
  returnGen (List.nth n' l def)).

  
Lemma semLiftGen {A B} (f: A -> B) (g: G A) :
  semGen (liftGen f g) <--> f @: semGen g.
Proof.
  rewrite imset_bigcup. apply: eq_bigcupr => size.
    by rewrite semBindSize (eq_bigcupr _ (fun a => semReturnSize (f a) size)).
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

Lemma semLiftGenSize {A B} (f: A -> B) (g: G A) size :
  semGenSize (liftGen f g) size <--> f @: (semGenSize g size).
Proof. 
    by rewrite semBindSize (eq_bigcupr _ (fun a => semReturnSize (f a) size)).
 Qed.

Program Instance liftGenUnsized {A B} (f : A -> B) (g : G A) 
        `{Unsized _ g} : Unsized (liftGen f g).
Next Obligation.
  by rewrite ! semLiftGenSize (unsized s1 s2).
Qed.

Program Instance liftGenMonotonic {A B} (f : A -> B) (g : G A) 
        `{SizeMonotonic _ g} : SizeMonotonic (liftGen f g).
Next Obligation.
  rewrite ! semLiftGenSize. apply imset_incl. by apply monotonic.
Qed.

Lemma semLiftGen2Size {A1 A2 B} (f: A1 -> A2 -> B) (g1 : G A1) (g2 : G A2) s :
  semGenSize (liftGen2 f g1 g2) s <-->
  f @2: (semGenSize g1 s, semGenSize g2 s).
Proof. 
  rewrite semBindSize curry_imset2l; apply: eq_bigcupr => x.
    by rewrite semBindSize; apply: eq_bigcupr => y; rewrite semReturnSize.
Qed.

     
Lemma semLiftGen2SizeMonotonic {A1 A2 B} (f: A1 -> A2 -> B)
                               (g1 : G A1) (g2 : G A2) 
                               `{SizeMonotonic _ g1} `{SizeMonotonic _ g2} :
  semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).
Proof.
  rewrite /semGen. setoid_rewrite semLiftGen2Size.
  move => b. split. 
  - move => [sb [_ Hb]]. (* point-free reasoning would be nice here *)
    destruct Hb as [a [[Hb11 Hb12] Hb2]]. exists a. split; [| by apply Hb2].
    split; eexists; by split; [| eassumption].
  - move => [[a1 a2] [[[s1 [_ G1]] [s2 [_ G2]]] Hf]]. compute in Hf.
    exists (max s1 s2). split; first by [].
    exists (a1,a2). split; last by []. split => /=;
    (eapply monotonic; last eassumption); 
    apply/leP; solve [ apply Max.le_max_l | apply Max.le_max_r ].
Qed.

Lemma semLiftGen2Unsized1 {A1 A2 B} (f: A1 -> A2 -> B)
      (g1 : G A1) (g2 : G A2) `{Unsized _ g1}:
  semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).
Proof.
  rewrite /semGen. setoid_rewrite semLiftGen2Size.
  move=> b. split.
  - move => [n [_ [[a1 a2] [[/= H2 H3] H4]]]]. exists (a1, a2).
    split; auto; split; eexists; split; eauto; reflexivity.
  - move => [[a1 a2] [[[s1 /= [H2 H2']] [s2 [H3 H3']]] H4]].
    eexists. split; first by eauto. 
    exists (a1, a2); split; eauto.
    split; last by eauto. simpl. 
    eapply unsized; eauto; apply (unsized2 H); eauto.
Qed.
  
Lemma semLiftGen2Unsized2 {A1 A2 B} (f: A1 -> A2 -> B)
      (g1 : G A1) (g2 : G A2) `{Unsized _ g2}:
  semGen (liftGen2 f g1 g2) <--> f @2: (semGen g1, semGen g2).
Proof.
  rewrite /semGen. setoid_rewrite semLiftGen2Size.
  move=> b. split. 
  - move => [n [_ [[a1 a2] [[/= H2 H3] H4]]]]. exists (a1, a2).
    split; auto; split; eexists; split; eauto; reflexivity.
  - move => [[a1 a2] [[[s1 /= [H2 H2']] [s2 [H3 H3']]] H4]].
    eexists. split; first by auto.
    exists (a1, a2). split; eauto.
    split; first by eauto. simpl. 
    eapply unsized; eauto.
Qed.

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

Program Instance liftGen2Unsized {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{Unsized _ g1} (g2 : G A2) `{Unsized _ g2} : Unsized (liftGen2 f g1 g2).
Next Obligation.
  rewrite ! semLiftGen2Size. 
  rewrite ! curry_imset2l. by setoid_rewrite (unsized s1 s2).
Qed.

Program Instance liftGen2Monotonic {A1 A2 B} (f : A1 -> A2 -> B) (g1 : G A1)
        `{SizeMonotonic _ g1} (g2 : G A2) `{SizeMonotonic _ g2} : 
  SizeMonotonic (liftGen2 f g1 g2).
Next Obligation.
  rewrite ! semLiftGen2Size. rewrite ! curry_imset2l. 
  move => b [a1 [Ha1 [a2 [Ha2 <-]]]].
  do 2 (eexists; split; first by eapply (monotonic H1); eauto).
  reflexivity.
Qed.


(* CH: Made this more beautiful than the rest *)
(* CH: Should anyway use dependent types for a generic liftGenN *)
Lemma semLiftGen4Size A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
                     (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4) s :
  semGenSize (liftGen4 f g1 g2 g3 g4) s <-->
  [set b : B | exists a1 a2 a3 a4, semGenSize g1 s a1 /\ semGenSize g2 s a2 /\
                 semGenSize g3 s a3 /\ semGenSize g4 s a4 /\ f a1 a2 a3 a4 = b].
Proof.
  split; unfold liftGen4; intros.
  - repeat match goal with
    | [ H : semGenSize _ _ _ |- _ ] =>
      try (apply semBindSize in H; destruct H as [? [? ?]]);
      try (apply semReturnSize in H; subst)
    end.
    do 4 eexists. repeat (split; [eassumption|]). assumption.
  - repeat match goal with
    | [ H : exists _, _ |- _ ] => destruct H as [? [? ?]]
    | [ H : and _ _ |- _ ] => destruct H as [? ?]
    end.
    repeat (apply semBindSize; eexists; split; [eassumption|]).
    apply semReturnSize. assumption.
Qed.

(* begin semLiftGen4SizeMonotonic *)
Lemma semLiftGen4SizeMonotonic A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B)
                               (g1 : G A1) (g2 : G A2) (g3 : G A3) (g4 : G A4)
                               `{SizeMonotonic _ g1} `{SizeMonotonic _ g2}
                               `{SizeMonotonic _ g3} `{SizeMonotonic _ g4} :
  semGen (liftGen4 f g1 g2 g3 g4) <-->
  [set b : B | exists a1 a2 a3 a4, semGen g1 a1 /\ semGen g2 a2 /\
                 semGen g3 a3 /\ semGen g4 a4 /\ f a1 a2 a3 a4 = b].
(* end semLiftGen4SizeMonotonic *)
Proof.
  rewrite /semGen. setoid_rewrite semLiftGen4Size.
  move => b. split. 
  - move => [s [_ [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 Hb]]]]]]]]]]; subst.
    exists a1. exists a2. exists a3. exists a4. 
    repeat split; exists s; (split; [reflexivity | eassumption ]). 
  -  move => [a1 [a2 [a3 [a4 [[s1 [_ Ha1]] 
                                [[s2 [_ Ha2]] 
                                   [[s3 [_ Ha3]] 
                                      [[s4 [_ Ha4]] Hb]]]]]]]]; subst.
    exists (max s1 (max s2 (max s3 s4))). 
    split; first by [].
    exists a1. exists a2. exists a3. exists a4. 
    repeat split; (eapply monotonic; [ apply/leP | ]; last eassumption).
    by eapply Max.le_max_l.
    eapply Nat.max_le_iff. right. by eapply Max.le_max_l.
    eapply Nat.max_le_iff. right.
    eapply Nat.max_le_iff. right. by eapply Max.le_max_l.
    eapply Nat.max_le_iff. right.
    eapply Nat.max_le_iff. right.
    eapply Nat.max_le_iff. by right. 
Qed.

Program Instance liftGen4Monotonic {A B C D E} 
        (f : A -> B -> C -> D -> E)
        (g1 : G A) (g2 : G B) (g3 : G C) (g4 : G D) 
        `{ SizeMonotonic _ g1} `{ SizeMonotonic _ g2}
        `{ SizeMonotonic _ g3} `{ SizeMonotonic _ g4} 
: SizeMonotonic (liftGen4 f g1 g2 g3 g4). 
Next Obligation.
  rewrite ! semLiftGen4Size.
  move => t /= [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 H5]]]]]]]]; subst.
  eexists. eexists. eexists. eexists. 
  repeat (split; try reflexivity); by eapply monotonic; eauto. 
Qed.

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

Lemma Forall2_cons T U (P : T -> U -> Prop) x1 s1 x2 s2 :
  List.Forall2 P (x1 :: s1) (x2 :: s2) <-> P x1 x2 /\ List.Forall2 P s1 s2.
Proof.
split=> [H|[? ?]]; last by constructor.
by inversion H.
Qed.

Lemma semSequenceGenSize A (gs : list (G A)) n :
  semGenSize (sequenceGen gs) n <-->
  [set l | length l = length gs /\
    List.Forall2 (fun y => semGenSize y n) gs l].
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

Lemma Forall2_SizeMonotonic {A} x n (gs : list (G A)) l :
  x <= n -> gs \subset SizeMonotonic -> 
  List.Forall2 (semGenSize^~ x) gs l ->
  List.Forall2 (semGenSize^~ n) gs l.
Proof. 
  intros. induction H1; auto.
  apply subconsset in H0. destruct H0; auto. 
  constructor; auto. eapply H0; eauto.
Qed.

Lemma semSequenceGenSizeMonotonic A (gs : list (G A)) :
  (gs \subset SizeMonotonic) ->
  semGen (sequenceGen gs) <-->
  [set l | length l = length gs /\
    List.Forall2 semGen gs l].
Proof.
  intros. rewrite /semGen. setoid_rewrite semSequenceGenSize.
  move => l. split.
  - move => [n [ _ [H1 H2]]]. split; auto.
    induction H2; subst; simpl; constructor.
    + exists n. split; auto. reflexivity. 
    + apply IHForall2; eauto. 
      apply subconsset in H. destruct H; auto. 
  - move => [H1 H2]. revert gs H H1 H2. induction l; intros gs H H1 H2.
    + destruct gs; try discriminate. exists 0. 
      split; auto. reflexivity.
    + destruct gs; try discriminate.
      apply subconsset in H. move : H => [H3 H4].  
      inversion H2; subst. destruct H6 as [n [ _ H5]].
      eapply IHl in H8; auto. destruct H8 as [x [_ [H7 H8]]].
      destruct (x <= n) eqn:Hle. 
      { exists n. split; eauto; first by reflexivity. split; auto. 
        constructor; auto. eapply Forall2_SizeMonotonic; eauto. }
      { exists x.  split; first by reflexivity. split; auto.
        constructor; auto. eapply H3; last by eassumption. 
        rewrite -> leq_eqVlt, -> Bool.orb_false_iff in Hle. 
        destruct Hle; auto. rewrite leqNgt H0 //. }
Qed.
 
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

Lemma semVectorOfUnsized {A} (g : G A) (k : nat) `{Unsized _ g}: 
  semGen (vectorOf k g) <--> [set l | length l = k /\ l \subset semGen g ]. 
Proof.
  rewrite /semGen.
  setoid_rewrite semVectorOfSize.
  move => l; split.
  - move => [k' [_ [H1 H2]]]. split; auto. exists k'. split; auto.
    reflexivity.
  - move => [H1 H2]. 
    exists k. split; first by reflexivity.
    split; auto. move => a /H2 [x [_ Hx]]. 
    by eapply unsized; eauto.
Qed.

Program Instance vectorOfUnsized {A} (k : nat) (g : G A) 
        `{Unsized _ g } : Unsized (vectorOf k g).
Next Obligation.
  rewrite ! semVectorOfSize. 
  split; move => [H1 H2]; split => //; by rewrite unsized; eauto.
Qed.

Program Instance vectorOfMonotonic {A} (k : nat) (g : G A) 
        `{SizeMonotonic _ g } : SizeMonotonic (vectorOf k g).
Next Obligation.
  rewrite ! semVectorOfSize. 
  move => l [H1 H2]; split => // a Ha. by eapply (monotonic H0); eauto.
Qed.


Lemma semListOfSize {A : Type} (g : G A) size :
  semGenSize (listOf g) size <-->
  [set l | length l <= size /\ l \subset (semGenSize g size)].
Proof.
rewrite /listOf semSizedSize semBindSize; setoid_rewrite semVectorOfSize.
rewrite semChooseSize // => l; split=> [[n [/andP [_ ?] [-> ?]]]| [? ?]] //.
by exists (length l).
Qed.

Lemma semListOfUnsized {A} (g : G A) (k : nat) `{Unsized _ g} : 
  semGen (listOf g) <--> [set l | l \subset semGen g ]. 
Proof.
  rewrite /semGen.
  setoid_rewrite semListOfSize. 
  move => l; split.
  - move => [k' [_ [H1 H2]]]. exists k'. split; auto.
    reflexivity.
  - move => Hl. exists (length l). repeat split => //.
    move => a /Hl [s [_ Ha]]. by eapply unsized; eauto.
Qed.

Program Instance listOfMonotonic {A} (g : G A) 
        `{SizeMonotonic _ g } : SizeMonotonic (listOf g).
Next Obligation.
  rewrite ! semListOfSize.
  move => l [H1 H2]; split => //. by eapply leq_trans; eauto.
  move => a /H2 Ha. by eapply monotonic; eauto.
Qed.


Lemma In_nth_exists {A} (l: list A) x def :
  List.In x l -> exists n, nth def l n = x /\ (n < length l)%coq_nat.
Proof.
elim : l => [| a l IHl] //=.
move => [H | /IHl [n [H1 H2]]]; subst.
  exists 0; split => //; omega.
exists n.+1; split => //; omega.
Qed.

Lemma nth_imset T (def : T) l : nth def l @: [set n | n < length l] <--> l.
Proof.
case: l => [|x l] t; first by split=> //; case=> ?; rewrite ltn0; case.
split; first by case=> n [? <-]; rewrite -nthE; apply/List.nth_In/ltP.
by case/(In_nth_exists _ _ def) => n [? ?]; exists n; split=> //; apply/ltP.
Qed.

Lemma semOneofSize {A} (l : list (G A)) (def : G A) s : semGenSize (oneof def l) s
  <--> if l is nil then semGenSize def s else \bigcup_(x in l) semGenSize x s.
Proof.
case: l => [|g l].
  rewrite semBindSize semChooseSize //.
  rewrite (eq_bigcupl [set 0]) ?bigcup_set1 // => a; split=> [/andP [? ?]|<-] //.
  by apply/antisym/andP.
rewrite semBindSize semChooseSize //.
set X := (fun a : nat => is_true (_ && _)).
by rewrite (reindex_bigcup (nth def (g :: l)) X) // /X subn1 nth_imset.
Qed.

Lemma semOneof {A} (l : list (G A)) (def : G A) :
  semGen (oneof def l) <-->
  if l is nil then semGen def else \bigcup_(x in l) semGen x.
Proof.
by case: l => [|g l]; rewrite 1?bigcupC; apply: eq_bigcupr => sz;
  apply: semOneofSize.
Qed.

Program Instance oneofMonotonic {A} (x : G A) (l : list (G A))
        `{ SizeMonotonic _ x} `(l \subset SizeMonotonic) 
: SizeMonotonic (oneof x l). 
Next Obligation.
  rewrite !semOneofSize. elim : l H0 => [_ | g gs IH /subconsset [H2 H3]] /=.
  - by apply monotonic.
  - specialize (IH H3). move => a [ga [[Hga | Hga] Hgen]]; subst.
    exists ga. split => //. left => //.
    eapply monotonic; eauto. exists ga.
    split. right => //.
    apply H3 in Hga. by apply (monotonic H1). 
Qed.

Lemma semElementsSize {A} (l: list A) (def : A) s :
  semGenSize (elements def l) s <--> if l is nil then [set def] else l.
Proof.
rewrite semBindSize.
setoid_rewrite semReturnSize.
rewrite semChooseSize //=.
setoid_rewrite nthE.
case: l => [|x l] /=.
  rewrite (eq_bigcupl [set 0]) ?bigcup_set1 // => n.
  by rewrite leqn0; split=> [/eqP|->].
rewrite -(@reindex_bigcup _ _ _ (nth def (x :: l)) _ (x :: l)) ?coverE //.
by rewrite subn1 /= nth_imset.
Qed.

Lemma semElements {A} (l: list A) (def : A) :
  (semGen (elements def l)) <--> if l is nil then [set def] else l.
Proof.
rewrite /semGen; setoid_rewrite semElementsSize; rewrite bigcup_const //.
by do 2! constructor.
Qed.

Program Instance elementsUnsized {A} {def : A} (l : list A) : 
  Unsized (elements def l).
Next Obligation.
  rewrite ! semElementsSize. by case: l.
Qed.

(* A rather long frequency proof, probably we can do better *)

Lemma not_lt : forall n m, (false = (n < m)) -> (m <= n).
Proof.
  move => n m. by elim: n m=> [| n IHn]; case.
Qed.

Lemma sum_fstE A x (a : A) l:
  sum_fst ((x, a) :: l) = x + sum_fst l.
Proof.
rewrite /sum_fst /=.
elim: l 0 x => [n x|[n1 x1] l IHl p q] /=; first by rewrite addnC.
by rewrite -IHl; congr foldl; rewrite addnAC.
Qed.

Lemma sum_fst_eq0P {A} (l : list (nat * A)) :
  sum_fst l = 0 <-> [seq x <- l | x.1 != 0] = [::].
Proof.
by elim: l => [|[[|n] x] l IHl] //=; split=> //; rewrite sum_fstE.
Qed.

Lemma pick_def :
  forall {A} (l: list (nat * G A)) n def,
    sum_fst l <= n ->
    pick def l n = (0, def).
Proof.
  move=> A l n def Hleq.
  elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
  rewrite sum_fstE in Hleq.
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
    rewrite sum_fstE in Hlt.
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

Lemma pick_imset A (def : G A) l :
  pick def l @: [set m | m < sum_fst l] <--> [seq x <- l | x.1 != 0].
Proof.
elim: l => [|[n x] l IHl] /=.
  rewrite /sum_fst /=.
  have->: (fun m => m < 0) <--> set0 by [].
  by rewrite imset0.
case: n => /= [|n].
  rewrite -IHl => t; split=> [[y []]|].
    by rewrite sum_fstE add0n subn0 => lt_y <-; exists y.
  by case=> y [lt_y <-]; exists y; split=> //; rewrite subn0.
move=> t; split=> /= [[p [lt_p]]|].
  case: ifP => [_ <-|lt_pn ?]; first by left.
    right; rewrite -(IHl t); exists (p - n.+1); split=> //.
  rewrite sum_fstE in lt_p.
  by rewrite -(ltn_add2r n.+1) subnK 1?addnC // leqNgt lt_pn.
case=> [<-|]; first by exists 0; split => //; rewrite sum_fstE.
rewrite -(IHl t); case=> p [lt_p <-]; exists (n.+1 + p); split.
  by rewrite sum_fstE ltn_add2l.
by rewrite ltnNge leq_addr addKn.
Qed.

Lemma pickDrop_def :
  forall {A} (l: list (nat * G (option A))) n,
    sum_fst l <= n ->
    pickDrop l n = (0, returnGen None, l).
Proof.
  move=> A l n Hleq.
  elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
  rewrite sum_fstE in Hleq.
  remember (n < i). case: b Heqb => Heqb; symmetry in Heqb.
  - have : (i + sum_fst l) < i by eapply (leq_ltn_trans); eassumption.
    rewrite -ltn_subRL. by have -> : forall i, (i - i) = 0 by elim.
  - rewrite IHl; eauto. rewrite -(leq_add2r i) subnK.
      by rewrite addnC. by apply/not_lt.
Qed.

(* Probably needs something about l' and l. *)
(* ZP : added a few things *)
Lemma pickDrop_exists :
  forall {A} (l: list (nat * G (option A))) n,
    n <  sum_fst l <->
    exists k g l',
      List.In (k,g) l /\ pickDrop l n = (k,g,l') /\ k <> 0 /\
      l <--> [set (k, g)] :|: l' /\
      length l' + 1 = length l /\
      sum_fst l' + k = sum_fst l.
Proof.
  move => A l n. split.
  - move => Hlt.
    elim : l n Hlt => //. case => i p xs IHxs n Hlt.
    rewrite sum_fstE in Hlt.
    move/(_ (n-i)) : IHxs => IHxs. simpl.
    remember (n < i). case: b Heqb => [Heqb | /not_lt Heqb].
    + exists i. exists p. exists xs. split => //=. by left.  split => //=.
      split. move => contra; subst. by rewrite ltn0 in Heqb.
      split. by rewrite cons_set_eq.
      split. by ssromega.
      rewrite sum_fstE. by ssromega.
    + rewrite -(ltn_add2r i) [X in _  < X]addnC subnK // in IHxs.
      move/(_ Hlt) : IHxs => [k [g [gs [H1 [H2 [H3 [H4 [H5 H6]]]]]]]].
      exists k. exists g. exists ((i,p)::gs).
      split; [right | split; [| split; [| split; [| split]]]];
      try (simpl; eauto; by rewrite H2).
      rewrite !cons_set_eq H4.
      rewrite setU_assoc (setU_comm [set (i, p)]) -setU_assoc.
      reflexivity.
      simpl. by ssromega.
      simpl. rewrite !sum_fstE. by ssromega.
  - move => [k [g [gs [HIn [Hpick [Hneq _]]]]]].
    remember (n < sum_fst l).
    case: b  Heqb => //= /not_lt/pickDrop_def H.
    rewrite H in Hpick. 
    inversion Hpick; subst; eauto.
Qed.

Lemma pickDrop_In :
  forall {A} (l: list (nat * G (option A))) k x,
    List.In (k,x) l /\ k <> 0 ->
    exists n l', pickDrop l n = (k,x,l').
Proof.
  move => A l k x [HIn Hfst].
  elim : l HIn => //=. case => //= i g xs IHxs [H1 | H2]; subst.
  + exists 0.  exists xs. simpl in *.
    inversion H1; subst; clear H1.
    have H : 0 < k by  elim : k Hfst IHxs => //=.
    rewrite H.
      by split => //=.
  + move/(_ H2) : IHxs => [n [l' Hpick]].
    exists (n + i). exists ((i,g)::l'). 
    rewrite -[X in _ < X]add0n ltn_add2r ltn0.
    rewrite  -[X in _ - X]add0n subnDr subn0.
    by rewrite Hpick.
Qed.

(* begin semFrequencySize *)
Lemma semFrequencySize {A}
      (l : list (nat * G A)) (def : G A) (size: nat) :
  semGenSize (frequency def l) size <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semGenSize def size else
      \bigcup_(x in l') semGenSize x.2 size.
(* end semFrequencySize *)
Proof.
rewrite semBindSize semChooseSize //=.
case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs].
move/sum_fst_eq0P: lsupp => suml; rewrite suml.
  rewrite (@eq_bigcupl _ _ _ [set 0]) ?bigcup_set1 ?pick_def // ?leqn0 ?suml //.
  by move=> n; split; rewrite leqn0; [move/eqP|] => ->.
symmetry; apply: reindex_bigcup.
have pos_suml: 0 < sum_fst l.
  have [] := sum_fst_eq0P l.
  by rewrite lsupp; case: (sum_fst l) => // /(_ erefl).
have->: (fun a : nat => a <= sum_fst l - 1) <--> [set m | m < sum_fst l].
  by move=> m /=; rewrite -ltnS subn1 prednK.
exact: pick_imset.
Qed.

(* begin semFrequency *)
Lemma semFrequency {A} (l : list (nat * G A)) (def : G A) :
  semGen (frequency def l) <-->
    let l' := [seq x <- l | x.1 != 0] in
    if l' is nil then semGen def else
      \bigcup_(x in l') semGen x.2.
(* end semFrequency *)
Proof.
by case lsupp: {1}[seq x <- l | x.1 != 0] => [|[n g] gs] /=;
rewrite 1?bigcupC; apply: eq_bigcupr => sz;
have := (semFrequencySize l def sz); rewrite lsupp.
Qed.

Lemma frequencySizeMonotonic {A} (g0 : G A) lg :
  SizeMonotonic g0 ->
  List.Forall (fun p => SizeMonotonic (snd p)) lg ->
  SizeMonotonic (frequency g0 lg).
Admitted.

Lemma eq_lt_0 : (fun x => x <= 0) <--> [set 0].
Proof. 
  move => x; split => H; auto.
  - destruct x; auto. 
    + unfold set1; auto.
    + inversion H.
  - inversion H; auto.
Qed.

Lemma semBacktrackFuelDef {A} fuel (l : list (nat * G (option A))) size :
  sum_fst l = 0 -> 
  semGenSize (backtrackFuel fuel 0 l) size <--> [set None].
Proof.
  move: l size. 
  induction fuel => l size HSum //=.
  - by rewrite semReturnSize.
  - rewrite semBindSize semChooseSize //=.
    rewrite (@eq_bigcupl _ _ _ [set 0]) ?bigcup_set1 ?pickDrop_def // ?sub0n ?leqn0 ?HSum //=.
    + rewrite semBindSize semReturnSize bigcup_set1; eauto.
    + by apply eq_lt_0.
Qed.

Lemma in_memP {A : eqType} x (l : seq A) :
  reflect (List.In x l) (x \in l)%bool.
Proof.
  induction l; simpl.
  - constructor; eauto.
  - rewrite in_cons.
    destruct (x == a) eqn:Heq; move : Heq => /eqP Heq; subst; simpl.
    + constructor; eauto.
    + eapply equivP; try eassumption.
      split; firstorder. congruence.
Qed.  

Lemma forall_leq_sum_fst {A} (l : list (nat * A)) :
  forall a n, seq_In l (n, a) -> n <= sum_fst l.
Proof.
  elim : l => [| [n a] l IH]; eauto.
  rewrite sum_fstE.
  move => n' a' /= [[H1 H2] | H2]; subst.
  by ssromega.
  apply IH in H2. by ssromega.
Qed.

Lemma pickDrop_leq_top {A} (l : seq (nat * G (option A))) (n : nat) k g l' size s :
  pickDrop l n = (k, g, l') ->
  semGenSize g size (Some s) ->
  n < sum_fst l.
Proof.
  revert n l'.
  elim : l => [|[m a] l IH] n l' /= Hpd Hgen.
  - move : Hpd => [H1 H2 H3]; subst.
    apply semReturnSize in Hgen. discriminate.
  - rewrite sum_fstE.
    destruct (n < m) eqn:H. by ssromega.
    destruct (pickDrop l (n - m)) as [[k' x'] xs'] eqn:Heq. 
    move : Hpd => [H1 H2 H3]; subst.
    eapply IH in Heq. by ssromega.
    eassumption.
Qed.

Lemma backtrackFuelSizeMonotonic {A : Type} tot fuel (lg : seq (nat * G (option A))) :
    sum_fst lg = tot -> length lg = fuel -> 
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (backtrackFuel fuel tot lg).
Proof.
  move: tot lg.
  induction fuel => tot lg.
  - move => HSum /List.length_zero_iff_nil HLen; subst; simpl.
    eauto with typeclass_instances.
  - move => HSum HLen Hsub.
    simpl. 
    refine (@bindMonotonicStrong _ _ _ _ _ _).
    move => x /semChoose Hin.
    unfold leq, super, ChooseNat, OrdNat in Hin.
    specialize (Hin (leq0n (tot-1))).
    destruct (sum_fst lg) eqn:Hsum; subst.
    + rewrite pickDrop_def.
      refine (@bindMonotonicStrong _ _ _ _ _ _).
      * intros [ y | ].
        now eauto with typeclass_instances.
        move => _.
        constructor. intros. rewrite !semBacktrackFuelDef; eauto.
        eapply subset_refl.
      * rewrite Hsum. ssromega.
    + edestruct (pickDrop_exists lg x) as [[k [g' [lg' [Hin' [Hdrop [Hneq [Heq [Heq' Hlen]]]]]]]] _].
      ssromega. rewrite Hdrop.
      refine (@bindMonotonicStrong _ _ _ _ _ _).
      eapply Hsub in Hin'. eassumption.
      intros [ a | ].
      now eauto with typeclass_instances.
      intros _. eapply IHfuel.
      * rewrite Hsum in Hlen. rewrite <- Hlen. ssromega.
      * rewrite HLen in Heq'. ssromega.
      * eapply subset_trans; [| eassumption ].
        rewrite Heq. eapply setU_subset_r.
        eapply subset_refl.
Qed.

Corollary backtrackSizeMonotonic {A : Type} (lg : seq (nat * G (option A))) :
  lg \subset [set x | SizeMonotonic x.2 ] ->
  SizeMonotonic (backtrack lg).
Proof.
  intros Hin. unfold backtrack.
  eapply backtrackFuelSizeMonotonic; eauto.
Qed.
  
Lemma semBacktrackFuel {A} tot fuel (l : list (nat * G (option A))) size :
  sum_fst l = tot -> length l = fuel -> 
  semGenSize (backtrackFuel fuel tot l) size <--> 
  (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGenSize x.2 size))) :|:
  ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGenSize x.2 size))).
Proof.
  move: tot l size.
  induction fuel => tot l size.
  - move => HSum /List.length_zero_iff_nil HLen; subst; simpl.
    by rewrite setI_comm !nil_set_eq setI_set0_abs bigcup_set0 bigcap_set0
               setU_comm setU_set0_neut setI_setT_neut semReturnSize.
  - move => HSum HLen.
    rewrite semBindSize semChooseSize //=. 
    split.
    { destruct (sum_fst l) eqn:Hsum; subst.
      - move => [n [Hleq H]].
        rewrite pickDrop_def in H; eauto.
        move : H =>  /semBindSize [[b |] [H1 H2]].
        + eapply semReturnSize in H1. inversion H1.
        + apply semBacktrackFuelDef in H2; eauto.
          inversion H2; subst.
          right. split; eauto.
          move => [n' a] [H3 H4]. eapply forall_leq_sum_fst in H3.
          subst. simpl in *. ssromega. 
      - move => [m [Hleq H]].
        move: (pickDrop_exists l m) => [H1 H2].
        edestruct H1 as [k [g [l' [HIn [Hpd [Hkneq [Hsub [Hlen Hfst]]]]]]]].
        rewrite Hsum; eauto. ssromega.
        rewrite Hpd in H. eapply semBindSize in H.
        move : H => [a' [Hg Hb]]. 
        destruct a'. 
        + left. exists (k, g).
          apply semReturnSize in Hb. inversion Hb; subst.
            by firstorder.
        + eapply IHfuel in Hb; eauto.
          * move : Hb => [Hsome | [Hnone Hcap]].
            left. eapply incl_bigcupl; [| eassumption ].
            apply setI_subset_compat.
            rewrite Hsub. apply setU_subset_r. by apply subset_refl.
            by apply subset_refl.   
            right. split; eauto.
            eapply eq_bigcapl. rewrite Hsub.
            rewrite setI_setU_distr. reflexivity.
            apply bigcap_setI_l. split; eauto.
            apply bigcap_setU_l. apply bigcap_set1.
            inversion Hnone; subst. eassumption.
          * rewrite Hsum in Hfst. rewrite <- Hfst. ssromega.
          * ssromega. }
    { move => [[[k g] [[Hg1 Hg2] [Ha1 Ha2]]] | [Hnone Hcap]]; simpl in *.
      - edestruct (pickDrop_In l) as [n [gs' Heq]]; eauto.
        destruct a; try discriminate.        
        exists n. split. rewrite <- HSum.
        eapply pickDrop_leq_top in Heq; eauto. by ssromega.
        rewrite Heq.
        eapply semBindSize. exists (Some a). split; eauto.
        apply semReturnSize. reflexivity.
      - destruct a; try discriminate.
        destruct (sum_fst l) eqn:Hsum.
        + eexists 0. split; eauto.
          rewrite pickDrop_def; eauto.
          eapply semBindSize. exists None. split.
          apply semReturnSize. reflexivity.
          subst. apply semBacktrackFuelDef; eauto.
        + subst.
          move: (pickDrop_exists l 0) => [Hex _].
          edestruct Hex as [k [g [gs' [Hin [Hpd [Hneq [Hsub [Hlen Hfst]]]]]]]]; eauto.
          exists 0. split; eauto. rewrite Hpd.
          eapply semBindSize. exists None. split.
          specialize (Hcap (k, g)). eapply Hcap.
          split; eauto.
          eapply IHfuel.
          rewrite Hsum in Hfst. rewrite <- Hfst. by ssromega.
          by ssromega.
          right. split. reflexivity.
          eapply incl_bigcapl; [| eassumption ].
          rewrite Hsub. apply setI_subset_compat.
          apply setU_subset_r. by apply subset_refl.
          by apply subset_refl. }
Qed.

Lemma semBacktrackSize {A} (l : list (nat * G (option A))) size :
  semGenSize (backtrack l) size <--> 
  (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGenSize x.2 size))) :|:
  ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGenSize x.2 size))).
Proof.
  eauto using semBacktrackFuel.
Qed.

Lemma semFoldGen_right :
  forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A) (s : nat),
    semGenSize (foldGen f bs a0) s <-->
    [ set an |
      foldr (fun b p => [set a_prev | exists a, a \in (semGenSize (f a_prev b) s :&: p)]) 
            [set an] bs a0].
Proof.
  move => A B f bs a0 s. rewrite /foldGen. 
   elim : bs a0 => [| b bs IHbs] a0 an. 
  - split. 
    + move/semReturnSize => ->. reflexivity. 
     + move => ->. now apply semReturnSize.
  - split. 
    + move/semBindSize => [a [H1 H2]]. 
       exists a. split => //. now apply IHbs.
    + move => [a [H1 H2]]. apply semBindSize. exists a. split => //.
       now apply IHbs. 
Qed.

Definition genPair {A B : Type} (ga : G A) (gb : G B) : G (A * B) :=
  liftGen2 pair ga gb.

Definition curry {A B C : Type} (f : A * B -> C) (a : A) (b : B) := f (a,b).

Definition uncurry {A B C : Type} (f : A -> B -> C) (ab : A * B) :=
  match ab with
  | (a,b) => f a b
  end.

Lemma mergeBinds :
  forall A B C (ga : G A) (gb : G B) (f : A -> B -> G C),
    semGen (bindGen ga (fun x => bindGen gb (f x))) <-->
    semGen (bindGen (genPair ga gb) (uncurry f)).
Proof.
  intros. unfold semGen. repeat setoid_rewrite semBindSize.
                                setoid_rewrite semReturnSize.
  intro c. split; intros [s [_ H]]; exists s; split; try by [].
  - destruct H as [a [Ha [b [Hb Hc]]]].
    exists (a,b). split. exists a. split; first by [].
                         exists b. split; first by [].
    reflexivity. by [].
  - destruct H as [[a b] [[a' [Ha [b' [Hb H]]]] Hc]].
    inversion H; subst; clear H.
    exists a. split. by []. exists b. split; by [].
Qed.    

Module QcDefaultNotation.

Notation " 'elems' [ x ] " := (elements x (cons x nil)) : qc_scope.
Notation " 'elems' [ x ; y ] " := (elements x (cons x (cons y nil))) : qc_scope.
Notation " 'elems' [ x ; y ; .. ; z ] " :=
  (elements x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'elems' ( x ;; l ) " :=
  (elements x (cons x l)) (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' [ x ] " := (oneof x (cons x nil)) : qc_scope.
Notation " 'oneOf' [ x ; y ] " := (oneof x (cons x (cons y nil))) : qc_scope.
Notation " 'oneOf' [ x ; y ; .. ; z ] " :=
  (oneof x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'oneOf' ( x ;; l ) " :=
  (oneof x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'freq' [ x ] " := (frequency x (cons x nil)) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ] " :=
  (frequency x (cons (n, x) (cons y nil))) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ; .. ; z ] " :=
  (frequency x (cons (n, x) (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'freq' ( ( n , x ) ;; l ) " :=
  (frequency x (cons (n, x) l)) (at level 1, no associativity) : qc_scope.

End QcDefaultNotation.

Module QcDoNotation.

Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'doM!' X <- A ; B" :=
  (bindGenOpt A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

End QcDoNotation.

Import QcDefaultNotation. Open Scope qc_scope.

(* CH: Reusing :: instead of ;; would have been nice, but I didn't manage *)

Lemma semElemsSize A (x : A) xs s : semGenSize (elems (x ;; xs)) s <--> x :: xs.
Proof. rewrite semElementsSize. reflexivity. Qed.

Lemma semOneOfSize A (g0 : G A) (gs : list (G A)) s :
  semGenSize (oneOf (g0 ;; gs)) s  <--> \bigcup_(g in (g0 :: gs)) semGenSize g s.
Proof. rewrite semOneofSize. reflexivity. Qed.

(* begin semElems *)
Lemma semElems A (x : A) xs : semGen (elems (x ;; xs)) <--> x :: xs.
(* end semElems *)
Proof. by rewrite semElements. Qed.

(* begin semOneOf *)
Lemma semOneOf A (g0 : G A) (gs : list (G A)) :
  semGen (oneOf (g0 ;; gs))  <--> \bigcup_(g in (g0 :: gs)) semGen g.
(* end semOneOf *)
Proof. by rewrite semOneof. Qed.

(* Operators like betterSized (better name pending) are guaranteed to
   produce size-monotonic generators (provided the body has this
   property). Note: this doesn't hold for sized! *)

Definition betterSized {A} (f : nat -> G A) :=
  sized (fun x => bindGen (choose (0, x)) f).

Program Instance betterSizedIndeedBetter {A} (f : nat -> G A) 
        (H: forall s, SizeMonotonic (f s)) :
  SizeMonotonic (betterSized f).
Next Obligation.
  rewrite /betterSized . 
  rewrite !semSizedSize !semBindSize !semChooseSize; last by []; last by [].
  move => a [s1' [/andP [_ H11] H12]].
  eexists. split; last by eapply monotonic; eauto. 
  apply/andP; split => //. by eapply leq_trans; eauto. 
Qed.

End GenHigh.
