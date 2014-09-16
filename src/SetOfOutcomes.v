Require Import Random AbstractGen RoseTrees.
Require Import Arith List seq ssreflect ssrbool ssrnat eqtype.

(* The monad carrier *)
Definition Pred (A : Type) := A -> Prop.

Definition bindP {A B} (m : Pred A) (f : A -> Pred B) : Pred B :=
  fun b => exists a, m a /\ f a b.

Definition returnP {A} (a : A) : Pred A :=
  fun x => eq a x.

Definition fmapP {A B} (f : A -> B) (a : Pred A) : Pred B :=
 bindP a (fun a => returnP (f a)).

Definition chooseP {A : Type} `{Random A} (p : A * A) : Pred A :=
  (fun a => Random.leq (fst p) a /\ Random.leq a (snd p)). 

Definition sizedP {A} (f : nat -> Pred A) : Pred A:=
  (fun a => exists n, f n a).

Definition suchThatMaybeP {A} (g : Pred A) (f : A -> bool)
: Pred (option A) :=
  fun b => (b = None) \/
           (exists y, b = Some y /\ g y /\ f y).


(* semantics of promoteP:
   all the nodes of a rose tree that satisfies the predicate
   have to satisfy the predicate of the corresponding node
   at the initial tree *)
(* Fixpoint promoteP {A : Type}   *)
(*            (m : Rose (Pred A)) : Pred (Rose A) := *)
(*   let makelst (l: list (Rose (Pred A))) : (Pred (list (Rose A))) :=  *)
(*       fold_right  *)
(*         (fun (m : Rose (Pred A)) (l' : Pred (list (Rose A))) => *)
(*            bindP (promoteP m) (fun (r : Rose A) => *)
(*            bindP l' (fun (l : list (Rose A)) => *)
(*            returnP (r :: l)))) (returnP [::]) l  *)
(*   in *)
(*   match m with *)
(*     | MkRose g l => *)
(*       bindP g (fun x : A => *)
(*       bindP (makelst (force l)) (fun (l' : list (Rose A)) => *)
(*       returnP (MkRose x (lazy l')))) *)
(*   end. *)

(* Semantics for promoteP that make the lemma about shrinking
   provable. We should try to prove it with the correct semantics *)
Fixpoint promoteP {A : Type}
           (m : Rose (Pred A)) : Pred (Rose A) :=
  match m with
    | MkRose g l =>
      bindP g (fun x : A =>
      returnP (MkRose x (lazy nil)))
  end.


 
Instance PredMonad : GenMonad Pred :=
  {
    bindGen := @bindP;
    returnGen := @returnP;
    fmapGen := @fmapP;
    choose := @chooseP;
    sized := @sizedP;
    suchThatMaybe := @suchThatMaybeP;
    promote := @promoteP
  }.

(* Equivalence on sets of outcomes *)
Definition set_eq {A} (m1 m2 : Pred A) :=
  forall A, m1 A <-> m2 A.

Infix "<-->" := set_eq (at level 70, no associativity) : pred_scope.

Open Scope pred_scope.

(* the set f outcomes m1 is a subset of m2 *)
Definition set_incl {A} (m1 m2 : Pred A) :=
  forall A, m1 A -> m2 A.

(* The set that is equal to A *)
Definition all {A} : Pred A := fun _ => True.

(* I don't think that this function will be a part if the common interface as
   Gen cannot implement it *)
Definition suchThat {A} (g : Pred A) (f : A -> bool) : Pred A :=
  (fun x => g x /\ f x).

(* Q: Can we plug into Matthieu's generic framework
   for rewriting with the lemmas below:

A New Look at Generalized Rewriting in Type Theory. Matthieu Sozeau
Journal of Formalized Reasoning 2 (1), December 2009, pp.41-62.
http://jfr.cib.unibo.it/article/view/1574/1077

A Gentle Introduction to Type Classes and Rewriting in Coq. Pierre
Castéran & Matthieu Sozeau, Misc, May 2012.
http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
*)

Lemma left_identity : forall {A B} (f : A -> Pred B) (a : A),
  (bindGen (returnGen a) f) <--> (f a).
Proof. intros. compute. firstorder. subst. assumption. Qed.


Lemma right_identity : forall {A} (m: Pred A),
  (bindGen m returnGen) <--> m.
Proof. intros. compute. firstorder. subst. assumption. Qed.

Lemma associativity : forall {A B C} (m : Pred A) (f : A -> Pred B)
                             (g : B -> Pred C),
  (bindGen (bindGen m f) g) <--> (bindGen m (fun x => bindGen (f x) g)).
Proof. intros. compute. firstorder. Qed.
 
(* Functor laws *)
Lemma fmap_id:
  forall A (a: Pred A), (fmapP id a) <--> (id a).
Proof.
  move => A pa. rewrite /fmapP /set_eq /bindP /returnP /id.
  move => a. split => [[a' [H1 H2]]| H] //=. by subst.
  by exists a; split.
Qed.

Lemma fmap_composition:
  forall A B C (a : Pred A) (f : A -> B) (g : B -> C),
    (fmapP g (fmapP f a)) <--> (fmapP (fun x => g (f x)) a).
Proof.
  move=> A B C P f g. rewrite /fmapP /set_eq /bindP /returnP /id. move=> pc.
  split=> [[b [[a [Pa fa]]] Heq]| [a [Pa Heq]]]; subst.
  + by exists a; split.
  + exists (f a); split=> //=.
    by exists a; split.
Qed.


(* Definitions of primitive combinators so we don't need to unfold the
   definitions each time *)

Lemma bindGen_def :
  forall {A B} (g : Pred A) (f : A -> Pred B),
    (bindGen g f) = fun b => exists a, g a /\ f a b.
Proof.
  by rewrite /bindGen.
Qed.

Lemma returnGen_def :
  forall {A} (a : A),
    returnGen a = eq a.
Proof.
  by rewrite /returnGen.
Qed.

Lemma fmapGen_def :
  forall {A B} (f : A -> B) (g : Pred A),
    fmapGen f g = fun b => exists a, g a /\ f a = b.
Proof.
  by rewrite /fmapGen.
Qed.

Lemma choose_def :
  forall {A} `{Random A} (p : A * A),
    @choose Pred _ _ _ p = fun (a : A) => Random.leq (fst p) a /\
                                          Random.leq a (snd p).
Proof.
  by rewrite /choose.
Qed.

Lemma sized_def :
  forall {A} (g : nat -> Pred A),
    sized g = fun a => exists n, g n a.
Proof.
  by rewrite /sized.
Qed.

Lemma suchThatMaybe_def :
  forall {A} (g : Pred A) (f : A -> bool),
    suchThatMaybe g f =
    fun b => (b = None) \/
             (exists y, b = Some y /\ g y /\ f y).
Proof.
  by rewrite /suchThatMaybe.
Qed.

(* Theorems about combinators *)

Lemma liftGen_def :
  forall {A B} (f: A -> B) (g: Pred A),
    liftGen f g =
    fun b =>
      exists a, g a /\ f a = b.
Proof.
  by rewrite /liftGen.
Qed.

Lemma liftGen2_def :
  forall {A B C} (f: A -> B -> C) (g1: Pred A) (g2: Pred B),
    liftGen2 f g1 g2 =
    fun b =>
      exists a1, g1 a1 /\
                 (exists a2, g2 a2 /\ f a1 a2 = b).
Proof.
  by rewrite /liftGen.
Qed.

Lemma liftGen3_def :
  forall {A B C D} (f: A -> B -> C -> D)
         (g1: Pred A) (g2: Pred B) (g3: Pred C),
    liftGen3 f g1 g2 g3 =
    fun b =>
      exists a1, g1 a1 /\
                 (exists a2, g2 a2 /\
                             (exists a3, g3 a3 /\ (f a1 a2 a3) = b)).
Proof.
  by rewrite /liftGen3.
Qed.

Lemma liftGen4_def :
  forall {A B C D E} (f: A -> B -> C -> D -> E)
         (g1: Pred A) (g2: Pred B) (g3: Pred C) (g4: Pred D),
    liftGen4 f g1 g2 g3 g4 =
    fun b =>
      exists a1, g1 a1 /\
                 (exists a2, g2 a2 /\
                             (exists a3, g3 a3 /\
                                         (exists a4, g4 a4 /\
                                                     eq (f a1 a2 a3 a4) b))).
Proof.
  by rewrite /liftGen4.
Qed.

Lemma liftGen5_def :
  forall {A B C D E G} (f: A -> B -> C -> D -> E -> G)
         (g1: Pred A) (g2: Pred B) (g3: Pred C) (g4: Pred D) (g5: Pred E),
    liftGen5 f g1 g2 g3 g4 g5 =
    fun b =>
      exists a1, g1 a1 /\
                 (exists a2, g2 a2 /\
                             (exists a3, g3 a3 /\
                                         (exists a4, g4 a4 /\
                                                     (exists a5, g5 a5 /\
                                                                 (f a1 a2 a3 a4 a5) = b)))).
Proof. 
  by rewrite /liftGen5.
Qed.

(* Specifications for derived constructs *)
 
Lemma sequenceGen_equiv :
  forall {A} (gs : list (Pred A)),
    sequenceGen gs <--> fun l => length l = length gs /\
                                 forall x, In x (zip l gs) -> (snd x) (fst x).
Proof.
  Opaque bindGen returnGen.
  rewrite /set_eq /sequenceGen.
  move => A gs l. split; rewrite /returnGen /bindGen /PredMonad /bindP /returnP.
  - elim : gs l => //= [| g gs IHxs] l Hfold; first by subst.
    case: l Hfold => //= [| b bs] [a [ga [l  [Hfold Hret]]]].
    + discriminate.
    + move: Hret => [Heq1 Heq2]; subst.
      move/IHxs: (Hfold) => [Heq H].
      split.
      * by rewrite Heq.
      * move=> x [Heq1 | HIn]. by subst => //=. by auto.
  - elim : gs l => //= [| g gs IHgs] l [Hlen H].
    + by symmetry; apply/size0nil.
    + case: l Hlen H => //= b bs [Hle] H.
      exists b. split; first by apply (H (b, g)); left.
      exists bs. split => //=.
      apply IHgs. split => //= x HIn. by auto.
Qed.

Lemma foldGen_cat:
  forall {A B : Type} (f : A -> B -> Pred A) (bn : list B) (a0 : A) (bs : B),
    foldGen f (bn ++  (bs :: nil)) a0 <--> 
    bindGen (foldGen f bn a0) (fun an => 
    f an bs).
Proof.
  move=> A B f bn a0 bs an.
  elim : bn a0 an bs => [| b bn IHbs] a0 an bs.
  - simpl. split.
    + move=> [a [Hf an']]. rewrite returnGen_def in an'; subst.
      exists a0. split => //.
    + move=> [a [Heq Hf]]. rewrite returnGen_def in Heq; subst.
      exists an. split => //.
  - simpl. split.
    + move=> [a [Hf /IHbs [a' [Hg Hf']]]]. exists a'. split => //. 
      exists a=> //.
    + move=> [a [[a' [Hf' Hg]] Hf]]. exists a'. split => //. 
      apply IHbs. eexists. split; eassumption.
Qed.
    
Lemma foldGen_left_equiv :
  forall {A B : Type} (f : A -> B -> Pred A) (bs : list B) (a0 : A),
    foldGen f bs a0 <-->
    foldl (fun g b => fun x => exists a, g a /\ f a b x) (eq a0) bs.
Proof.
  move=> A B f bs a0 an. rewrite /foldGen.
  elim/last_ind : bs a0 an => [| b bs IHbs] a0 an.
  - split; auto.
  - rewrite -cats1. rewrite foldl_cat /=. split.
    + move => /foldGen_cat [a' [Hfold Hf]].  
      exists a'. split => //. by apply IHbs. 
    + move => [a' [Hfold Hf]]. apply foldGen_cat. 
      exists a'. split=> //. by apply IHbs.
Qed.


Lemma foldGen_right_equiv :
  forall {A B : Type} (f : A -> B -> Pred A) (bs : list B) (a0 : A),
    foldGen f bs a0 <-->
    fun an => 
      foldr (fun b p => fun a_prev => exists a, f a_prev b a /\ p a) 
            (eq an) bs a0.
Proof.
  move=> A B f bs a0 an. rewrite /foldGen.
  elim : bs a0 an => [| b bs IHbs] a0 an;
  try (rewrite returnGen_def); try (rewrite bindGen_def); split=> //=;
  move => [a1 [fa0 /IHbs H]]; by exists a1.
Qed.
 
(* Our induction principle for fold; might be useful in proofs? *)
Section invariants.

Variable A : Type.
Variable B : Type.
Variable I : A -> seq B -> Prop.
Variable f : A -> B -> A.

Theorem ind : forall acc' xs',
  I acc' xs' ->
  (forall x xs acc, I acc (x :: xs) -> I (f acc x) xs) ->
  I (fold_left f xs' acc') nil.
Proof.
  move => acc' xs'. move : acc'. elim : xs' => //= acc' xs' IH acc init step.
  apply IH; by apply step.
Qed.

End invariants.

Lemma vectorOf_equiv: 
  forall {A : Type} (k : nat) (g : Pred A),
    vectorOf k g <--> fun l => (length l = k /\ forall x, In x l -> g x).
Proof.
  move=> A k g l. rewrite /vectorOf. split. 
  - elim : l k => //= [| b bs IHbs] k Hfold;
    rewrite /returnGen /bindGen /PredMonad /bindP /returnP;
    case: k Hfold => //= k [a [ga [l [Hfold ret]]]]; first by []. 
    case: ret => Heq1 Heq2; subst.
    move/IHbs: Hfold => [Heq Hforall]. subst.
      by split => //= x [Heq | HIn]; subst; auto.
  - elim : l k => //= [| b bs IHbs] k [Heq Hforall];
    rewrite returnGen_def; case: k Heq => //= k [Heq]; subst.
    rewrite bindGen_def. exists b.
    split; first by apply (Hforall b); left.
    rewrite bindGen_def. exists bs.
    split => //=. apply IHbs. by split => //=; auto.
Qed.

Lemma listOf_equiv:
  forall {A : Type} (g : Pred A),
    listOf g <--> fun l => (forall x, In x l -> g x).
Proof.
   move=> A g a. rewrite /listOf sized_def.
   split.
   + move => [n  Hgen].
     rewrite bindGen_def in Hgen.
     by move: Hgen => [n' [_ /vectorOf_equiv [_ H]]].
   + move => Hforall.
     exists (length a).
     rewrite bindGen_def. exists (length a).
     split.
     rewrite choose_def; split => //.
     by apply/vectorOf_equiv.
Qed.

Lemma seqnth_In :
  forall (A : Type) (n : nat) (l : seq A) (d : A),
    (n < length l) -> In (nth d l n) l.
Proof.
  move=> A n l. elim : l n => //= x xs IHxs. case => //= [| n] d Hlt.
  + by left.
  + by right; auto.
Qed.
 
Lemma oneof_equiv:
  forall {A} (l : list (Pred A)) (def : Pred A),
    (oneof def l) <-->
     (fun e => (exists x, (In x l /\ x e)) \/ (l = nil /\ def e)).
Proof.
  move=> A l def a.
  rewrite /oneof.
  split; rewrite bindGen_def choose_def;
  [ move=> [n [[/= Hlo Hhi] H]] |
    move=> /= [[p [Hin pa]] | [Hnil Hdef]]].
  - case: l Hhi Hlo H => //= [|x xs] Hhi Hlo H.
    + by right; split; case : n H Hhi Hlo => //=.
    + case: n H Hhi Hlo => [| n] H Hhi Hlo.
      * by left; eexists; split ; [by left|].
      * left. exists (nth def xs n). split => //=.
        right. apply seqnth_In.
        by rewrite -[X in _ < X - 1]addn1 -[X in _ < _ - X]add0n
                   subnDr subn0 in Hhi.
  -  + apply In_split in  Hin. move: Hin => [l1 [l2 Heq]]. subst.
       exists (length l1).
       split. split => //=. 
       by rewrite app_length -addnBA leq_addr.
       rewrite nth_cat  //=.
       have -> : length l1 = size l1 by [].
       by rewrite ltnn -[X in X - X]addn0 subnDl sub0n.
     + subst. exists 0. split => //.
Qed.
 
Lemma elements_equiv :
  forall {A} (l: list A) (def : A),
    (elements def l) <--> (fun e => In e l \/ (l = nil /\ e = def)).
Proof.
  move => A l def a.
  rewrite /elements bindGen_def choose_def /=.
  split => [[n [[Hlo Hhi] H]] |
            [H | [H1 H2]]]; subst. 
  - rewrite returnGen_def in H. subst.
    case : l Hhi Hlo => //= [| x xs] Hhi Hlo.
    + rewrite sub0n leqn0 in Hhi.
      move/eqP : Hhi => Hhi; subst. by right; split.
    + left. case: n Hhi Hlo => [| n] Hhi Hlo.
      by left.
      right; apply/nth_In/leP.
      by rewrite -[X in _ < X - _]addn1 -{2}[1]add0n subnDr subn0 in Hhi.
  - + apply in_split in H. move: H => [l1 [l2 Heq]]; subst.
      exists (length l1). rewrite returnGen_def. split. split => //=.
      by rewrite app_length -addnBA leq_addr.
      by rewrite app_nth2 //= NPeano.Nat.sub_diag.
    + subst. exists 0. split => //.
Qed.

(* A rather long frequency proof, probably we can do better *)

Lemma sum_fst_zero:
  forall {A} (l: list (nat * A)),
           sumn [seq fst i | i <- l] = 0 <-> forall x, In x l -> fst x == 0.
Proof.
  move=> A l.
  split. elim : l => //= x xs IHxs /plus_is_O [Heq1 Heq2] [n a] [H1 | H2].
  by apply/eqP; subst.
  by apply IHxs.
  elim l => // x xs IHxs H. simpl.
  apply NPeano.Nat.eq_add_0. split.
  apply/eqP. apply H. by constructor.
  apply IHxs. move=> x' HIn. apply H.
  constructor(exact HIn).
Qed.

Lemma pick_filter:
  forall {A} (l: list (nat * Pred A)) n def,
    pick def n l = pick def n (filter (fun x => 0 != fst x) l).
Proof.
  move => A l n def.
  elim: l n => //=. case=> //= n' p xs IHxs n.
  remember (n < n'). case: b Heqb => Heqb. case: n' Heqb => //= n' Heqb.
  by rewrite -Heqb.
  case: n' Heqb => //= [|n'] Heqb.
  by rewrite subn0.
  by rewrite -Heqb.
Qed.


Lemma filter_forall :
  forall {A} (l: list A) (P : A -> bool) (x: A),
    In x (filter P l) <-> P x /\ In x l.
Proof.
  move => A l P x. split.
  + move=> HIn. by apply/and_comm/filter_In.
  + by move/and_comm/filter_In => Hand.
Qed.

Lemma filter_nil :
  forall {A} (l : list A) (P : A -> bool),
    (forall x, In x l -> P x = false) -> filter P l = [::].
Proof.
  move => A l P H. elim : l H => //= x xs IHxs H.
  rewrite H. apply IHxs => x' HIn. by apply H; right.
  by left.
Qed.

Lemma not_lt : forall n m, (false = (n < m)) -> (m <= n).
Proof.
  move => n m. by elim: n m=> [| n IHn]; case.
Qed.

Lemma pick_def :
  forall {A} (l: list (nat * Pred A)) n def,
    sumn [seq fst i | i <- l] <= n ->
    pick def n l = (0, def).
Proof.
  move=> A l n def Hleq.
  elim : l n Hleq => //=. case=> //= i p l IHl n Hleq.
  remember (n < i). case: b Heqb => Heqb. symmetry in Heqb.
  have : i + sumn [seq fst i0 | i0 <- l] < i
    by apply (leq_ltn_trans Hleq).
  rewrite -ltn_subRL.
  by have -> : forall i, (i - i) = 0 by elim.
  apply IHl.
  rewrite -(leq_add2r i) subnK. by rewrite addnC.
  by apply/not_lt.
Qed.

Lemma pick_exists :
  forall {A} (l: list (nat * Pred A)) n def,
    n <  sumn [seq fst i | i <- l] <->
    exists x, In x l /\ pick def n l = x /\ fst x <> 0.
Proof.
  move => A l n def. split.
  * move => Hlt.
    elim : l n Hlt => //. case => i p xs IHxs n Hlt.
    rewrite map_cons -cat1s sumn_cat //= addn0 in Hlt.
    move/(_ (n-i)) : IHxs => IHxs.  simpl.
    remember (n < i). case: b Heqb => [Heqb | /not_lt Heqb].
    + exists (i, p). split => //=. by left.  split => //=.
      move => contra; subst. by rewrite ltn0 in Heqb.
    + rewrite -(ltn_add2r i) [X in _  < X]addnC subnK // in IHxs.
      move/(_ Hlt) : IHxs => [x [H1 [H2 H3]]].
      by exists x; split; [right | split].
  * move => [x [HIn [Hpick Hneq]]].
    remember (n < sumn [seq fst i | i <- l]).
    case: b  Heqb => //= /not_lt/pick_def H.
    rewrite H in Hpick. rewrite -Hpick //= in Hneq.
Qed.
 
Lemma pick_In :
  forall {A} (l: list (nat * Pred A)) x def,
    In x l /\ fst x <> 0 ->
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

Lemma frequency_equiv :
  forall {A} (l : list (nat * Pred A)) (def : Pred A),
    (frequency' def l) <-->
    (fun e => (exists n, exists g, (In (n, g) l /\ g e /\ n <> 0)) \/
              ((l = nil \/ (forall x, In x l -> fst x = 0)) /\ def e)).
Proof.
  move=> A l def a.
  rewrite /frequency' /bindGen /PredMonad /bindP /choose /Randomnat //=.
  split => [[n [[/= Hlo Hhi] H]] |
            [[n [g [H1 [H2 H3]]]] | [[H1 | H1] H2]]].
  - rewrite -(leq_add2r 1) addn1 in Hhi.
    remember (sumn [seq fst i | i <- l]) as sum.
    case: sum Heqsum Hhi H => [|sum] Heqsum Hhi H.
    + symmetry in Heqsum. move/(sum_fst_zero l): Heqsum => HIn.
      rewrite pick_filter filter_nil //= in H.
      right. split => //=; right => x HIn'. by apply/eqP; auto.
      move=> x HIn'. by move/eqP: (HIn x HIn') => ->.
    + rewrite subnK // Heqsum in Hhi.
      move/(pick_exists l n def): Hhi => [[i p] //= [H1 [H2 H3]]].
      left. exists i. exists p. by rewrite H2 // in H.
  - + have Hand: In (n, g) l /\ fst (n, g) <> 0 by split.
      move : (pick_In l (n, g) def Hand) => [n' Hpick].
      exists n'. split => //=. split => //=.
      have Hlt: n' < sumn [seq fst i | i <- l]
        by apply/(pick_exists _ _ def)=> //=; exists (n, g).
      rewrite -(leq_add2r 1) addn1 subnK. by auto.
      case: (sumn [seq fst i | i <- l]) Hlt => //=.
      by rewrite  Hpick.
    + * subst. simpl. rewrite sub0n. exists 0. split => //=.
      * exists 0. split. split => //=. 
        elim: l H1 => //=. case => n p l IHl H1.
        move/(_ (n, p)): (H1) => //= H. rewrite H => //=.
        rewrite subn0. by auto. 
        by left.
Qed.
 

(* Useless theorems.. *)
Lemma fold_prop :
  forall {A B} (f : A -> B -> A -> Prop) l P P',
    (P <-> P') ->
    (foldl (fun p (args : (A* (B *A))) =>
                         let (a_prev, ba) := args in
                         p /\ f a_prev (fst ba) (snd ba)) P l
     <->
     foldl (fun p (args : (A* (B *A))) =>
                         let (a_prev, ba) := args in
                         p /\ f a_prev (fst ba) (snd ba)) P' l).
Proof.
  move => A B f l.
  elim: l  => //=. case => a_prev. case => b a xs //= IHxs P P'.
  - move => Hequiv. apply/(IHxs (P /\ f a_prev b a))=> //=.
    by split; move => [H1 H2]; split => //=; auto; apply/Hequiv.
Qed.
 
Lemma foldl_prop : forall {A B} (f : A -> B -> A -> Prop) l init P,
  P /\ foldl (fun p (args : (A* (B *A))) =>
                         let (a_prev, ba) := args in
                         p /\ f a_prev (fst ba) (snd ba)) init l <->
  foldl (fun p (args : (A* (B *A))) =>
                         let (a_prev, ba) := args in
                         p /\ f a_prev (fst ba) (snd ba)) (P /\ init) l.
Proof.
  move=> A B f l init P.
  elim : l P init => //=. case => a_prev. case => b a xs IHxs P init.
  split.
  + move => //= [HP Hfold].
    have: ((P /\ init) /\ f a_prev b a) <-> (P /\ init /\ f a_prev b a)
      by apply and_assoc.
    move/fold_prop => fold_eq.
    apply/fold_eq. apply IHxs. by split.
  + move/IHxs =>  [[HP Hinit] Hfold]. simpl in *.
    split => //=. apply IHxs. split => //=.
Qed.

Lemma zip_nil_l : forall {A B} (l : seq A), zip (@nil B) l = [::].
Proof. by move => A B; case => //. Qed.

Lemma zip_nil_r : forall {A B} (l : seq A), zip l (@nil B) = [::].
Proof. by move => A B; case => //. Qed.
