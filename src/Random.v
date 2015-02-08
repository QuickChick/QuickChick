Require Import ssreflect ssrbool ssrnat eqtype.
Require Import ZArith.

(* We axiomatize a random number generator
   (currently written in OCaml only) *)
Axiom RandomSeed : Type.
Axiom randomSeedInhabitant : RandomSeed.

Axiom randomNext     : RandomSeed -> Z * RandomSeed.
Axiom randomGenRange : RandomSeed -> Z * Z.
Axiom mkRandomSeed   : Z          -> RandomSeed.
Axiom newRandomSeed  : RandomSeed.

Axiom randomSplit    : RandomSeed   -> RandomSeed * RandomSeed.
Axiom randomSplitAssumption :
  forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).

CoInductive RandomSeedTree :=
| RstNode : RandomSeed -> RandomSeedTree -> RandomSeedTree -> RandomSeedTree.

Definition root_rst (rst : RandomSeedTree) : RandomSeed :=
  match rst with
  | RstNode root _ _ => root
  end.

Definition left_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ t1 _ => t1
  end.

Definition right_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ _ t2 => t2
  end.

Lemma rst_eta : forall rst : RandomSeedTree,
  rst = RstNode (root_rst rst) (left_rst rst) (right_rst rst).
Proof. destruct rst. reflexivity. Qed.

CoFixpoint mkSeedTree (s : RandomSeed) : RandomSeedTree :=
  let (s1, s2) := randomSplit s in
  RstNode s (mkSeedTree s1) (mkSeedTree s2).

Lemma mkSeedTreeHelper : forall (r r1 r2 : RandomSeed),
                           randomSplit r = (r1, r2) ->
                           mkSeedTree r = RstNode r (mkSeedTree r1) (mkSeedTree r2).
Proof.
  move => r r1 r2 H. pattern (mkSeedTree r). rewrite -> rst_eta.
  simpl. rewrite H. reflexivity.
Qed.

Inductive SplitDirection := Left | Right.

Definition SplitPath := list SplitDirection.

Require Import List. Import ListNotations.
Fixpoint varySeedAux (p : SplitPath) (rst : RandomSeedTree) : RandomSeed :=
  let '(RstNode s t1 t2) := rst in
  match p with 
    | [] => s 
    | Left  :: p' => varySeedAux p' t1
    | Right :: p' => varySeedAux p' t2
  end.

Definition varySeed (p : SplitPath) (s : RandomSeed) : RandomSeed :=
  varySeedAux p (mkSeedTree s).

Inductive SeedTree := 
| SeedTreeUndef : SeedTree
| SeedTreeLeaf : RandomSeed -> SeedTree
| SeedTreeNode : SeedTree -> SeedTree -> SeedTree.

Inductive SubSeedTree : SeedTree -> RandomSeedTree -> Prop :=
| SubUndef : forall (rst : RandomSeedTree), SubSeedTree SeedTreeUndef rst
| SubLeaf  : forall (s : RandomSeed) (rst1 rst2 : RandomSeedTree),
               SubSeedTree (SeedTreeLeaf s) (RstNode s rst1 rst2)
| SubNode  : forall (st1 st2 : SeedTree) (rst1 rst2 : RandomSeedTree) (s : RandomSeed),
               SubSeedTree st1 rst1 -> 
               SubSeedTree st2 rst2 ->
               SubSeedTree (SeedTreeNode st1 st2) (RstNode s rst1 rst2).

Fixpoint varySeed' (st : SeedTree) (p : SplitPath) : option RandomSeed :=
  match st with 
    | SeedTreeUndef => None
    | SeedTreeLeaf s => 
      match p with 
        | [] => Some s 
        | _  => None 
      end
    | SeedTreeNode st1 st2 => 
      match p with 
        | [] => None 
        | Left  :: p' => varySeed' st1 p'
        | Right :: p' => varySeed' st2 p'
      end
  end.

Lemma pathAgreesOnSubTree : forall (st : SeedTree) (rst : RandomSeedTree) (p : SplitPath)
                                   (s : RandomSeed), 
                              SubSeedTree st rst -> 
                              varySeed' st p = Some s ->
                              varySeedAux p rst = s.
Proof.
induction st.
+ intros. simpl in H0. congruence.
+ intros. simpl in H0.
  destruct p eqn:P.
  - inversion H. simpl. inversion H0. reflexivity.
  - inversion H0.
+ intros. simpl in H0.
  destruct p eqn:P.
  - inversion H0.
  - inversion H; subst. 
    destruct s0 eqn:S0.
    * simpl. apply IHst1; auto.
    * simpl. apply IHst2; auto.
Qed.

Lemma splitExpand : forall (st : SeedTree), exists (s : RandomSeed), SubSeedTree st (mkSeedTree s).
  induction st.
  + exists randomSeedInhabitant. apply SubUndef.
  + exists r. 
    destruct (randomSplit r) eqn:Split.
    rewrite (mkSeedTreeHelper r r0 r1); auto.
    apply SubLeaf.
  + inversion IHst1 as [s1 H1].
    inversion IHst2 as [s2 H2].
    pose proof (randomSplitAssumption s1 s2) as [seed Hyp].
    exists seed.
    rewrite (mkSeedTreeHelper seed s1 s2); auto.
    apply SubNode; auto.
Qed.    

Inductive PrefixFree : list SplitPath -> Prop :=
| FreeNil : PrefixFree []
| FreeCons : forall (p : SplitPath) (l : list SplitPath), 
               PrefixFree l ->
               (forall (p' : SplitPath), In p' l -> 
                                        (forall p1 p2, p' ++ p1 = p ++ p2-> False)) ->
                                        PrefixFree (p :: l).

Lemma prefixFreeSingleton : forall p, PrefixFree [p].
intro.
apply FreeCons.
+ apply FreeNil.
+ intros. inversion H.
Qed.

Lemma prefixFreeEmpty : forall l, PrefixFree ([] :: l) -> l = [].
intros.
destruct l; auto.
inversion H.
subst.
pose proof H3 l.
assert (In l (l :: l0)) by (left; auto).
eapply H0 in H1. inversion H1.
instantiate (2 := []). rewrite app_nil_r; simpl; eauto.
Qed.

Inductive correspondingSeedTree (l : list SplitPath) (st : SeedTree) : Prop :=
| Corresponding : (forall (p : SplitPath), In p l <-> exists s, varySeed' st p = Some s) ->
                  PrefixFree l ->
                  correspondingSeedTree l st.

Lemma corrEmptyUndef : correspondingSeedTree [] SeedTreeUndef.
  apply Corresponding. 
  + split.
    - intro Contra; inversion Contra.
    - intro Hyp. inversion Hyp as [x Contra]. inversion Contra.
  + apply FreeNil.
Qed.

Lemma PrefixFreeWithNil : forall l, PrefixFree ([] :: l) -> l = [].
  intros.
  inversion H; subst.
  destruct l eqn:L; auto.
  pose proof (H3 l0).
  assert (In l0 (l0 :: l1)) by (left; auto).
  eapply H0 in H1.
  + inversion H1.
  + instantiate (1 := l0). instantiate (1 := []). rewrite app_nil_r. auto.
Qed.

Lemma corrEmptyLeaf : forall s l, correspondingSeedTree l (SeedTreeLeaf s) -> l = [[]].
  intros. 
  inversion H as [P H'].
  pose proof (P []).
  inversion_clear H0.
  assert (In [] l) by (apply H2; exists s; auto).
  destruct l eqn:L.
  + inversion H0.
  + destruct s0 eqn:S0.
    - apply PrefixFreeWithNil in H'. subst. auto.
    - pose proof (P (s1 :: s2)).
      assert (In (s1 :: s2) ((s1 :: s2) :: l0)) by (left; auto).
      apply H3 in H4.
      inversion H4.
      simpl in H5.
      inversion H5.
Qed.


Lemma corrNodeNonEmpty : forall st1 st2 l p, 
                           correspondingSeedTree l (SeedTreeNode st1 st2) ->
                           In p l -> p <> [].
unfold not; intros.
inversion H.
pose proof H2 p.
apply H4 in H0.
inversion H0.
subst.
simpl in H5.
inversion H5.
Qed.

Hint Resolve corrEmptyUndef.
Hint Resolve corrNodeNonEmpty.
Definition Direction_eq_dec : forall (d1 d2 : SplitDirection), 
                                d1 = d2 \/ d1 <> d2.
decide equality.
Qed.

Definition eq_dir_b (d1 d2 : SplitDirection) : bool :=
  match d1,d2 with
    | Left, Left => true
    | Right, Right => true
    | _, _ => false
  end.

Lemma eq_dir_b_eq : forall d1 d2, eq_dir_b d1 d2 = true <-> d1 = d2.
intros.
unfold eq_dir_b.
destruct d1; destruct d2; split; auto; intro Contra; inversion Contra.
Qed.

Definition refineList (d : SplitDirection) (l : list SplitPath) : list SplitPath := 
  map (@tl SplitDirection) (filter (fun p => match hd_error p with 
                             | Some d' => eq_dir_b d d'
                             | _       => false
                           end) l).

Lemma refineCorrect : forall d l p, In p (refineList d l) -> In (d :: p) l.
intros d l p.
unfold refineList.
rewrite in_map_iff.
intros.
inversion H; clear H.
inversion H0; clear H0.
generalize H1; clear H1.
rewrite filter_In.
intros.
inversion H0; clear H0.
unfold tl in H.
destruct x eqn:X.
+ simpl in H2. inversion H2.
+ simpl in H2. apply eq_dir_b_eq in H2. subst. auto.
Qed.

Lemma refineCorrect' : forall d l p, In (d :: p) l -> In p (refineList d l).
intros.
unfold refineList.
apply in_map_iff.
exists (d :: p).
split; auto.
apply filter_In.
split; simpl; auto.
unfold eq_dir_b; destruct d; auto.
Qed.

Lemma refinePreservesPrefixFree : forall d l, PrefixFree l -> PrefixFree (refineList d l).
  intros.
  induction l.
  - unfold refineList; constructor.
  - destruct a eqn:A; subst.
    * apply prefixFreeEmpty in H. subst. unfold refineList. simpl. constructor.
    * destruct s eqn:S; destruct d; subst.
      + unfold refineList; simpl.
        eapply FreeCons.
        - apply IHl. inversion H; auto.
        - intros. inversion H; subst; clear H.
          apply in_map_iff in H0.
          inversion H0; subst; clear H0.
          inversion H; subst; clear H.
          apply filter_In in H2. inversion H2; subst; clear H2.
          destruct x eqn:X; simpl in *. inversion H0.
          destruct s eqn:S; simpl in *. 
          pose proof H5 (Left :: l0).
          eapply H2 in H; auto.
          simpl. instantiate (1 := p2). instantiate (1:= p1). rewrite H1. auto.
          inversion H0.
      + unfold refineList; simpl. apply IHl.
        inversion H. auto.
      + unfold refineList; simpl. apply IHl.
        inversion H. auto.
      + unfold refineList; simpl.
        eapply FreeCons.
        - apply IHl. inversion H; auto.
        - intros. inversion H; subst; clear H.
          apply in_map_iff in H0.
          inversion H0; subst; clear H0.
          inversion H; subst; clear H.
          apply filter_In in H2. inversion H2; subst; clear H2.
          destruct x eqn:X; simpl in *. inversion H0.
          destruct s eqn:S; simpl in *. 
          inversion H0.
          pose proof H5 (Right :: l0).
          eapply H2 in H; auto.
          simpl. instantiate (1 := p2). instantiate (1:= p1). rewrite H1. auto.
Qed.

Program Fixpoint addToTree (st : SeedTree) (p : SplitPath) (s : RandomSeed)
        (l : list SplitPath)
        (Corr : correspondingSeedTree l st)
        (Pref : forall p', In p' l -> (forall p1 p2, p ++ p1 = p' ++ p2 -> False))
: SeedTree :=
  match st with 
    | SeedTreeUndef => 
      match p with 
        | [] => SeedTreeLeaf s
        | Left  :: p' => SeedTreeNode (addToTree SeedTreeUndef p' s [] _ _) SeedTreeUndef
        | Right :: p' => SeedTreeNode SeedTreeUndef (addToTree SeedTreeUndef p' s [] _ _) 
      end
    | SeedTreeLeaf s => _  (* Contradiction! *)
    | SeedTreeNode st1 st2 =>
      match p with 
        | [] => _ (* Contradiction! *)
        | Left  :: p' => SeedTreeNode (addToTree st1 p' s (refineList Left l) _ _) st2
        | Right :: p' => SeedTreeNode st1 (addToTree st2 p' s (refineList Right l) _ _)
      end
  end.
Next Obligation.
apply corrEmptyLeaf in Corr. subst.
pose proof (Pref []).
exfalso.
eapply H.
+ left; auto.
+ instantiate (2 := []). rewrite app_nil_r. simpl. eauto.
Qed.
Next Obligation.  
eapply Corresponding.
+ split; intros.
  - apply refineCorrect in H.
    inversion Corr.
    pose proof (H0 (Left :: p)).
    apply H2 in H.
    inversion H.
    simpl in H3.
    exists x.
    auto.
  - inversion H.
    inversion Corr.
    assert (exists seed, varySeed' (SeedTreeNode st1 st2) (Left :: p) = Some seed)
      by (exists x; auto).
    apply H1 in H3.
    apply refineCorrect'; auto.
+ inversion Corr.
  apply refinePreservesPrefixFree.
  auto.
Qed.
Next Obligation.
eapply Pref.
instantiate (1:= Left :: p'0).
apply refineCorrect; auto.
instantiate (1:= p2). instantiate (1:=p1). simpl. rewrite H0. auto.
Qed.
Next Obligation.
eapply Corresponding.
+ split; intros.
  - apply refineCorrect in H.
    inversion Corr.
    pose proof (H0 (Right :: p)).
    apply H2 in H.
    inversion H.
    simpl in H3.
    exists x.
    auto.
  - inversion H.
    inversion Corr.
    assert (exists seed, varySeed' (SeedTreeNode st1 st2) (Right :: p) = Some seed)
      by (exists x; auto).
    apply H1 in H3.
    apply refineCorrect'; auto.
+ inversion Corr.
  apply refinePreservesPrefixFree.
  auto.
Qed.
Next Obligation.
eapply Pref.
instantiate (1:= Right :: p'0).
apply refineCorrect; auto.
instantiate (1:= p2). instantiate (1:=p1). simpl. rewrite H0. auto.
Qed.

Theorem topLevelSeedTheorem : (* Need a better name :P *)
  forall (l : list SplitPath) (f : SplitPath -> RandomSeed),
    PrefixFree l -> exists (s : RandomSeed), 
                      forall p, In p l -> varySeed p s = f p.
Admitted.
(*

Fixpoint addToTree (p : SplitPath) (s : RandomSeed) (acc : SeedTree) : SeedTree :=
  match p with 
    | [] -> 

Fixpoint mkPathTree (acc : SeedTree) (l : list SplitPath) (f : SplitPath -> RandomSeed) 
: SeedTree := 
  match l with  
    | [] => acc 
    | p :: ps => mkPathTree (addToTree p (f p) acc) ps f 
  end.
      match p with 
        | 
      


Inductive Prefix : SplitPath -> SplitPath -> Prop :=
| PreNil  : forall (p : SplitPath), Prefix [] p
| PreCons : forall (d : SplitDirection) (p1 p2 : SplitPath),
              Prefix p1 p2 -> Prefix (d :: p1) (d :: p2).



Program Fixpoint prefixFreePathTree (l : list SplitPath) (NonEmpty : l = [] -> False) 
        (Hyp : PrefixFreePaths l) : SeedTree :=
  match l with 
    | [] => _
    | 
  end.



Inductive ExpandsTo (s : RandomSeed) (t : SeedTree): Prop := 
  | ExpandsLeaf : t = SeedTreeLeaf s -> ExpandsTo s t
  | ExpandsNode : forall s1 s2 t1 t2, 
                    (s1, s2) = randomSplit s -> 
                    ExpandsTo s1 t1 -> 
                    ExpandsTo s2 t2 -> 
                    t = SeedTreeNode t1 t2 -> 
                    ExpandsTo s t.

Lemma splitExpand : forall (t : SeedTree), exists (s : RandomSeed), ExpandsTo s t.
  induction t.
  + inversion IHt1 as [s1 H1].
    inversion IHt2 as [s2 H2].
    pose proof (randomSplitAssumption s1 s2) as [seed Hyp].
    exists seed.
    eapply ExpandsNode; eauto.
  + exists r. by apply ExpandsLeaf.
Qed.

(* Vary a random seed based on a path *) 
(* left <-> false, right <-> true *)
Definition boolVary (b : bool) (s : RandomSeed) : RandomSeed :=
  let (s1, s2) := randomSplit s in
  if b then s2 else s1.

(* 
Fixpoint varySeed (p : list bool) (s : RandomSeed) : RandomSeed :=
  match p with 
    | [] => boolVary true s 
    | b :: bs => varySeed bs (boolVary b (boolVary false s))
  end.
*)

Require Import Recdef.
Require Import Numbers.Natural.Peano.NPeano.

Function varySeed (n : nat) (s : RandomSeed) {measure (fun n => n) n} : RandomSeed := 
  match n with 
    | O => boolVary true s
    | _ => boolVary (beq_nat (modulo n 2) 0) (boolVary false (varySeed (n / 2) s))
  end.
Proof.
intros; subst; apply Nat.div_lt; [apply lt_0_Sn | ]; auto.
Defined. 

Lemma natSetGivesLeafTree : forall (max : nat) (f : nat -> RandomSeed), 
                              exists (lt : LeafTree), 
                                forall (n : nat), n <= max -> 
                                  varySeed n .
                              
*)                              



(* Primitive generator combinators and some basic soundness
   assumptions about them *)
Axiom randomRBool : bool * bool -> RandomSeed -> bool * RandomSeed.
Axiom randomRBoolCorrect :
  forall b b1 b2,
    implb b1 b = true /\ implb b b2 = true <->
    exists seed, (fst (randomRBool (b1, b2) seed)) = b.
Axiom randomRNat  : nat  * nat  -> RandomSeed -> nat * RandomSeed.
Axiom ramdomRNatCorrect:
  forall n n1 n2,
    n1 <= n /\ n <= n2 <->
    exists seed, (fst (randomRNat (n1, n2) seed)) = n.
Axiom randomRInt  : Z * Z    -> RandomSeed -> Z * RandomSeed.
Axiom ramdomRIntCorrect:
  forall z z1 z2,
    Z.leb z1 z /\ Z.leb z z2 <->
    exists seed, (fst (randomRInt (z1, z2) seed)) = z.


(* A small experiment showing that infinite random trees
   are a potential model of the randomSplitAssumption *)

Module InfiniteTrees.
  CoInductive RandomSeed : Type :=
  | Node : bool -> RandomSeed -> RandomSeed -> RandomSeed.

  Definition randomSplit (s : RandomSeed) :=
    match s with
    | Node b s1 s2 => (s1,s2)
    end.

  Lemma randomSplitAssumption :
    forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
  Proof.
    move => s1 s2. by exists (Node true s1 s2).
  Qed.
End InfiniteTrees.


(* Type class machinery for generating things in intervals *)

Class OrdType (A: Type) :=
  {
    leq     : A -> A -> bool;
    refl    : forall a, leq a a;
    trans   : forall  a b c, leq b a -> leq a c -> leq b c;
    antisym : forall a b, leq a b -> leq b a -> a = b
  }.

Program Instance OrdBool : OrdType bool :=
  {
    leq b1 b2 := implb b1 b2
  }.
Next Obligation.
  by destruct a.
Qed.
Next Obligation.
  by destruct a; destruct b; destruct c.
Qed.
Next Obligation.
  by destruct a; destruct b.
Qed.

Program Instance OrdNat : OrdType nat :=
  {
    leq := ssrnat.leq;
    trans := leq_trans
  }.
Next Obligation.
  apply/eqP. by rewrite eqn_leq; apply/andP; split.
Qed.

Program Instance OrdZ : OrdType Z :=
  {
    leq := Z.leb;
    refl := Z.leb_refl;
    antisym := Zle_bool_antisym;
    trans := fun a b => Zle_bool_trans b a
  }.


Class Random (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A * RandomSeed;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a /\ leq a a2 <->
                            exists seed, fst (randomR (a1, a2) seed) = a
  }.

Program Instance RandomBool : Random bool :=
  {
    randomR := randomRBool;
    randomRCorrect := randomRBoolCorrect
  }.

Instance RandomNat : Random nat :=
  {
    randomR := randomRNat;
    randomRCorrect := ramdomRNatCorrect
  }.


Instance RandomZ : Random Z :=
  {
    randomR := randomRInt;
    randomRCorrect := ramdomRIntCorrect
  }.
