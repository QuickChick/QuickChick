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

CoFixpoint mkSeedTree (s : RandomSeed) := 
  let (s1, s2) := randomSplit s in
  RstNode s (mkSeedTree s1) (mkSeedTree s2).

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

Inductive PrefixFree : list SplitPath -> Prop :=
| FreeSingle : forall (p : SplitPath), PrefixFree [p]
| FreeCons : forall (p : SplitPath) (l : list SplitPath), 
               PrefixFree l ->
               forall (p' p'': SplitPath), In p' l -> (p' ++ p'' = p -> False) -> 
                                           PrefixFree (p :: l).

Theorem topLevelSeedTheorem : (* Need a better name :P *)
  forall (l : list SplitPath) (f : SplitPath -> RandomSeed),
    PrefixFree l -> exists (s : RandomSeed), 
                      forall p, In p l -> varySeed p s = f p.
Admitted.
(*
Inductive SeedTree := 
| SeedTreeUndef : SeedTree
| SeedTreeLeaf : RandomSeed -> SeedTree
| SeedTreeNode : SeedTree -> SeedTree -> SeedTree.

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
