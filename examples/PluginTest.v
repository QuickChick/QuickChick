From QuickChick Require Import QuickChick.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive Arbitrary for Tree.

Inductive goodTree : nat -> Tree -> Prop :=
| GoodLeaf : forall n, goodTree n Leaf 
| GoodNode : forall m l r, goodTree m l -> goodTree m (Node m l r).

                                             (* m > n -> goodTree m l -> goodTree m r -> goodTree n (Node m l r). *)

Instance test_coercion A B (P : A -> B -> Prop) `{Gen B}
         {_ : forall y, GenSuchThat _ (fun x => P x y)} :
  GenSuchThat _ (fun p : A * B => let (x,y) := p in P x y) :=
  {| arbitraryST :=
      bindGen arbitrary (fun y =>
      bindGenOpt (@arbitraryST _ (fun x : A => P x y) _) (fun x => 
      returnGen (Some (x,y)))) |}.

Definition foo : G (option (nat * nat)) :=
  @arbitraryST _ (fun p : nat * nat => let (x,y) := p in x = y) _.

QuickChickDebug Debug On.
Derive ArbitrarySizedSuchThat for (fun p => let (m,tr) := p in goodTree m tr).




