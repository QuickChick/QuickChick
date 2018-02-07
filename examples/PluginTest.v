From QuickChick Require Import QuickChick.

QuickChickDebug Debug On.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive Arbitrary for Tree.

Inductive recursion_test : nat -> Tree -> Prop :=
| RecLeaf : forall n, recursion_test n Leaf 
| RecNode : forall m l r, recursion_test m l -> recursion_test m (Node m l r).

Derive ArbitrarySizedSuchThat for (fun p => let (m,tr) := p in recursion_test m tr).

Inductive checker_test : nat -> Tree -> Prop :=
| CheckerLeaf : forall n, checker_test n Leaf
| CheckerNode : forall n t, checker_test O Leaf -> checker_test n t.

Instance dec_opt l t : DecOpt (checker_test l t).
Admitted.

Derive ArbitrarySizedSuchThat for (fun p => let (m,tr) := p in checker_test m tr).

Set Printing All.
Derive DecOpt for (checker_test n t).
Print DecOptchecker_test.

(* Non recursive test *)
Derive ArbitrarySizedSuchThat for (fun tr => recursion_test m tr).


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
