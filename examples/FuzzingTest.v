From QuickChick Require Import QuickChick.
Require Import List ZArith. Import ListNotations.

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

Definition removeP (xl : nat * list nat) : option bool := 
  Some (negb (existsb (fun y => beq_nat y (fst xl)) (remove (fst xl) (snd xl)))).

Definition fuzzer := (fun _ : unit => fuzzLoop arbitrary fuzz show removeP).
FuzzQC removeP (fuzzer tt). 

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive Arbitrary for Tree.
Derive Fuzzy for Tree.

Inductive Tree' A :=
| Leaf' : Tree' A
| Node' : A -> Tree' A -> Tree' A -> Tree' A.

Derive Arbitrary for Tree'.
Derive Fuzzy for Tree'.