From QuickChick Require Import QuickChick.

(* An unconstrained generator for a type whose constructors all take a
   recursive argument has nothing to produce when its fuel runs out. The
   derivation reports the type instead of failing to elaborate. [Fail]
   does not catch anomalies. *)

Inductive endless := More : endless -> endless.

Fail QuickChick Derive GenSized for endless.

(* A mutual member with no base constructor still has values when a
   partner has one. At fuel zero it builds on the partner's base case. *)
Inductive no_base_left (A : Type) :=
| NLeaf : A -> no_base_left A
| NLeft : no_base_right A -> no_base_left A
with no_base_right (A : Type) :=
| NRight : no_base_left A -> no_base_right A.

Arguments NLeaf {A}. Arguments NLeft {A}. Arguments NRight {A}.

QuickChick Derive GenSized for no_base_left.

Fixpoint depth_left {A} (x : no_base_left A) : nat :=
  match x with NLeaf _ => 0 | NLeft r => S (depth_right r) end
with depth_right {A} (x : no_base_right A) : nat :=
  match x with NRight l => S (depth_left l) end.

Sample (fmap depth_right (@arbitrarySized (no_base_right nat) _ 0)).

(* A chain in which only the last member has a base constructor. *)
Inductive chain_a := ChainA : chain_b -> chain_a
with chain_b := ChainB : chain_c -> chain_b
with chain_c := ChainBase : nat -> chain_c | ChainBack : chain_a -> chain_c.

QuickChick Derive GenSized for chain_a.

Fixpoint depth_a (x : chain_a) : nat := match x with ChainA b => S (depth_b b) end
with depth_b (x : chain_b) : nat := match x with ChainB c => S (depth_c c) end
with depth_c (x : chain_c) : nat :=
  match x with ChainBase _ => 0 | ChainBack a => S (depth_a a) end.

Sample (fmap depth_a (@arbitrarySized chain_a _ 3)).
