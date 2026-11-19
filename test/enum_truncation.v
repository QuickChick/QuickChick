From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* A size bound cuts an enumeration of an infinite type short, so a checker
   that finds no witness in it answers None, not Some false. Here checking a
   node enumerates its operands' labels through Lit's enumerator; a label too
   long for the size has no split within it, though Node holds. *)
Inductive Lit : nat -> list bool -> Prop := any n l : Lit n l.
Inductive Node : nat -> nat -> list bool -> Prop :=
| bop a b l1 l2 : Lit a l1 -> Lit b l2 -> Node a b (l1 ++ l2).
QuickChick Derive Checker for (Node a b l).

Definition long := [true; false; true; true; false; false; true;
                    true; false; true; true; false; false; true].

Example long_node : Node 1 2 long.
Proof. apply (bop 1 2 (firstn 7 long) (skipn 7 long)); constructor. Qed.

Example node_checks :
  (decOpt (P := Node 1 2 [true; false]) 5, decOpt (P := Node 1 2 long) 5,
   decOpt (P := Node 1 2 long) 9) = (Some true, None, Some true).
Proof. vm_compute. reflexivity. Qed.

(* An enumeration of a finite type, such as bool, is complete, so exhausting
   it still refutes. *)
Inductive B : nat -> Prop := mkB n (b : bool) : b = true -> n = 0 -> B n.
QuickChick Derive Checker for (B n).

Example finite_checks : (decOpt (P := B 0) 5, decOpt (P := B 1) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.
