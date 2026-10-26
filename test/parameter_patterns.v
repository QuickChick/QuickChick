From QuickChick Require Import QuickChick.
Require Import List String. Import ListNotations.

(* Derived Show and Shrink match on constructors. A type's parameters must
   be written in those patterns unless they are implicit, so the patterns
   give every parameter as [_] after [@]. *)

Inductive tree (A : Type) := Leaf : A -> tree A | Node : tree A -> tree A.

QuickChick Derive (Show, Shrink) for tree.

Example show_tree : show (Node nat (Leaf nat 3)) = "Node (Leaf 3)"%string.
Proof. reflexivity. Qed.

Example shrink_tree :
  shrink (Node nat (Leaf nat 3))
  = [Leaf nat 3; Node nat (Leaf nat 1); Node nat (Leaf nat 0)].
Proof. reflexivity. Qed.

Inductive itree (A : Type) := ILeaf : A -> itree A | INode : itree A -> itree A.
Arguments ILeaf {A}. Arguments INode {A}.

QuickChick Derive (Show, Shrink) for itree.

Example show_itree : show (INode (ILeaf 3)) = "INode (ILeaf 3)"%string.
Proof. reflexivity. Qed.

Inductive left_side (A : Type) := LBase : A -> left_side A | LStep : right_side A -> left_side A
with right_side (A : Type) := RStep : left_side A -> right_side A.

QuickChick Derive Show for left_side.

Example show_mutual :
  show (RStep _ (LStep _ (RStep _ (LBase _ 7)))) = "RStep (LStep (RStep (LBase 7)))"%string.
Proof. reflexivity. Qed.

(* Parameters implicit in one constructor and explicit in another, and an
   implicit argument that is not a parameter. *)
Inductive mix (A B : Type) := MA : A -> mix A B | MB : B -> mix A B -> mix A B.
Arguments MA {A} B _. Arguments MB A {B} _ _.

QuickChick Derive (Show, Shrink) for mix.

Example show_mix : show (MB nat true (MA bool 3)) = "MB true (MA 3)"%string.
Proof. reflexivity. Qed.

Inductive hidden (A : Type) := Hide : forall {n : nat}, A -> hidden A | Wrap : hidden A -> hidden A.

QuickChick Derive (Show, Shrink) for hidden.

Example show_hidden : show (Wrap nat (Hide nat (n := 4) 5)) = "Wrap (Hide 4 5)"%string.
Proof. reflexivity. Qed.
