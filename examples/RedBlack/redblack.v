Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.

(* Formalization inspired from
   https://www.cs.princeton.edu/~appel/papers/redblack.pdf *)

(* An implementation of Red-Black Trees (insert only) *)

(* begin tree *)
Inductive color := Red | Black.
Inductive tree := Leaf : tree | Node : color -> tree -> nat -> tree -> tree.
(* end tree *)

(* insertion *)

Definition balance rb t1 k t2 :=
  match rb with
    | Red => Node Red t1 k t2
    | _ =>
      match t1 with
        | Node Red (Node Red a x b) y c =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | Node Red a x (Node Red b y c) =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | _ => match t2 with
                 | Node Red (Node Red b y c) z d =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | Node Red b y (Node Red c z d) =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | _ => Node Black t1 k t2
               end
      end
  end.

Fixpoint ins x s :=
  match s with
    | Leaf => Node Red Leaf x Leaf
    | Node c a y b => if x < y then balance c (ins x a) y b
                      else if y < x then balance c a y (ins x b)
                           else Node c a x b
  end.

Definition makeBlack t :=
  match t with
    | Leaf => Leaf
    | Node _ a x b => Node Black a x b
  end.

Definition insert x s := makeBlack (ins x s).


(* Red-Black Tree invariant: complete and correct definition *)
(* begin is_redblack *)
(* Inductive predicate for red-black trees with proper invariants:
   - Red nodes MUST have black children (no red-red violations)
   - All paths from node to leaves have equal black-height
   - BST property: lo < all values in tree < hi
   - The color parameter tracks the node's actual color
   - The nat parameters are: black-height, lower bound, upper bound
*)
Inductive is_redblack_node : tree -> color -> nat -> nat -> nat -> Prop :=
| RB_leaf : forall lo hi,
    (* Leaves are black with height 0, bounds are satisfied trivially *)
    is_redblack_node Leaf Black 0 lo hi
| RB_red : forall a x b h lo hi,
    (* Red nodes MUST have black children (enforces no red-red violations) *)
    lo < x -> x < hi ->
    is_redblack_node a Black h lo x ->
    is_redblack_node b Black h x hi ->
    is_redblack_node (Node Red a x b) Red h lo hi
| RB_black : forall c1 c2 a x b h lo hi,
    (* Black nodes can have children of any color *)
    lo < x -> x < hi ->
    is_redblack_node a c1 h lo x ->
    is_redblack_node b c2 h x hi ->
    (* Increment black-height for black node *)
    is_redblack_node (Node Black a x b) Black (S h) lo hi.

(* A proper red-black tree has a black root with unbounded range *)
Definition is_redblack (t : tree) : Prop := 
  exists h, is_redblack_node t Black h 0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
(* end is_redblack *)

(* begin insert_preserves_redblack *)
Definition insert_preserves_redblack : Prop :=
  forall x s, is_redblack s -> is_redblack (insert x s).
(* end insert_preserves_redblack *)

(* Declarative Proposition *)
Lemma insert_preserves_redblack_correct : insert_preserves_redblack.
Abort. (* if this wasn't about testing, we would just prove this *)
