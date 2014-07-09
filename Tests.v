Require Import QuickChick.

Require Import List.
Import ListNotations.
Require Import EqNat.
Require Import NPeano.

(* Small example with default arbitrary instances *)

Fixpoint my_delete (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: my_delete x t
  end.

Definition prop_delete_removes_every_x (x : nat) (l : list nat) :=
  negb (existsb (fun y => beq_nat y x) (my_delete x l)).

Definition test0 := 
  showResult (quickCheck prop_delete_removes_every_x).

QuickCheck test0.

(* Tree example showing custom datatypes *)

Inductive Tree (A : Type) :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Instance arbTree {A : Type} `{_ : Arbitrary A}
: Arbitrary (Tree A) :=
{|
  arbitrary := 
    let fix genTree (n : nat) : Gen (Tree A):= 
        match n with
          | O => returnGen (Leaf A)
          | S n' => 
            frequency (returnGen (Leaf A)) 
                      [(1, returnGen (Leaf A));
                       (n, liftGen3 (Node A) arbitrary (genTree n') (genTree n'))]
        end
    in sized genTree;
  shrink t := 
      let fix shrinkTree (t : Tree A) := 
          match t with 
            | Leaf => []
            | Node x l r => 
              map (fun x' => Node A x' l r) (shrink x) ++ 
              map (fun l' => Node A x l' r) (shrinkTree l) ++
              map (fun r' => Node A x l r') (shrinkTree r)
          end
      in shrinkTree t
|}.

Require Import String.
Open Scope string.
Instance showTree {A : Type} `{_ : Show A} : Show (Tree A) :=
{| 
  show t := 
    let fix showTree (t : Tree A) :=
        match t with
          | Leaf => "Leaf"
          | Node x l r => "Node " ++ show x 
                                  ++ " ( " ++ showTree l ++ " ) " 
                                  ++ " ( " ++ showTree r ++ " ) "
        end
    in showTree t
|}.

Open Scope list.
(* Faulty mirror function *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf A
    | Node x l r => Node A x r l
  end.

Fixpoint tree_to_list {A : Type} (t : Tree A) : list A :=
  match t with
    | Leaf => []
    | Node x l r => [x] ++ tree_to_list l ++ tree_to_list r
  end.

Definition prop_mirror_reverse (t : Tree nat) :=
  if list_eq_dec Nat.eq_dec (tree_to_list t) (rev (tree_to_list (mirror t)))
  then true 
  else false.

Definition testTree :=
  showResult (quickCheck prop_mirror_reverse).

QuickCheck testTree.

Definition prop_length_false (A : Type) (l : list A) :=
  beq_nat (List.length l) 0.

Definition testTree :=
  showResult (quickCheck prop_length_false).