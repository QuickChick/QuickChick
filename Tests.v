Require Import QuickCheck.

Require Import List.
Import ListNotations.
Require Import EqNat.

Fixpoint my_delete (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: my_delete x t
  end.

Definition prop_delete_removes_every_x (x : nat) (l : list nat) :=
  negb (existsb (fun y => beq_nat y x) (my_delete x l)).

Definition exMain := 
  quickCheck prop_delete_removes_every_x.