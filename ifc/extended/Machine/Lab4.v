Require Import Labels.
Require Import List. Import ListNotations.

(** The four point finite lattice (diamond shape) *)
Inductive Lab4 : Set :=
  | L  : Lab4
  | M1 : Lab4
  | M2 : Lab4
  | H  : Lab4.

Instance JoinSemiLattice_Lab4 : JoinSemiLattice Lab4 :=
{  bot := L
;  join l1 l2 :=
     match l1, l2 with
       | _ , H  => H
       | H , _  => H
       | L , _  => l2
       | _ , L  => l1
       | M1, M2 => H
       | M2, M1 => H
       | _ , _  => l1 (* l1 == l2 *)
     end
; flows l1 l2 :=
    match l1, l2 with
      | L , L  => true
      | L , M1 => true
      | L , M2 => true
      | L , H  => true
      | M1, M1 => true
      | M1, H  => true
      | M2, M2 => true
      | M2, H  => true
      | H , H  => true
      | _ , _  => false
    end
}.
Proof.
now auto.
now intros l; destruct l; auto.
now intros l; destruct l; auto.
now intros l1 l2 l3; destruct l1, l2, l3; auto.
now intros l1 l2; destruct l1, l2; auto.
now intros l1 l2; destruct l1, l2; auto.
now intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.

Instance Lattice_Lab4 : Lattice Lab4 := { top := H }.
Proof. intros l; destruct l; auto. Defined.

Instance FiniteLattice_Lab4 : FiniteLattice Lab4 := { elems := [L;M1;M2;H] }.
Proof. intros l; destruct l; simpl; tauto. Defined.
