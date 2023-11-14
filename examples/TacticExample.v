Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
From Coq Require Import Nat.
From Coq Require Import Arith.Arith.
(*From Coq Require Import Bool.Bool.*)
(*Require Export Coq.Strings.String.*)
From Coq Require Import Logic.FunctionalExtensionality.
(*From Coq Require Import Lists.List.*)
(*Import ListNotations.*)
Set Default Goal Selector "!".

Definition to_be_generated :=
  forAll arbitrary (fun x =>
  forAll arbitrary (fun y =>                      
  if (x = y)? then checker ((x = 0)?)
  else checker tt)).


Inductive evenP : nat -> Prop :=
| even0 : evenP 0
| evenSS : forall n, evenP n -> evenP (S (S n)).

(*Create a DecOpt instance for even*)
#[global] 
Instance even_dec_opt (n :nat ) : DecOpt (evenP n) :=
  { decOpt := fun _ => Some (Nat.even n) }.


QuickChickDebug Debug On.
Theorem foo : forall (x y : nat) , x < 8.
Proof.
  quickchick.
Admitted.

Theorem add_0_r_firsttry : forall n:nat,
    n + 0 = n.
Proof.
  quickchick.
Abort.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  quickchick.
Abort.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  quickchick.
Abort.


Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  quickchick.  Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  quickchick.  Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  quickchick.  Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  quickchick.  Admitted.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)
Local Open Scope nat_scope.
Lemma double_plus : forall n, double n = n + n .
Proof.
  quickchick.  Admitted.

Fixpoint nateqb (n m : nat) :=
  match n,m with
  | 0, 0 => true
  | S n, S m => nateqb n m
  | _, _ => false
  end.

Theorem eqb_refl : forall n : nat,
  nateqb n n = true.
Proof. quickchick. Admitted.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof. quickchick. Admitted.

(* ################################################################# *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof. quickchick. Admitted.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof. quickchick. Admitted.
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof. quickchick. Admitted.
(* ################################################################# *)


Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. quickchick. Admitted.
Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. quickchick. Admitted.



(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(* ################################################################# *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. quickchick. Admitted.
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof. quickchick. Admitted.

Search (nat -> nat -> bool).
Theorem plus_leb_compat_l : forall (n m p : nat),
  (Nat.leb n m = true) -> (((p + n) <=? (p + m)) = true).
Proof. quickchick. Admitted.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof. quickchick. Admitted.
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof. quickchick. Admitted.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof. quickchick. Admitted.
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof. quickchick. Admitted.
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. quickchick. Admitted.
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof. quickchick. Admitted.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof. quickchick. Admitted.
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof. quickchick. Admitted.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. quickchick. Admitted.
(* ################################################################# *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Derive (Arbitrary, Show) for bin.

Fixpoint bineq (n m : bin) : bool :=
  match n, m with
  | Z, Z => true
  | B0 n, B0 m => bineq n m
  | B1 n, B1 m => bineq n m
  | _,_ => false
  end.

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => double (bin_to_nat m')
  | B1 m' => S (double (bin_to_nat m'))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof. quickchick. Admitted.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof. quickchick. Admitted.
(* ################################################################# *)



#[global] 
Instance bineq_dec_opt (b b' : bin ) : DecOpt (b = b') :=
  { decOpt := fun _ => Some (bineq b b') }.


Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Proof. quickchick. Abort.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof. quickchick. Admitted.
Definition double_bin (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => B0 (B0 b')
  | B1 b' => B0 (B1 b')
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. quickchick. Admitted.


Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof. quickchick. Admitted.


Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => match normalize b' with
             | Z => Z
             | b'' => B0 b''
             end
  | B1 b' => B1 (normalize b')
  end.
(* FILL IN HERE *)
Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof. quickchick. Admitted.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Derive (Arbitrary, Show) for natprod.
#[global] Instance Dec_eq_natprod (n n' : natprod) : Dec (n = n').
Proof. dec_eq. Defined.
Check (pair 3 5) : natprod.
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Notation "( x , y )" := (pair x y).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.
        
Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. quickchick. Admitted.
Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof. quickchick. Admitted.
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof. quickchick. Admitted.
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof. quickchick. Admitted.
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof. quickchick. Admitted.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Derive Show for natlist.
Derive Arbitrary for natlist.
#[global] Instance Dec_eq_natlist (l l' : natlist) : Dec (l = l').
Proof. dec_eq. Defined.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | S _ => h :: (nonzeros t)
              end
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match odd h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).


Fixpoint alternate (l1 l2 : natlist) : natlist := 
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.


#[global] Instance Deq_eq_bag (b b' : natlist) : Dec (b = b').
Proof. dec_eq. Defined.

Fixpoint count (v : nat) (s : natlist) : nat :=
  match s with
  | nil => O
  | h :: t => match eqb v h with
              | true => S (count v t)
              | false => count v t
              end
  end.

Definition sum : natlist -> natlist -> natlist := app.
Definition addL (v : nat) (s : natlist) : natlist := v :: s.
Fixpoint member (v : nat) (s : natlist) : bool :=
  match s with
  | nil => false
  | h :: t => match eqb v h with
              | true => true
              | false => member v t
              end
  end.

Fixpoint remove_one (v : nat) (s : natlist) : natlist :=
  match s with
  | nil => nil
  | h :: t => match eqb v h with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Fixpoint remove_all (v:nat) (s:natlist) : natlist :=
  match s with
  | nil => nil
  | h :: t => match eqb v h with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.

Fixpoint included (s1 : natlist) (s2 : natlist) : bool :=
  match s1 with
  | nil => true
  | h :: t => match member h s2 with
              | true => included t (remove_one h s2)
              | false => false
              end
  end.

Theorem add_inc_count : forall (b : natlist) (n : nat),
  count n (addL n b) = S (count n b).
Proof. quickchick. Admitted.

Definition manual_grade_for_add_inc_count : option (nat*string) := None.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. quickchick. Admitted.
Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof. quickchick. Admitted.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. quickchick. Admitted.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.
Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof. quickchick. Admitted.
Check length.
Check add.
Check (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun l1 =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun l2 =>
       QuickChick.Checker.checker
         match @QuickChick.Decidability.decOpt (@eq (@nat) (length (app l1 l2)) (add (length l1) (length l2))) _ 1000%nat with
         | Coq.Init.Datatypes.Some res => res
         | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
         end))).


Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = ((length l1) + (length l2)).
Proof. Print eq. quickchick. Admitted.
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof. quickchick. Admitted.


Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof. quickchick. Admitted.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. quickchick. Admitted.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof. quickchick. Admitted.
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof. quickchick. Admitted.
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof. quickchick. Admitted.
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1 :: t1, h2 :: t2 => match eqb h1 h2 with
                          | true => eqblist t1 t2
                          | false => false
                          end
  end.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof. quickchick. Admitted.

Theorem count_member_nonzero : forall (s : natlist),
  1 <=? (count 1 (1 :: s)) = true.
Proof. quickchick. Admitted.
Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof. quickchick. Admitted.
Theorem remove_does_not_increase_count: forall (s : natlist),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof. quickchick. Admitted.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof. quickchick. Admitted.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.
Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Derive Arbitrary for natoption.
Derive Show for natoption.
#[global] Instance Deq_eq_natoption (n n' : natoption) : Dec (n = n').
Proof. dec_eq. Defined.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.
Definition hd_error (l : natlist) : natoption :=
  match l with
  | x :: l' => Some x
  | _ => None
  end.
  

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof. quickchick. Admitted.
End NatList.

Inductive id : Type :=
  | Id (n : nat).
Derive (Show, Arbitrary) for id.
#[global] Instance Dec_eq_id (n n' : id) : Dec (n = n').
Proof. dec_eq. Defined.
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof. quickchick. Admitted.
Module PartialMap.
Export NatList.  
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
Derive Show for partial_map.
Derive Arbitrary for partial_map.
#[global] Instance Dec_eq_partial_map (m m' : partial_map) : Dec (m = m').
Proof. dec_eq. Defined.
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof. quickchick. Admitted.
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof. quickchick. Admitted.
End PartialMap.

 (* 2023-10-03 16:40 *)


  
 (*
Create a new file, lots of tests: trees, numbers, lists, etc.

Also do preservation in a separate file STLC. 

ADD THIS FILE TO QUICKCHICK TEST SUITE
add the test file to the makefile.

Push to master

Create baseline.

Create a new tactic that prints info about evarmaps environ, relcontext



*)
