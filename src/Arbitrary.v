Require Import Gen.
Require Import ZArith.
Require Import ZArith.Znat.
Require Import Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import List.

Class Arbitrary (A : Type) : Type :=
{
  arbitrary : Gen A;
  shrink    : A -> list A
}.

Instance arbBool : Arbitrary bool :=
{|
  arbitrary := chooseBool (false, true);
  shrink x  :=
  match x with
      | false => nil
      | true  => cons false nil
  end
|}.

Function shrinkNat (x : nat) {measure (fun x => x) x}: list nat :=
  match x with
    | O => nil
    | _ => cons (div x 2) (shrinkNat (div x 2))
  end.
intros; simpl; pose proof (divmod_spec n 1 0 0).
assert (H01 : 0 <= 1) by omega; apply H in H01; subst; clear H.
destruct (divmod n 1 0 0); destruct n1; simpl; omega.
Qed.

Instance arbNat : Arbitrary nat :=
{|
  arbitrary := chooseNat (0, 100);
  shrink x := shrinkNat x
|}.

Function shrinkZ (x : Z) {measure (fun x => Z.abs_nat x) x}: list Z :=
  match x with
    | Z0 => nil
    | Zpos _ => rev (cons (Z.pred x) (cons (Z.div x 2) (shrinkZ (Z.div x 2))))
    | Zneg _ => rev (cons (Z.succ x) (cons (Z.div x 2) (shrinkZ (Z.div x 2))))
  end.
Admitted.


Fixpoint shrinkList {A : Type} (shr : A -> list A) (l : list A) : list (list A) :=
  match l with
      | nil => nil
      | cons x xs => 
        cons xs (map (fun xs' => cons x xs') (shrinkList shr xs))
             ++ (map (fun x'  => cons x' xs) (shr x ))
    end.

Instance arbList {A : Type} `{Arb : Arbitrary A}
: Arbitrary (list A) :=
{|
  arbitrary := listOf (arbitrary);
  shrink l  := shrinkList shrink l
|}.

Local Open Scope Z_scope.
Instance arbInt : Arbitrary Z :=
{|
  arbitrary := chooseZ (-100, 100);
  shrink x := shrinkZ x
|}.

(* For these instances to be useful, we would need to support dependent types *)

(*
Instance arbSet : Arbitrary Set :=
{|
  arbitrary := returnGen nat;
  shrink x := nil
|}.

Instance arbType : Arbitrary Type :=
{|
  arbitrary := returnGen (nat : Type);
  shrink x := nil
|}.
*)