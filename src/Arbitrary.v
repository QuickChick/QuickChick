Require Import AbstractGen.
Require Import ZArith.
Require Import ZArith.Znat.
Require Import Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import List.


Class Arbitrary (A : Type) : Type :=
{
  arbitrary : forall {Gen : Type -> Type} {H : GenMonad Gen}, Gen A;
  shrink    : A -> list A
}.


Section ArbitrarySection.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}.

  Definition arbitraryBool := choose (false, true).
  Definition arbitraryNat :=  
    sized (fun x => choose (0, x)).
  (* Why we  are not using sized to generate Nats like QC?
      Definition arbitraryNat :=  choose (0, 100). *)
  Definition arbitraryZ := 
    sized (fun x => 
             let z := Z.of_nat x in 
             choose (-z, z)%Z).
  (* Definition arbitraryZ := choose (-100, 100)%Z. *)
  Definition arbitraryList {A : Type} {Arb : Arbitrary A} := 
    listOf arbitrary.
End ArbitrarySection.

 
Global Instance arbBool : Arbitrary bool :=
{|
  arbitrary := @arbitraryBool;
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

Global Instance arbNat : Arbitrary nat :=
{|
  arbitrary := @arbitraryNat;
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

Global Instance arbList {A : Type} {Arb : Arbitrary A}
: Arbitrary (list A) :=
{|
  arbitrary := 
    fun gen hgen => @arbitraryList gen hgen A Arb;
  shrink l  := shrinkList shrink l
|}.

Local Open Scope Z_scope.
Global Instance arbInt : Arbitrary Z :=
{|
  arbitrary := @arbitraryZ;
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