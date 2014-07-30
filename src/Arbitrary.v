Require Import AbstractGen.
Require Import ZArith ZArith.Znat Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import List.
Require Import SetOfOutcomes.
Require Import ssreflect. 

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


Instance arbBool : Arbitrary bool :=
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

Instance arbNat : Arbitrary nat :=
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

Instance arbList {A : Type} {Arb : Arbitrary A} : Arbitrary (list A) :=
  {|
    arbitrary := 
      fun gen hgen => @arbitraryList gen hgen A Arb;
    shrink l  := shrinkList shrink l
  |}.

Instance arbInt : Arbitrary Z :=
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

(* Correctness proof about built-in generators *)

Lemma arbBool_correct:
  arbitrary <--> (fun (_ : bool) => True).
Proof.
  rewrite /arbitrary /arbBool /arbitraryBool. move => b.
  split => // _. rewrite choose_def.
  simpl. case: b; split; move => contra; discriminate. 
Qed.

Lemma arbNat_correct:
  arbitrary <--> (fun (_ : nat) => True).
Proof.
  rewrite /arbitrary /arbNat /arbitraryNat. move => n.
  split => // _. 
  rewrite sized_def. exists n. rewrite choose_def.
  split; [apply nat_compare_le | apply nat_compare_ge]; simpl; omega.
Qed.

Lemma arbInt_correct: 
  arbitrary <--> (fun (_ : Z) => True).
Proof.
  rewrite /arbitrary /arbInt /arbitraryZ.  
  rewrite sized_def. move => z. split => //= _. 
  exists (Z.abs_nat z).
  split. 
  - apply/Z.compare_le_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
  - apply/Z.compare_ge_iff. rewrite Nat2Z.inj_abs_nat. 
    by case: z => //= p; omega. 
Qed.

Lemma arbList_correct:
  forall {A} {H : Arbitrary A},
    (arbitrary <--> (fun (_ : A) => True)) ->
    (arbitrary <--> (fun (_ : list A) => True)).
Proof.
  move => A H Hcorrect. rewrite /arbitrary /arbList /arbitraryList.
  move=> l. split => // _. 
  apply listOf_equiv. move => x _. by apply Hcorrect.
Qed.


