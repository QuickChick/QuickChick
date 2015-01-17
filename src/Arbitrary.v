Require Import ModuleGen GenCombinators.
Require Import ZArith ZArith.Znat Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import List.
Require Import ssreflect ssrbool ssrnat.

Import Gen GenComb.
Class Arbitrary (A : Type) : Type :=
  {
    arbitrary : G A;
    shrink    : A -> list A
  }.

Definition arbitraryBool := choose (false, true).
Definition arbitraryNat :=
  sized (fun x => choose (0, x)).

Definition arbitraryZ :=
  sized (fun x =>
           let z := Z.of_nat x in
           choose (-z, z)%Z).

(* Definition arbitraryZ := choose (-100, 100)%Z. *)
Definition arbitraryList {A : Type} {Arb : Arbitrary A} :=
  listOf arbitrary.

Function shrinkBool (x : bool) :=
  match x with
    | false => nil
    | true  => cons false nil
  end.

Function shrinkNat (x : nat) {measure (fun x => x) x}: list nat :=
  match x with
    | O => nil
    | _ => cons (div x 2) (shrinkNat (div x 2))
  end.
Proof.
  intros; simpl; pose proof (divmod_spec n 1 0 0).
  assert (H01 : (0 <= 1)%coq_nat) by omega; apply H in H01; subst; clear H.
  destruct (divmod n 1 0 0); destruct n1; simpl; omega.
Qed.

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


Instance arbBool : Arbitrary bool :=
  {|
    arbitrary := @arbitraryBool;
    shrink  := shrinkBool
  |}.

Instance arbNat : Arbitrary nat :=
  {|
    arbitrary := @arbitraryNat;
    shrink := shrinkNat
  |}.

Instance arbList {A : Type} {Arb : Arbitrary A} : Arbitrary (list A) :=
  {|
    arbitrary:= arbitraryList;
    shrink := shrinkList shrink
  |}.

Instance arbInt : Arbitrary Z :=
  {|
    arbitrary := arbitraryZ;
    shrink := shrinkZ
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
  semGen arbitrary <--> (fun (_ : bool) => True).
Proof.
  rewrite /arbitrary /arbBool /arbitraryBool. move => b.
  split => // _. apply semChoose. 
  case: b; split => //. 
Qed.

Lemma arbNat_correct:
  semGen arbitrary <--> (fun (_ : nat) => True).
Proof.
  rewrite /arbitrary /arbNat /arbitraryNat. move => n.
  split => // _.
  apply semSized. exists n. apply semChooseSize.
  split=> //.
Qed.


Lemma arbInt_correct:
  forall s,
    semSize arbitrary s <--> 
    (fun (z : Z) =>  (- Z.of_nat s <= z <= Z.of_nat s)%Z).
Proof.
  rewrite /arbitrary /arbInt /arbitraryZ. move => n. split.
  - move/semSizedSize/semChooseSize => /= [H1 H2].
    split; by apply Zle_bool_imp_le.
  - move => [H1 H2].
    apply semSizedSize. apply semChooseSize.
    split; by apply Zle_imp_le_bool. 
Qed.


Lemma arbBool_correctSize:
  forall s,
    semSize arbitrary s <--> (fun (_ : bool) => True).
Proof.
  rewrite /arbitrary /arbBool /arbitraryBool. move => b.
  split => // _. apply semChooseSize. 
  case: b; case: a; split => //=. 
Qed.

Lemma arbNat_correctSize:
  forall s, 
    semSize arbitrary s <--> (fun (n : nat) => (n <= s)%coq_nat).
Proof.
  rewrite /arbitrary /arbNat /arbitraryNat. move => n.
  split.
  - by move/semSizedSize/semChooseSize => /= [H1 /leP H2]. 
  - move => /leP H.
    apply semSizedSize. apply semChooseSize.
    split; auto. 
Qed.

Lemma arbInt_correctSize:
  semGen arbitrary <--> (fun (_ : Z) => True).
Proof.
  rewrite /arbitrary /arbInt /arbitraryZ. move => n. split => // _.
  apply semSized.
  exists (Z.abs_nat n). apply semChooseSize.
  by split => //=; rewrite Nat2Z.inj_abs_nat; 
     case: n => //= p; apply Z.leb_refl.
Qed.


(* TODO : this need semListOf *)
Lemma arbList_correct:
  forall {A} {H : Arbitrary A},
    (semGen arbitrary <--> (fun (_ : A) => True)) ->
    (semGen arbitrary <--> (fun (_ : list A) => True)).
Proof.
  move => A H Hcorrect. rewrite /arbitrary /arbList /arbitraryList.
  move=> l. split => // _.
Abort.
  (* apply semListOfSize.  *)
