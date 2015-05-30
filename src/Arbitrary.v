Require Import GenLow GenHigh Sets.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import List.
Require Import ssreflect ssrbool ssrnat.

Require Import ZArith ZArith.Znat Arith.
Import GenLow GenHigh.

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

Definition arbitraryList {A : Type} {Arb : Arbitrary A} :=
  listOf arbitrary.

Definition arbitraryPair {A B : Type} `{Arbitrary A} `{Arbitrary B} : G (A*B) :=
  liftGen2 pair arbitrary arbitrary.

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

Lemma abs_div2_pos : forall p, Z.abs_nat (Z.div2 (Z.pos p)) = Div2.div2 (Pos.to_nat p).
Proof.
  intros. destruct p.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; omega.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xO.
      rewrite mult_comm. rewrite Nat.div2_div. rewrite Nat.div_mul. reflexivity. omega.
  reflexivity.
Qed.

Lemma neg_succ : forall p,
  Z.neg (Pos.succ p) = Z.pred (Z.neg p).
Proof.
  move => p. rewrite <- Pos.add_1_r.
  rewrite <- Pos2Z.add_neg_neg.
  rewrite <- Z.sub_1_r.
  reflexivity.
Qed.

Lemma neg_pred : forall p, (p > 1)%positive ->
  Z.neg (Pos.pred p) = Z.succ (Z.neg p).
Proof.
  move => p Hp. destruct p using Pos.peano_ind. by inversion Hp.
  rewrite Pos.pred_succ. rewrite neg_succ. rewrite Z.succ_pred.
  reflexivity.
Qed.

Lemma abs_succ_neg : forall p,
  Z.abs_nat (Z.succ (Z.neg p)) = Nat.pred (Pos.to_nat p).
Proof.
  move => p. destruct p using Pos.peano_ind. reflexivity.
  rewrite -neg_pred /Z.abs_nat. rewrite Pos2Nat.inj_pred. reflexivity.
  apply Pos.lt_1_succ. apply Pos.lt_gt; apply Pos.lt_1_succ.
Qed.

Lemma abs_succ_div2_neg : forall p,
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Div2.div2 (Pos.to_nat p) \/
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Nat.pred (Div2.div2 (Pos.to_nat p)).
Proof.
  intros. destruct p.
    left. rewrite /Z.div2 /Pos.div2.
      rewrite neg_succ. rewrite <- Zsucc_pred. rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; omega.
    right. rewrite /Z.div2 /Pos.div2.
      rewrite Pos2Nat.inj_xO. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_mul. simpl.
      apply abs_succ_neg. omega.
  left. simpl. reflexivity.
Qed.

Function shrinkZ (x : Z) {measure (fun x => Z.abs_nat x) x}: list Z :=
  match x with
    | Z0 => nil
    | Zpos _ => rev (cons (Z.pred x) (cons (Z.div2 x) (shrinkZ (Z.div2 x))))
    | Zneg _ => rev (cons (Z.succ x) (cons (Z.succ (Z.div2 x)) (shrinkZ (Z.succ (Z.div2 x)))))
  end.
Proof.
  move => ? p ?. subst. rewrite abs_div2_pos. rewrite Zabs2Nat.inj_pos.
    rewrite Nat.div2_div. apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
  move => ? p ?. subst. destruct (abs_succ_div2_neg p) as [H | H].
    rewrite {}H /Z.abs_nat. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
    rewrite {}H /Z.abs_nat. eapply le_lt_trans. apply le_pred_n. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. omega.
Qed.

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

Instance arbPair {A B} `{Arbitrary A} `{Arbitrary B} : Arbitrary (A * B) :=
  {| 
    arbitrary := arbitraryPair;
    shrink p := List.combine (shrink (fst p)) (shrink (snd p))
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
  semGen arbitrary <--> [set: bool].
Proof.
by rewrite semChoose //; case.
Qed.

Lemma arbNat_correct:
  semGen arbitrary <--> [set: nat].
Proof.
rewrite /arbitrary /= /arbitraryNat /=.
rewrite semSized => n; split=> // _; exists n; split=> //.
by rewrite (semChooseSize _ _ _) /Random.leq /=.
Qed.

Lemma arbInt_correct s :
  semGenSize arbitrary s <-->
  [set z | (- Z.of_nat s <= z <= Z.of_nat s)%Z].
Proof.
rewrite semSizedSize semChooseSize.
  by move=> n; split=> [/andP|] [? ?]; [|apply/andP]; split; apply/Zle_is_le_bool.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Zle_0_nat.
exact/Zle_0_nat.
Qed.

Lemma arbBool_correctSize s :
  semGenSize arbitrary s <--> [set: bool].
Proof.
by rewrite semChooseSize //; case.
Qed.

Lemma arbNat_correctSize s :
  semGenSize arbitrary s <--> [set n : nat | (n <= s)%coq_nat].
Proof.
by rewrite semSizedSize semChooseSize // => n /=; case: leP.
Qed.

Lemma arbInt_correctSize : semGen arbitrary <--> [set: Z].
Proof.
rewrite semSized => n; split=> // _; exists (Z.abs_nat n); split=> //.
rewrite Nat2Z.inj_abs_nat (semChooseSize _ _ _).
  by case: n => //= p; rewrite !Z.leb_refl.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Z.abs_nonneg.
exact/Z.abs_nonneg.
Qed.

Lemma arbList_correct:
  forall {A} {H : Arbitrary A} (P : nat -> A -> Prop) s,
    (semGenSize arbitrary s <--> P s) ->
    (semGenSize arbitrary s <-->
     (fun (l : list A) => length l <= s /\ (forall x, List.In x l -> P s x))).
Proof.
  move => A H P s Hgen l. rewrite /arbitrary /arbList /arbitraryList.
  split.
  - move => /semListOfSize [Hl Hsize]. split => // x HIn. apply Hgen.
    auto.
  - move => [Hl HP]. apply semListOfSize. split => // x HIn.
    apply Hgen. auto.
Qed.

Lemma arbPair_correctSize 
      {A B} `{Arbitrary A} `{Arbitrary B} (Sa : nat -> set A) 
      (Sb : nat -> set B) s:
    (semGenSize arbitrary s <--> Sa s) -> 
    (semGenSize arbitrary s <--> Sb s) ->
    (semGenSize arbitrary s <--> setX (Sa s) (Sb s)).
Proof.
  move => H1 H2 . rewrite semLiftGen2Size; move => [a b].
  split. 
  by move => [[a' b'] [[/= /H1 Ha /H2 Hb] [Heq1 Heq2]]]; subst; split.
  move => [/H1 Ha /H2 Hb]. eexists; split; first by split; eauto.
  reflexivity.
Qed.
