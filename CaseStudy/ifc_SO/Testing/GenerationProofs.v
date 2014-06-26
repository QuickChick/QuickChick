Require Import QuickChick SetOfOutcomes.

Require Import Common Machine Generation.

Require Import List.
Require Import ZArith.

Require Import ssreflect ssrbool ssrnat eqtype.


Lemma gen_from_length_correct: forall l,
  peq (gen_from_length l) (fun z => (Z.le 0 z /\ Z.le z (l-1))).
Proof.
  move => l. Opaque Z.compare. 
  rewrite /peq /gen_from_length /choose /PredMonad /cmp /=. 
  split => [[/Z.compare_le_iff H1 /Z.compare_ge_iff H2]|
            [/Z.compare_le_iff H1 /Z.compare_ge_iff H2]];
    by split; auto.
Qed.


Lemma gen_from_nat_length_correct: forall l,
  peq (gen_from_nat_length l) (fun z => (Z.le 0 z /\ Z.le z ((Z.of_nat l)-1))).
Proof.
  move => l.
  rewrite /gen_from_nat_length.
  move/(_ (Z.of_nat l)): gen_from_length_correct; apply. 
Qed.

Lemma gen_BinOpT_correct : 
  peq gen_BinOpT all.
Proof.
  rewrite /peq /gen_BinOpT /all. split => // _.
  apply oneof_correct. left. 
  case : A; [exists (pure BAdd) | exists (pure BMult)]; split => //=;
  [|right]; by left.
Qed.


Lemma powerset_nonempty : 
  forall {A} (l : list A), powerset l <> nil.
Proof.
  move => A. elim => //= x xs IHxs.
  case: (powerset xs) IHxs => //=. 
Qed.

Lemma gen_label_correct : 
  forall (l : Label),
    peq (gen_label l) (fun e => In e (allThingsBelow l)).
Proof.
  move=> l. rewrite /peq /gen_label. move => l'.   
  split => [/elements_correct [H1 | [H1 H2]] //= | HIn]; subst.  
  + rewrite /allThingsBelow  /allBelow in H1. apply map_eq_nil in H1.
    by move/powerset_nonempty : H1.
  + apply elements_correct. by left.
Qed.

Lemma gen_label_inf_correct : forall inf,
  peq (gen_label_inf inf) (fun e => In e (allThingsBelow (top_prin inf))).
Proof.
  move => inf. apply/gen_label_correct.
Qed.
