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

Lemma ge_le : forall n m, (n <= m)%coq_nat <-> (m >= n)%coq_nat.
Proof. split; auto. Qed.

(* TODO: Add to "Theorem" Library" *)
Lemma oneof_correct:  
  forall {A} (l : list (Pred A)) (def : Pred A), 
    peq (oneof def l) (fun e => (exists x, (In x l /\ x e)) \/ (l = [] /\ def e)).
Proof.   
  move=> A l def. 
  rewrite /peq /oneof. move => a. Opaque nat_compare.
  rewrite /choose /PredMonad /cmp /bindP //=. 
  split=> [[n [[/nat_compare_le/leP Hlo /nat_compare_ge/leP Hhi] H]] | 
           [[p [Hin pa]] | [Hnil Hdef]]].
  + case: l Hhi Hlo H => //= [|x xs] Hhi Hlo H.
    * by right; split; case : n H Hhi Hlo => //=.
    * case: n H Hhi Hlo => [| n] H Hhi Hlo.
      - by left; eexists; split ; [by left|].
      - left. exists (nth n xs def). split => //=.
        right. apply nth_In. 
        rewrite -[X in _ < X - 1]addn1 -[X in _ < _ - X]add0n subnDr subn0 in Hhi.
        by apply/leP.
  +  * apply In_split in  Hin. move: Hin => [l1 [l2 [Heq]]]. subst. 
       exists (length l1). 
       split. split. by apply/nat_compare_le/leP.
       apply/nat_compare_ge/leP.
       by rewrite app_length -addnBA leq_addr.  
       by rewrite app_nth2 //= NPeano.Nat.sub_diag. 
    * subst. exists 0. split. 
       split. by apply/nat_compare_le.
         by apply/nat_compare_ge.
         by [].
Qed.

Lemma gen_BinOpT_correct : 
  peq gen_BinOpT all.
Proof.
  rewrite /peq /gen_BinOpT /all. split => // _.
  apply oneof_correct. left. 
  case : A; [exists (pure BAdd) | exists (pure BMult)]; split => //=;
  [|right]; by left.
Qed.

Lemma elements_correct :
  forall {A} (l: list A) (def : A),
    peq (elements def l) (fun e => In e l \/ (l = [] /\ e = def)).
Proof.
  move => A l def.
  rewrite /peq /elements. move=> a. Opaque nat_compare.
  rewrite /choose /PredMonad /cmp /bindP /returnP //=. 
  split => [[n [[/nat_compare_le/leP Hlo /nat_compare_ge/leP Hhi] H]] | 
            [H | [H1 H2]]]; subst. 
  * case : l Hhi Hlo => //= [| x xs] Hhi Hlo.
    - rewrite sub0n leqn0 in Hhi. 
      move/eqP : Hhi => Hhi; subst. by right; split.
    - left. case: n Hhi Hlo => [| n] Hhi Hlo.
      by left.
      right; apply/nth_In/leP. 
      by rewrite -[X in _ < X - _]addn1 -{2}[1]add0n subnDr subn0 in Hhi.
  * apply in_split in H. move: H => [l1 [l2 Heq]]; subst.
    exists (length l1). split. split. 
    by apply/nat_compare_le/leP.
    apply/nat_compare_ge/leP.
    by rewrite app_length -addnBA leq_addr.  
    by rewrite app_nth2 //= NPeano.Nat.sub_diag. 
    * subst. exists 0. split. 
       split. by apply/nat_compare_le.
         by apply/nat_compare_ge.
         by [].
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

Lemma frequency_correct :
  forall {A} (l : list (nat * Pred A)) (def : Pred A), 
    peq (frequency' def l) 
        (fun e => (exists x, (In x l /\ (snd x) e /\ fst x <> 0)) \/ 
                  (l = [] /\ def e)).
Proof.
  move=> A l def a.  Opaque nat_compare.
  rewrite /frequency' /bindGen /PredMonad /bindP /choose /Randomnat /cmp //=. 
  split => [[n [[/nat_compare_le/leP Hlo /nat_compare_ge/leP Hhi] H]] | 
            [[[n p] [H1 [H2 H3]]]| [H1 H2]]]. 
  * elim : l n H Hlo Hhi=> [|[n' p] xs IHxs] //= n H Hlo Hhi. 
    + by right; split. 
    + remember (n <= n').
      case: b Heqb H => Heqb H; left. 
      - exists (n', p). split=> //=; [by left | split => //=].
        have /lt0n_neq0 : (0 < n') by admit. admit.  
      - have hyp1 : 0 <n - n' by admit.
        have hyp2 : n - n' <= seq.sumn (seq.map fst xs) by admit.
        move: (IHxs _ H hyp1 hyp2) => [[x [H1 [H2 H3]]] | [Heq Hdef]].  
        - apply In_split in H1. move: H1 => [l1 [l2 [Heq]]]; subst.

left. exists x. by split; [right | split]. 
        - subst. simpl in *. left. exists (n', p). split; [by left | split]. simpl.
     
          

      
      Search _ (0 < _) (_ != _).

left. move: (IHxs _ 

move :(@leq_trans _ _ n' Hhi). Search _ (_ <= _).
  

  move => a. Opaque nat_compare.
  split => [/oneof_correct [[x [HIn  H2]] | [Heq Hdef]] | 
            [[[n p] [H1 [H2 H3]]]| [H1 H2]]]. 
  apply In_split in HIn. move: HIn => [l1 [l2 Heq]]. 
move: H => 
  rewrite /choose /PredMonad /cmp /bindP //=. 
  split=> [[n [[/nat_compare_le/leP Hlo /nat_compare_ge/leP Hhi] H]] | 
           [[p [Hin pa]] | [Hnil Hdef]]].
  + case: l Hhi Hlo H => //= [|x xs] Hhi Hlo H.
    * by right; split; case : n H Hhi Hlo => //=.
    * case: n H Hhi Hlo => [| n] H Hhi Hlo.
      - by left; eexists; split ; [by left|].
      - left. exists (nth n xs def). split => //=.
        right. apply nth_In. 
        rewrite -[X in _ < X - 1]addn1 -[X in _ < _ - X]add0n subnDr subn0 in Hhi.
        by apply/leP.
  +  * apply In_split in  Hin. move: Hin => [l1 [l2 [Heq]]]. subst. 
       exists (length l1). 
       split. split. by apply/nat_compare_le/leP.
       apply/nat_compare_ge/leP.
       by rewrite app_length -addnBA leq_addr.  
       by rewrite app_nth2 //= NPeano.Nat.sub_diag. 
    * subst. exists 0. split. 
       split. by apply/nat_compare_le.
         by apply/nat_compare_ge.
         by [].
Qed.




