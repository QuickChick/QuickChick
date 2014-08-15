Require Import String.
Require Import Arith.EqNat.
Require Import ZArith.

Require Import Machine.

Require Import QuickChick EndToEnd SetOfOutcomes.

Require Import Common.
Require Import Printing.
Require Import Shrinking.
Require Import Generation.
Require Import Indist.
Require Import SSNI.

Require Import ssreflect ssrbool eqtype.

Require Import Show.

(* Possible steps according to SSNI_helper*)

(*

L ->  s1'
|     |    final states indistinguishable
L ->  s2'




L ->  s1'
|
L ->  x    no step for the second state



H -> L
|    |     final states indistinguishable
H -> L




H -> L
|        no condition here. Seems a bit strange.
H -> H



H -> H   high to high step. Requires no trace and the states before and
         after to be indistinguishable

*)


Definition propSSNI_prop (t : table) (v : Variation) : Prop :=
  let '(Var lab st1 st2) := v in
  (indist lab st1 st2) ->
  (is_low_state st1 lab /\ (forall tr1 st1' tr2 st2',
                          exec t st1 = Some (tr1, st1') ->
                          exec t st2 = Some (tr2, st2') ->
                          observe_comp (observe lab tr1) (observe lab tr2) /\
                          (indist lab st1' st2'))) \/
  (~~ is_low_state st1 lab /\ (forall tr1 st1',
                             exec t st1 = Some (tr1, st1') ->
                             ((is_low_state st1' lab /\
                               forall tr2 st2',
                                 exec t st2 = Some (tr2, st2') ->
                                 is_low_state st2' lab ->
                                 observe_comp (observe lab tr1) (observe lab tr2) /\
                                 (indist lab st1' st2')) \/
                              (~~ is_low_state st1' lab /\
                               List.length (observe lab tr1) = 0%nat /\
                               indist lab st1 st1')))).

Definition propSSNI_bool (t : table) (v : Variation) : bool :=
    let '(Var lab st1 st2) := v in
    if indist lab st1 st2 then
      match exec t st1  with
        | Some (tr1, st1') =>
          if is_low_state st1 lab then
            match exec t st2 with
              | Some (tr2, st2') =>
                (observe_comp (observe lab tr1) (observe lab tr2)
                              && (indist lab st1' st2'))
              | _ => true
            end
          else (* is_high st1 *)
            if is_low_state st1' lab then
              match exec t st2 with
                | Some (tr2, st2') =>
                  if is_low_state st2' lab then
                    observe_comp (observe lab tr1) (observe lab tr2)
                                 && (indist lab st1' st2')
                  else true
                | _ => true
              end
            else
              beq_nat (List.length (observe lab tr1)) 0
                      && indist lab st1 st1'
        | _ => true
      end
    else true.

Lemma ssniP:
  forall (t : table) v,
    reflect (propSSNI_prop t v) (propSSNI_bool t v).
Proof.
  move=> t [lab st1 st2]. apply/(@iffP (propSSNI_bool t (Var lab st1 st2))); try (by apply idP);
  rewrite /propSSNI_bool /propSSNI_prop.
  { destruct (indist lab st1 st2) => //.
    destruct (exec t st1) as [ [tr1' st1'] |].
    - destruct (is_low_state st1 lab).
      + destruct (exec t st2) as [ [tr2' st2'] |];
        move => H _; left; split => //.
        move=> tr1_ st1'_ st2_ st2'_ [eq1 eq2] [eq3 eq4]; subst.
        by apply/andP.
      + move => H _. right. split => //.
        move=> tr1_ st1'_ [eq1 eq2]; subst.
        destruct (exec t st2) as [[tr2' st2'] |].
        * destruct (is_low_state st1'_ lab).
          left. split => //. move => tr2_ st2'_ [eq1 eq2] H'; subst.
          destruct (is_low_state st2'_ lab); try congruence.
          by apply/andP.
          right. split=> //. move : H => /andP [H1 H2]. split => //.
          by apply beq_nat_eq.
        * destruct (is_low_state st1'_ lab). left. by split => //.
          right. split => //. move : H => /andP [H1 H2]. split => //.
          by apply beq_nat_eq.
    - move=> _ _. destruct (is_low_state st1 lab).
      + left. split => //.
      + right. split => //. }
  { destruct (indist lab st1 st2) => //. move => /(_ is_true_true) H.
    move: H => [[H1 H2] | [H1 H2]].
    - rewrite H1. destruct (exec t st1) as [ [tr1' st1'] |] => //.
      destruct (exec t st2) as [ [tr2' st2'] |] => //.
      apply/andP. by auto.
    - apply Bool.negb_true_iff  in H1. rewrite H1.
      destruct (exec t st1) as [ [tr1' st1'] |] => //.
      move : H2 => /(_ _ _ Logic.eq_refl) [[H2 H3] | [H2 [H3 H4]]].
      + rewrite H2. destruct (exec t st2) as [ [tr2' st2'] |] => //.
        move: H3 => /(_ _ _ Logic.eq_refl) H3.
        destruct (is_low_state st2' lab) => //. apply/andP; by auto.
      + apply Bool.negb_true_iff in H2. rewrite H2.
        apply/andP. split => //. by apply beq_nat_true_iff in H3. }
Qed.

Lemma propSSNI_helper_equiv:
  forall (t : table) v,
    semProperty (@propSSNI_helper Pred _ t v) <-> propSSNI_prop t v.
Proof.
  move=> t [lab st1 st2]. split; [move => H; apply/ssniP| move=> /ssniP H];
  rewrite /propSSNI_helper /propSSNI_bool /semTestable semCollect_idemp in H *.
  - move=> /semPredQProp H. destruct (indist lab st1 st2) => //.
    { destruct (exec t st1) as [ [tr1' st1'] |] => //.
      destruct (is_low_state st1 lab).
      - destruct (exec t st2) as [ [tr2' st2'] |] => //.
          by move/semCollect_idemp(*/semPredQProp
                 /semWhenFail_idemp*)/semBool : H => H.
      - destruct (is_low_state st1').
        + destruct (exec t st2) as [[tr2 st2'] |] => //.
          destruct (is_low_state st2' lab).
            by move/semCollect_idemp(*/semPredQProp/semWhenFail_idemp*)/semBool : H.
            by move/semCollect_idemp/semPredQProp/semBool : H.
        + by move/semCollect_idemp(*/semPredQProp/semWhenFail_idemp*)/semBool : H. }
  -  move=> H.
     destruct (indist lab st1 st2);
       try by apply/semPredQProp/semCollect_idemp/semPredQProp/semBool.
    { destruct (exec t st1) as [ [tr1' st1'] |].
      destruct (is_low_state st1 lab).
      - destruct (exec t st2) as [ [tr2' st2'] |].
        by apply/semPredQProp/semCollect_idemp(*/semPredQProp/semWhenFail_idemp*)/semBool.
        by apply/semPredQProp/semCollect_idemp/semPredQProp/semBool.
      - destruct (is_low_state st1').
        + destruct (exec t st2) as [[tr2 st2'] |].
          * destruct (is_low_state st2' lab).
            by apply/semPredQProp/semCollect_idemp(*/semPredQProp/semWhenFail_idemp*)/semBool.
            by apply/semPredQProp/semCollect_idemp/semPredQProp/semBool.
          * by apply/semPredQProp/semCollect_idemp/semPredQProp/semBool.
        + by apply/semPredQProp/semCollect_idemp(*/semPredQProp/semWhenFail_idemp*)/semBool.
      - by apply/semPredQProp/semCollect_idemp/semPredQProp/semBool. }
Qed.
