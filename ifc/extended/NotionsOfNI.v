Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

Set Implicit Arguments.

Section Everything.

Variable A : Type.
Variable low : pred A.
Variable start : pred A.
Variable ended : pred A.
Variable step : A -> option A.
Variable indist : rel A.

Hypothesis indistT : transitive indist.

Hypothesis indistS : symmetric indist.

Hypothesis ended_low : subpred ended low.

Hypothesis ended_indist :
  forall s1 s2,
    indist s1 s2 ->
    ended s1 = ended s2.

Hypothesis indist_low :
  forall s1 s2,
    indist s1 s2 ->
    low s1 = low s2.

Definition high := [pred s | ~~ low s].

Definition stuck := [pred s | ~~ step s].

Hypothesis ended_stuck : subpred ended stuck.

Fixpoint exec (n : nat) (s : A) : A :=
  match n, step s with
  | S n', Some s' => exec n' s'
  | _, _ => s
  end.

Fixpoint trace (n : nat) (s : A) : seq A :=
  match n, step s with
  | S n', Some s' => s :: trace n' s'
  | _, _ => [:: s]
  end.

Lemma exec_trace s' n s : exec n s = last s' (trace n s).
Proof.
  elim: n s s' => [|n IH] s s' //=.
  case E: (step s) => [s''|//=].
  rewrite (IH _ s) {IH} /=.
  case: n => [|n] //=.
Qed.

Lemma trace_ended n s :
  ended s -> trace n s = [:: s].
Proof.
move => H; case: n => [|n] //=.
move/ended_stuck: H.
by rewrite /stuck /=; case: (step s).
Qed.

Lemma exec_ended n s :
  ended s -> exec n s = s.
Proof.
  move => H.
  by rewrite (exec_trace s) (trace_ended _ H).
Qed.

Definition eeni : Prop :=
  forall (s1 s2 : A) (n : nat),
    start s1 ->
    start s2 ->
    indist s1 s2 ->
    ended (exec n s1) ->
    ended (exec n s2) ->
    indist (exec n s1) (exec n s2).

Inductive indistt : seq A -> seq A -> Prop :=
| IndisttNil : forall t, indistt [::] t
| IndisttConsLow : forall x1 x2 t1 t2,
                    indist x1 x2 -> indistt t1 t2 ->
                    low x1 -> low x2 ->
                    indistt (x1 :: t1) (x2 :: t2)
| IndisttConsHigh : forall x1 t1 t2,
                     indistt t1 t2 ->
                     high x1 ->
                     indistt (x1 :: t1) t2
| IndisttSym : forall t1 t2,
                indistt t1 t2 ->
                indistt t2 t1.

Definition indisttb (t1 t2 : seq A) : bool :=
  all id (map (prod_curry indist) (zip (filter low t1) (filter low t2))).

Lemma indisttbtN t : indisttb t [::].
Proof.
  case: t => [//=|x t] /=.
  rewrite /indisttb /=.
  case: (low x); first by [].
  by case: ([seq x <- t | low x]).
Qed.

Lemma indisttbNt t : indisttb [::] t.
  case: t => [//=|x t] /=.
  rewrite /indisttb /=.
  case: (low x); first by [].
  by case: ([seq x <- t | low x]).
Qed.

Lemma indistt_cons x1 x2 t1 t2 :
  indistt (x1 :: t1) (x2 :: t2) ->
  [\/ [/\ indist x1 x2, low x1, low x2 & indistt t1 t2],
      [/\ indistt t1 (x2 :: t2) & high x1] |
      [/\ indistt (x1 :: t1) t2 & high x2] ].
Proof.
  move: {1 3}(x1 :: t1) (erefl (x1 :: t1))
        {1 3}(x2 :: t2) (erefl (x2 :: t2))
        => t1' Ht1' t2' Ht2' H.
  elim: H x1 t1 Ht1' x2 t2 Ht2'
        => {t1' t2'} //= [x1 x2 t1 t2 Ex Et IH L1 L2|x1 t1 t2 Et IH H1|t2 t1 Et IH].
  - move => ? ? [<- <-] ? ? [<- <-].
    apply Or31. by constructor.
  - move => ? ? [<- <-] ? ? ?.
    apply Or32.
    split; last by [].
    congruence.
  - move => x1 t1' H1 x2 t2' H2.
    move: IH => /(_ _ _ H2 _ _ H1) [[IH1 IH2 IH3 /(@IndisttSym _) IH4]|[IH1 IH2]|[IH1 IH2]].
    + apply Or31.
      rewrite indistS in IH1.
      by constructor.
    + apply Or33. split; last by [].
      apply IndisttSym. congruence.
    + apply Or32. split; last by [].
      apply IndisttSym. congruence.
Qed.

Lemma indistt_consH x1 t1 t2 :
  high x1 ->
  indistt (x1 :: t1) t2 ->
  indistt t1 t2.
Proof.
  move => H1.
  move: {2}(size t1 + size t2) (leqnn (size t1 + size t2)) => n Hn.
  elim: n t1 t2 Hn => [t1 t2|n IH t1].
  - by rewrite leqn0 addn_eq0; case: t1; case:t2 => //; constructor.
  - case=> [|x2 t2] Hn E.
    { apply IndisttSym. by constructor. }
    move: E => /(@indistt_cons _) [[_ E _ _]|[E _] //=|[E1 E2]].
    + by rewrite /high /= E in H1.
    + apply IndisttSym. apply IndisttConsHigh; last by [].
      apply IndisttSym. apply IH; last by [].
      by rewrite /= addnS ltnS in Hn.
Qed.

Lemma indisttb_single s1 s2 : indist s1 s2 -> indisttb [:: s1] [:: s2].
Proof.
  move => H.
  rewrite /indisttb /= (indist_low H).
  case: (low s2) => //=.
  by rewrite andbT.
Qed.

Lemma indisttb_cons2 s1 t1 s2 t2 : indist s1 s2 -> indisttb (s1 :: t1) (s2 :: t2) = indisttb t1 t2.
Proof.
  move => H.
  rewrite /indisttb /= (indist_low H).
  case: (low s2) => //=.
  by rewrite H.
Qed.

Lemma indisttP t1 t2 : reflect (indistt t1 t2) (indisttb t1 t2).
Proof.
  move: {2}(size t1 + size t2) (leqnn (size t1 + size t2)) => n Hn.
  elim: n t1 t2 Hn => [|n IH] t1 t2.
  - by rewrite leqn0 addn_eq0; case: t1; case: t2 => //; do 2! constructor.
  - case: t1 => [|x1 t1].
    { rewrite indisttbNt.
      by do 2! constructor. }
    case: t2 => [|x2 t2] Hn.
    { rewrite indisttbtN.
      constructor. apply IndisttSym. by constructor. }
    rewrite /indisttb /=.
    have [L1|L1] := (boolP (low x1)); have [L2|L2] := (boolP (low x2)) => /=.
    + rewrite /= addSn addnS ltnS ltn_neqAle in Hn.
      move: Hn => /andP [_ /(IH _) Hn] {IH}.
      apply/(iffP idP).
      * move/andP => [E1 /Hn E2]. by constructor.
      * move => /(@indistt_cons _) H.
        rewrite /high /= L1 L2 in H.
        case: H => //=.
        move => [-> _ _ H] /=.
        by apply/Hn.
    + by move => [_ ?].
    + by move => [_ ?].
    + rewrite [size (x2 :: t2)]/= addnS ltnS in Hn.
      move: Hn => /(IH _) {IH} /= IH.
      rewrite /indisttb /= L1 in IH.
      apply/(iffP IH) => H.
      * apply IndisttSym. apply IndisttConsHigh; try done.
        by apply IndisttSym.
      * apply IndisttSym.
        apply (@indistt_consH x2); first by [].
        by apply IndisttSym.
    + rewrite [size (x1 :: t1)]/= addSn ltnS in Hn.
      move: Hn => /(IH _) {IH} Hn.
      rewrite /indisttb /= L2 /= in Hn.
      apply (iffP Hn) => H.
      * by apply IndisttConsHigh.
      * by apply (@indistt_consH x1).
    + rewrite /= addSn addnS ltnS ltn_neqAle in Hn.
      move: Hn => /andP [_ /(IH _) Hn] {IH}.
      apply (iffP Hn) => H.
      * apply IndisttConsHigh; last by [].
        apply IndisttSym.
        apply IndisttConsHigh; last by [].
        by apply IndisttSym.
      * apply (@indistt_consH x1); first by [].
        apply IndisttSym.
        apply (@indistt_consH x2); first by [].
        by apply IndisttSym.
Qed.

(* CH: It's nasty to expose a quantification over n in the property;
       there are much better ways to do this (equivalent but less proof-oriented);
       see how we define things in the paper *)
Definition llni : Prop :=
  forall (s1 s2 : A) (n : nat),
    start s1 ->
    start s2 ->
    indist s1 s2 ->
    indisttb (trace n s1) (trace n s2).

Record ssni : Prop := {

  ssni_low_low : forall s1 s2 s1' s2',
                   low s1 ->
                   indist s1 s2 ->
                   step s1 = Some s1' ->
                   step s2 = Some s2' ->
                   indist s1' s2';

  ssni_high_high : forall s s',
                     high s -> high s' ->
                     step s = Some s' ->
                     indist s s';

  ssni_high_low : forall s1 s2 s1' s2',
                    high s1 ->
                    indist s1 s2 ->
                    low s1' -> low s2' ->
                    step s1 = Some s1' ->
                    step s2 = Some s2' ->
                    indist s1' s2'

  (* The fourth condition is now redundant given the assumption about
     indistalence and ended states, which seems to be needed for the
     LLNI -> EENI proof. *)

}.

Lemma llni_eeni : llni -> eeni.
Proof.
  move => LLNI s1 s2 n I1 I2 E12 H1 H2.
  move: LLNI => /(_ s1 s2 n I1 I2 E12)/indisttP LLNI {I1 I2}.
  move: {1 3}(trace n s1) {1 3}(trace n s2) (erefl (trace n s1)) (erefl (trace n s2)) LLNI
        => t1 t2 Ht1 Ht2 LLNI {E12}.
  elim: LLNI n {2 4 6}(n) s1 s2 H1 H2 Ht1 Ht2
        => [t|s1' s2' t1' t2' Ex Et IH Hx1 Hx2|s1' t1' t2' Et IH Hx1|t1' t2' Et IH] n1 n2 s1 s2 H1 H2 Ht1 Ht2.
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1.
    by case: (step s1) H1 Ht1 => [s1'|].
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1;
    case: n2 H2 Ht2 => [|n2] //= H2 Ht2.
    + by move: Ht1 Ht2 Ex => [-> ?] [-> ?].
    + move: Ht1 Ex Hx1 => [-> _] Ex Hx1.
      case S2: (step s2) s2' Ht2 H1 Hx2 H2 Ex => [s2'|] s2'' /= [-> Ht2] {s2''} H1 Hx2 H2 Ex; last by [].
      rewrite (ended_indist Ex) in H1.
      by have := ended_stuck H1; rewrite /stuck /= S2.
    + move: Ht2 Ex Hx2 => [-> _] Ex Hx2.
      case S1: (step s1) s1' Ht1 H2 Hx1 H1 Ex => [s1'|] s1'' /= [-> Ht1] {s1''} H2 Hx1 H1 Ex; last by [].
      rewrite -(ended_indist Ex) in H2.
      by have := ended_stuck H2; rewrite /stuck /= S1.
    + case S1: (step s1) s1' Ht1 Ex Hx1 H1 => [s1'|] s1'' [-> ?] {s1''} Ex Hx1 H1;
      case S2: (step s2) s2' Ht2 Ex Hx2 H2 => [s2'|] s2'' [-> ?] {s2''} Ex Hx2 H2 //=.
      * by apply IH.
      * rewrite -(ended_indist Ex) in H2.
        by have := ended_stuck H2; rewrite /stuck /= S1.
      * rewrite (ended_indist Ex) in H1.
        by have := ended_stuck H1; rewrite /stuck /= S2.
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1.
    { move: Ht1 Hx1 => [-> _] Hx1.
      by rewrite /ended /= (ended_low H1) in Hx1. }
    case S1: (step s1) s1' Ht1 Hx1 H1 => [s1'|] s1'' [-> Ht1] {s1''} Hx1 H1; first by apply IH.
    by rewrite /ended /= (ended_low H1) in Hx1.
  - by rewrite indistS; apply: IH.
Qed.

(* CH: TODO: allow the two indistinguishability relations to vary *)
Lemma ssni_llni : ssni -> llni.
Proof.
  move => SSNI s1 s2 n I1 I2 E12.
  move: n {2 4}(n) {2}(n + n) (leqnn (n + n)) => n1 n2 n Hn.
  elim: n s1 s2 {I1 I2} E12 n1 n2 Hn => [|n IH] s1 s2 E12 n1 n2 Hn.
  - rewrite leqn0 addn_eq0 in Hn.
    move: Hn => /andP [/eqP -> /eqP ->] /=.
    exact: indisttb_single E12.
  - case: n1 Hn => [|n1] /= Hn;
    case: n2 Hn => [|n2] /= Hn.
    + exact: indisttb_single E12.
    + by case S2: (step s2) => [s2'|] /=; rewrite (indisttb_cons2 _ _ E12) indisttbNt.
    + by case S1: (step s1) => [s1'|] /=; rewrite (indisttb_cons2 _ _ E12) indisttbtN.
    + case S1: (step s1) => [s1'|]; case S2: (step s2) => [s2'|];
      try by rewrite (indisttb_cons2 _ _ E12) ?indisttbNt ?indisttbtN.
      rewrite /indisttb /= -(indist_low E12).
      have [L|L] := boolP (low s1) => /=.
      * rewrite E12 /=.
        apply IH; first by eapply (ssni_low_low SSNI); eauto.
        rewrite addnS addSn ltnS ltn_neqAle in Hn.
        by move: Hn => /andP [? ?].
      * have [L1'|L1'] := boolP (low s1'); first have [L2'|L2'] := boolP (low s2').
        - rewrite addnS addSn ltnS ltn_neqAle in Hn.
          move: Hn => /andP [_ ?].
          apply IH; last by [].
          eapply ssni_high_low; eauto.
          exact: L.
        - rewrite addnS ltnS in Hn.
          have E12': indist s1 s2'.
          { apply: (indistT E12).
            eapply ssni_high_high; eauto.
            by rewrite /high /= -(indist_low E12). }
          move: IH => /(_ s1 s2' E12' _ _ Hn).
          by rewrite /indisttb /= S1 /= (negbTE L).
        - rewrite addSn ltnS in Hn.
          have E12': indist s1' s2.
          { apply: (indistT _ E12).
            rewrite indistS.
            eapply ssni_high_high; eauto. }
          move: IH => /(_ s1' s2 E12' _ _ Hn).
          rewrite (indist_low E12) in L.
          by rewrite /indisttb /= S2 /= (negbTE L).
Qed.

End Everything.
