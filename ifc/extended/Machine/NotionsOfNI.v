Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

Set Implicit Arguments.

Section Everything.

Variable A : eqType.
Variable low : pred A.
Variable initial : pred A.
Variable halted : pred A.
Variable step : A -> option A.
Variable equiv : rel A.

Hypothesis equivS : symmetric equiv.

Hypothesis halted_low : subpred halted low.

Hypothesis halted_equiv :
  forall s1 s2,
    equiv s1 s2 ->
    halted s1 = halted s2.

Definition high := [pred s | ~~ low s].

Definition stuck := [pred s | step s == None].

Hypothesis halted_stuck : subpred halted stuck.

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

Lemma trace_halted n s :
  halted s -> trace n s = [:: s].
Proof.
  move => H.
  case: n => [|n] /=; first by [].
  by move: H => /(@halted_stuck _)/eqP ->.
Qed.

Lemma exec_halted n s :
  halted s -> exec n s = s.
Proof.
  move => H.
  by rewrite (exec_trace s) (trace_halted _ H).
Qed.

Definition eeni : Prop :=
  forall (s1 s2 : A) (n : nat),
    initial s1 ->
    initial s2 ->
    equiv s1 s2 ->
    halted (exec n s1) ->
    halted (exec n s2) ->
    equiv (exec n s1) (exec n s2).

Inductive equivt : seq A -> seq A -> Prop :=
| EquivtNil : forall t, equivt [::] t
| EquivtConsLow : forall x1 x2 t1 t2,
                    equiv x1 x2 -> equivt t1 t2 ->
                    low x1 -> low x2 ->
                    equivt (x1 :: t1) (x2 :: t2)
| EquivtConsHigh : forall x1 t1 t2,
                     equivt t1 t2 ->
                     high x1 ->
                     equivt (x1 :: t1) t2
| EquivtSym : forall t1 t2,
                equivt t1 t2 ->
                equivt t2 t1.

Definition equivtb (t1 t2 : seq A) : bool :=
  all id (map (prod_curry equiv) (zip (filter low t1) (filter low t2))).

Lemma equivtbtN t : equivtb t [::].
Proof.
  case: t => [//=|x t] /=.
  rewrite /equivtb /=.
  case: (low x); first by [].
  by case: ([seq x <- t | low x]).
Qed.

Lemma equivtbNt t : equivtb [::] t.
  case: t => [//=|x t] /=.
  rewrite /equivtb /=.
  case: (low x); first by [].
  by case: ([seq x <- t | low x]).
Qed.

Lemma equivt_cons x1 x2 t1 t2 :
  equivt (x1 :: t1) (x2 :: t2) ->
  [\/ [/\ equiv x1 x2, low x1, low x2 & equivt t1 t2],
      [/\ equivt t1 (x2 :: t2) & high x1] |
      [/\ equivt (x1 :: t1) t2 & high x2] ].
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
    move: IH => /(_ _ _ H2 _ _ H1) [[IH1 IH2 IH3 /(@EquivtSym _) IH4]|[IH1 IH2]|[IH1 IH2]].
    + apply Or31.
      rewrite equivS in IH1.
      by constructor.
    + apply Or33. split; last by [].
      apply EquivtSym. congruence.
    + apply Or32. split; last by [].
      apply EquivtSym. congruence.
Qed.

Lemma equivt_consH x1 t1 t2 :
  high x1 ->
  equivt (x1 :: t1) t2 ->
  equivt t1 t2.
Proof.
  move => H1.
  move: {2}(size t1 + size t2) (leqnn (size t1 + size t2)) => n Hn.
  elim: n t1 t2 Hn => [|n IH] t1 t2 Hn E.
  - rewrite leqn0 addn_eq0 !size_eq0 in Hn.
    move: Hn => /andP [/eqP -> /eqP ->].
    by constructor.
  - case: t2 Hn E => [|x2 t2] Hn E.
    { apply EquivtSym. by constructor. }
    move: E => /(@equivt_cons _) [[_ E _ _]|[E _] //=|[E1 E2]].
    + by rewrite /high /= E in H1.
    + apply EquivtSym. apply EquivtConsHigh; last by [].
      apply EquivtSym. apply IH; last by [].
      by rewrite /= addnS ltnS in Hn.
Qed.

Lemma equivtP t1 t2 : reflect (equivt t1 t2) (equivtb t1 t2).
Proof.
  move: {2}(size t1 + size t2) (leqnn (size t1 + size t2)) => n Hn.
  elim: n t1 t2 Hn => [|n IH] t1 t2 Hn.
  - rewrite leqn0 addn_eq0 !size_eq0 in Hn.
    move: Hn => /andP [/eqP -> /eqP ->].
    by do 2! constructor.
  - case: t1 Hn => [|x1 t1] Hn.
    { rewrite equivtbNt.
      by do 2! constructor. }
    case: t2 Hn => [|x2 t2] Hn.
    { rewrite equivtbtN.
      constructor. apply EquivtSym. by constructor. }
    rewrite /equivtb /=.
    have [L1|L1] := (boolP (low x1)); have [L2|L2] := (boolP (low x2)) => /=.
    + rewrite /= addSn addnS ltnS ltn_neqAle in Hn.
      move: Hn => /andP [_ /(IH _) Hn] {IH}.
      apply/(iffP idP).
      * move/andP => [E1 /Hn E2]. by constructor.
      * move => /(@equivt_cons _) H.
        rewrite /high /= L1 L2 in H.
        case: H => //=.
        move => [-> _ _ H] /=.
        by apply/Hn.
    + by move => [_ ?].
    + by move => [_ ?].
    + rewrite [size (x2 :: t2)]/= addnS ltnS in Hn.
      move: Hn => /(IH _) {IH} /= IH.
      rewrite /equivtb /= L1 in IH.
      apply/(iffP IH) => H.
      * apply EquivtSym. apply EquivtConsHigh; try done.
        by apply EquivtSym.
      * apply EquivtSym.
        apply (@equivt_consH x2); first by [].
        by apply EquivtSym.
    + rewrite [size (x1 :: t1)]/= addSn ltnS in Hn.
      move: Hn => /(IH _) {IH} Hn.
      rewrite /equivtb /= L2 /= in Hn.
      apply (iffP Hn) => H.
      * by apply EquivtConsHigh.
      * by apply (@equivt_consH x1).
    + rewrite /= addSn addnS ltnS ltn_neqAle in Hn.
      move: Hn => /andP [_ /(IH _) Hn] {IH}.
      apply (iffP Hn) => H.
      * apply EquivtConsHigh; last by [].
        apply EquivtSym.
        apply EquivtConsHigh; last by [].
        by apply EquivtSym.
      * apply (@equivt_consH x1); first by [].
        apply EquivtSym.
        apply (@equivt_consH x2); first by [].
        by apply EquivtSym.
Qed.

Definition llni : Prop :=
  forall (s1 s2 : A) (n : nat),
    initial s1 ->
    initial s2 ->
    equiv s1 s2 ->
    equivtb (trace n s1) (trace n s2).

Record ssni : Prop := {

  ssni_low_low : forall s1 s2 s1' s2',
                   low s1 -> low s2 ->
                   equiv s1 s2 ->
                   step s1 = Some s1' ->
                   step s2 = Some s2' ->
                   equiv s1' s2';

  ssni_high_high : forall s s',
                     high s -> high s' ->
                     step s = Some s' ->
                     equiv s s';

  ssni_high_low : forall s1 s2 s1' s2',
                    high s1 -> high s2 ->
                    equiv s1 s2 ->
                    low s1' -> low s2' ->
                    step s1 = Some s1' ->
                    step s2 = Some s2' ->
                    equiv s1' s2'

  (* The fourth condition is now redundant given the assumption about
     equivalence and halted states, which seems to be needed for the
     LLNI -> EENI proof. *)

}.

Lemma llni_eeni : llni -> eeni.
Proof.
  move => LLNI s1 s2 n I1 I2 E12 H1 H2.
  move: LLNI => /(_ s1 s2 n I1 I2 E12)/equivtP LLNI {I1 I2}.
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
      rewrite (halted_equiv Ex) in H1.
      by move: (halted_stuck H1) S2 => /eqP ->.
    + move: Ht2 Ex Hx2 => [-> _] Ex Hx2.
      case S1: (step s1) s1' Ht1 H2 Hx1 H1 Ex => [s1'|] s1'' /= [-> Ht1] {s1''} H2 Hx1 H1 Ex; last by [].
      rewrite -(halted_equiv Ex) in H2.
      by move: (halted_stuck H2) S1 => /eqP ->.
    + case S1: (step s1) s1' Ht1 Ex Hx1 H1 => [s1'|] s1'' [-> ?] {s1''} Ex Hx1 H1;
      case S2: (step s2) s2' Ht2 Ex Hx2 H2 => [s2'|] s2'' [-> ?] {s2''} Ex Hx2 H2 //=.
      * by apply IH.
      * rewrite -(halted_equiv Ex) in H2.
        by move: (halted_stuck H2) S1 => /eqP ->.
      * rewrite (halted_equiv Ex) in H1.
        by move: (halted_stuck H1) S2 => /eqP ->.
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1.
    { move: Ht1 Hx1 => [-> _] Hx1.
      by rewrite /halted /= (halted_low H1) in Hx1. }
    case S1: (step s1) s1' Ht1 Hx1 H1 => [s1'|] s1'' [-> Ht1] {s1''} Hx1 H1; first by apply IH.
    by rewrite /halted /= (halted_low H1) in Hx1.
  - rewrite equivS. by apply IH.
Qed.

End Everything.
