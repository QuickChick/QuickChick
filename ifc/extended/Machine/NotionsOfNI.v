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

End Everything.

(*

Lemma llni_eeni : llni -> eeni.
Proof.
  move => LLNI s1 s2 n I1 I2 E12 H1 H2.
  move: LLNI => /(_ s1 s2 n I1 I2 E12)/equivtP LLNI {I1 I2}.
  move: {1 3}(trace n s1) {1 3}(trace n s2) (erefl (trace n s1)) (erefl (trace n s2)) LLNI
        => t1 t2 Ht1 Ht2 LLNI {E12}.
  elim: LLNI n {2 4 6}(n) s1 s2 H1 H2 Ht1 Ht2
        => [t|s1' s2' t1' t2' Ex Et IH Hx1 Hx2| | ] n1 n2 s1 s2 H1 H2 Ht1 Ht2.
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1.
    by case: (step s1) H1 Ht1 => [s1'|].
  - case: n1 H1 Ht1 => [|n1] //= H1 Ht1.
    + move: Ht1 => [E1 E2].
      rewrite E1 in Ex.
      rewrite (halted_equiv Ex) in H1.
      case: n2 H2 Ht2 => [|n2] /= H2 Ht2.
      * by move: Ht2 => [<- _].


rewrite /exec /trace



  move: n {2 4 6 8}(n) {2}(n + n) (leqnn (n + n)) H1 H2 LLNI => n1 n2 n Hn H1 H2 LLNI.
  elim: n n1 n2 s1 s2 {E12} Hn H1 H2 LLNI
        => [|n IH] n1 n2 s1 s2 Hn H1 H2 LLNI.
  - rewrite !leqn0 addn_eq0 in Hn.
    move: Hn H1 H2 LLNI => /andP [/eqP -> /eqP ->] /= H1 H2 LLNI.
    by rewrite (halted_low H1) (halted_low H2) /= andbT in LLNI.
  - case: n1 Hn H1 LLNI => [|n1] /= Hn H1 LLNI;
    case: n2 Hn H2 LLNI => [|n2] /= Hn H2 LLNI.
    + by rewrite (halted_low H1) (halted_low H2) /= andbT in LLNI.
    + case S2: (step s2) H2 LLNI => [s2'|] /= H2 LLNI; last first.
      { by rewrite (halted_low H1) (halted_low H2) /= andbT in LLNI. }
      case: (low s2) LLNI => LLNI.
      { rewrite (halted_low H1) /= andbT in LLNI.
        rewrite (halted_equiv LLNI) in H1.
        by move: (halted_stuck H1) S2 => /eqP ->. }
      rewrite ltnS in Hn.
      by move: IH => /(_ 0 n2 s1 s2' Hn H1 H2 LLNI) /= IH.
    + case S1: (step s1) H1 LLNI => [s1'|] /= H1 LLNI; last first.
      { by rewrite (halted_low H1) (halted_low H2) /= andbT in LLNI. }
      case: (low s1) LLNI => LLNI.
      { rewrite (halted_low H2) /= in LLNI.
        move: LLNI => /andP [LLNI _].
        rewrite -(halted_equiv LLNI) in H2.
        by move: (halted_stuck H2) S1 => /eqP ->. }
      rewrite addn0 ltnS -(addn0 n1) in Hn.
      by move: IH => /(_ n1 0 s1' s2 Hn H1 H2 LLNI) /= IH.
    + case S1: (step s1) H1 LLNI => [s1'|] /= H1 LLNI;
      case S2: (step s2) H2 LLNI => [s2'|] /= H2 LLNI.
      * case: (low s1) LLNI => LLNI; case: (low s2) LLNI => /= LLNI.
        - move: LLNI => /andP [_ LLNI].
          rewrite addnS addSn ltnS ltn_neqAle in Hn.




      rewrite /= in L1.


      {

  - rewrite (halted_low H1) in LLNI.
    case S2: (step s2) H2 LLNI => [s2'|] /= H2 LLNI; last first.
    { by rewrite (halted_low H2) /= andbT in LLNI. }
    case: (low s2) LLNI => LLNI.
    {

rewrite (halted_equiv E12) in H1.
    by move: H1 => /halted_stuck/eqP ->.
  - rewrite -(halted_equiv E12) in H2.
    by move: H2 => /halted_stuck/eqP ->.
  - case S1: (step s1) H1 LLNI => [s1'|] //= H1 LLNI; last first.
    { rewrite (halted_equiv E12) in H1.
      by move: H1 => /halted_stuck/eqP ->. }
    case S2: (step s2) H2 LLNI => [s2'|] /= H2 LLNI; last first.
    { rewrite -(halted_equiv E12) in H2.
      move: H2 => /halted_stuck/eqP H2.
      congruence. }
    + rewrite

case: (low s1) LLNI => //= LLNI.
      *


  move: {1 2 3}(trace n s1) {1 2 3}(trace n s2) H1 H2 LLNI => t1 t2 H1 H2 LLNI.
  elim: t1 t2 s1 s2 E12 H1 H2 LLNI
        => [|s1' t1 IH] [|s2' t2] //= s1 s2 E12 H1 H2 LLNI.


  elim: t1 t2




Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.

Set Implicit Arguments.

(** This file defines several notions of NI
   - start-to-end NI (SENI), for finite executions only
   - semantic NI (SNI), for potentially infinite traces
   - lock-step NI (LSNI), for potentially infinite traces

   This file also establish, under some hypotheses, logical links
   between these notions:
   - LSNI implies SENI
   - LSNI implies SNI
   LSNI is a stronger property that we can prove by (co)induction,
   and it implies both the final properties SENI and SNI that
   we would like to provide to the end-user.
*)

(** * Lots of parameters *)
Section Everything.

(** Parameters needed by both start-to-end and lockstep
    non-interference *)

Variable A : Type.
Variable sys_trace : trace A -> Prop.

Variable Observer: Type.

Variable equiv : Observer -> relation A.

(* Low denotes the level of the attacker, ie
   - information at his level
   - everything below
*)
Variable Low : Observer -> A -> Prop.

Variable Succ : A -> Prop.

(** Additional parameters needed by start-to-end and semantic
    non-interference *)

Variable weak_equiv : Observer -> relation A.
Hypothesis H_weak : forall o s1 s2, equiv o s1 s2 -> weak_equiv o s1 s2.
Hypothesis H_weak_equiv : (forall o, equivalence _ (weak_equiv o)).

Hypothesis weak_equiv_dec : forall o s1 s2,
  {weak_equiv o s1 s2} + {~weak_equiv o s1 s2}.

(** * Start-to-end non-interference *)

(** Start-to-end non-interference talks only about
    terminating executions. We can't prove this directly, but this is
    one of the two properties we want in the end *)

(** Start-to-end non-interference doesn't consider any of the
    intermediate states, but only the initial and the final
    states. One thing to note is that we did need to distinguish
    between successfully terminating executions and erroneously
    terminating ones. *)

(** Another thing to note is that we can only guarantee anything if
    the final states are high. If one of the traces ends in a high
    state than basically all bets are off, the other trace can
    continue any way it likes, and even terminate in a completely
    unrelated state. *)

(** The only reason to still define ends_with as a relation, as
    opposed to a function, is that the function would be partial *)
Inductive ends_with : list A -> A -> Prop :=
| ends_sing : forall a, ends_with (cons a nil) a
| ends_dcons : forall a1 a2 t a,
                 ends_with (cons a2 t) a ->
                 ends_with (cons a1 (cons a2 t)) a.
Hint Constructors ends_with.

Definition start_to_end_ni : Prop :=
  forall o s1 s2 l1 l2 s1' s2',
    equiv o s1 s2 ->
    sys_trace (list_to_trace (s1 :: l1)) ->
    sys_trace (list_to_trace (s2 :: l2)) ->
    ends_with (s1 :: l1) s1' ->
    ends_with (s2 :: l2) s2' ->
    Low o s1' ->
    Succ s1' ->
    Low o s2' ->
    Succ s2' ->
    weak_equiv o s1' s2'.

(* DD: I'd like to clean out the noise in start-to-end with something like


Definition end_to_end_ni : Prop :=
  forall o s1 s2 l1 l2 s1' s2',
    equiv o s1 s2 ->
    sys_trace_ends s1 s1' ->
    sys_trace_ends s2 s2' ->
    Low o s1' ->
    Succ s1' ->
    Low o s2' ->
    Succ s2' ->
    weak_equiv o s1' s2'.
*)

(** * Semantic non-interference *)

(** Semantic non-interference talks about observable events in both
    finite and infinite executions. It models an attacker that observes
    these outputs/events as they occur. *)

(* CH: For finite executions we always ignore the longer trace. We
   could be more precise, like in lockstep non-interference below,
   but that would be more complicated so I didn't (yet) do it *)
(* XXX: With this change then there is a big chance that semantic
   non-interference will imply start-to-end non-interference; which is
   currently not the case. Not sure how important that is though. *)

(* CH: we defined indistinguishable as a relation instead of a cofix
   because removing stuttering states is not a valid operation on lazy
   lists (filter is not guarded). Moreover, (co)inductive definitions
   give us much better inversion principles that help a lot in
   proofs. *)

CoInductive semantic_indist (o: Observer) : relation (trace A) :=
  | si_stutter1 : forall a1 a1' t1 t2,
      weak_equiv o a1 a1' ->
      semantic_indist o (TCons a1' t1) t2 ->
      semantic_indist o (TCons a1 (TCons a1' t1)) t2
  | si_stutter2 : forall t1 a2 a2' t2,
      weak_equiv o a2 a2' ->
      semantic_indist o t1 (TCons a2' t2) ->
      semantic_indist o t1 (TCons a2 (TCons a2' t2))
  | si_step : forall a1 a1' t1 a2 a2' t2,
      weak_equiv o a1 a2 ->
      ~(weak_equiv o a1 a1') ->
      ~(weak_equiv o a2 a2') ->
      semantic_indist o (TCons a1' t1) (TCons a2' t2) ->
      semantic_indist o (TCons a1 (TCons a1' t1)) (TCons a2 (TCons a2' t2))
  | si_step_end1 : forall a1 a2 t2,
      weak_equiv o a1 a2 ->
      semantic_indist o (TCons a1 TNil) (TCons a2 t2)
  | si_step_end2 : forall a1 t1 a2,
      weak_equiv o a1 a2 ->
      semantic_indist o (TCons a1 t1) (TCons a2 TNil).

Definition semantic_ni : Prop := forall o s1 s2 t1 t2,
  equiv o s1 s2 ->
  sys_trace (TCons s1 t1) ->
  sys_trace (TCons s2 t2) ->
  semantic_indist o (TCons s1 t1) (TCons s2 t2).

(** * lockstep non-interference *)

(** This stronger property is supposed to imply both start-to-end
    non-interference and semantic non-interference *)

CoInductive lockstep_indist (O: Observer) : relation (trace A) :=
| li_lockstep_end : lockstep_indist O TNil TNil
| li_low_lockstep : forall s1 s2 t1 t2,
    Low O s1 ->
    equiv O s1 s2 ->
    lockstep_indist O t1 t2 ->
    lockstep_indist O (TCons s1 t1) (TCons s2 t2)
| li_high_end1 : forall s1 s2 t2,
    ~(Low O s1 /\ Succ s1) ->
    equiv O s1 s2 ->
    lockstep_indist O (TCons s1 TNil) (TCons s2 t2)
| li_high_end2 : forall s1 s2 t1,
    ~(Low O s2 /\ Succ s2) ->
    equiv O s1 s2 ->
    lockstep_indist O (TCons s1 t1) (TCons s2 TNil)
| li_high_high1 : forall s1 s1' s2 t1 t2,
    ~Low O s1  ->
    ~Low O s1' ->
    equiv O s1 s2 ->
    equiv O s1 s1' ->
    lockstep_indist O (TCons s1' t1) (TCons s2 t2) ->
    lockstep_indist O (TCons s1 (TCons s1' t1)) (TCons s2 t2)
| li_high_high2 : forall s1 s2 s2' t1 t2,
    ~Low O s2 ->
    ~Low O s2' ->
    equiv O s1 s2 ->
    equiv O s2 s2' ->
    lockstep_indist O (TCons s1 t1) (TCons s2' t2) ->
    lockstep_indist O (TCons s1 t1) (TCons s2 (TCons s2' t2))
| li_high_low_lockstep : forall s1 s1' s2 s2' t1 t2,
    ~Low O s1  ->
    ~Low O s2  ->
    Low O s1'  ->
    Low O s2'  ->
    equiv O s1 s2 ->
    lockstep_indist O (TCons s1' t1) (TCons s2' t2) ->
    lockstep_indist O (TCons s1 (TCons s1' t1))
                    (TCons s2 (TCons s2' t2)).

(* CH: got rid of the symmetry case by duplicating things -- this does
   help in the proofs (e.g. lockstep_indist_lockstep_indist_ind_gen
   and helper_lockstep_ind_ni_implies_start_to_end_ni below) *)

Definition lockstep_ni : Prop := forall o s1 s2 t1 t2,
  equiv o s1 s2 ->
  sys_trace (TCons s1 t1) ->
  sys_trace (TCons s2 t2) ->
  lockstep_indist o (TCons s1 t1) (TCons s2 t2).


(** * Proof that lockstep non-interference implies
      start-to-end non-interference *)

(** Since this proof is only about finite traces we define a weaker
    inductive variant of lockstep non-interference, but which is
    still strong enough to imply start-to-end non-interference *)

Inductive lockstep_indist_ind (O: Observer) : relation (list A) :=
| lii_lockstep_end : lockstep_indist_ind O nil nil
| lii_low_lockstep : forall s1 s2 t1 t2,
    Low O s1 ->
    equiv O s1 s2 ->
    lockstep_indist_ind O t1 t2 ->
    lockstep_indist_ind O (s1 :: t1) (s2 :: t2)
| lii_high_end1 : forall s1 s2 t2,
    ~(Low O s1 /\ Succ s1) ->
    equiv O s1 s2 ->
    lockstep_indist_ind O (s1 :: nil) (s2 :: t2)
| lii_high_end2 : forall s1 t1 s2,
    ~(Low O s2 /\ Succ s2) ->
    equiv O s1 s2 ->
    lockstep_indist_ind O (s1 :: t1) (s2 :: nil)
| lii_high_high1 : forall s1 s1' s2 t1 t2,
    ~Low O s1 ->
    ~Low O s1' ->
    equiv O s1 s2 ->
    equiv O s1 s1' ->
    lockstep_indist_ind O (s1' :: t1) (s2 :: t2) ->
    lockstep_indist_ind O (s1 :: s1' :: t1) (s2 :: t2)
| lii_high_high2 : forall s1 s2 s2' t1 t2,
    ~Low O s2 ->
    ~Low O s2' ->
    equiv O s1 s2 ->
    equiv O s2 s2' ->
    lockstep_indist_ind O (s1 :: t1) (s2' :: t2) ->
    lockstep_indist_ind O (s1 :: t1) (s2 :: s2' :: t2)
| lii_high_low_lockstep : forall s1 s1' s2 s2' t1 t2,
    ~Low O s1  ->
    ~Low O s2  ->
    Low O s1'  ->
    Low O s2'  ->
    equiv O s1 s2 ->
    lockstep_indist_ind O (s1' :: t1) (s2' :: t2) ->
    lockstep_indist_ind O (s1 :: s1' :: t1)
                         (s2 :: s2' :: t2).

Definition lockstep_ind_ni : Prop := forall o s1 s2 l1 l2,
  equiv o s1 s2 ->
  sys_trace (list_to_trace (s1 :: l1)) ->
  sys_trace (list_to_trace (s2 :: l2)) ->
  lockstep_indist_ind o (s1 :: l1) (s2 :: l2).

Lemma helper_lockstep_ind_ni_start_to_end_ni
    : forall o l1 s1' l2 s2',
  lockstep_indist_ind o l1 l2 ->
  ends_with l1 s1' ->
  ends_with l2 s2' ->
  Low o s1'  ->
  Succ s1' ->
  Low o s2' ->
  Succ s2' ->
  equiv o s1' s2'.
Proof.
  induction 1; intros;
  repeat
    match goal with
    | [H : ends_with nil _ |- _ ] => inversion H
    | [H : ends_with (_ :: nil) _ |- _ ] => inv H
    | [H : ends_with (_ :: _ ::  _) _ |- _ ] => inv H
    | [H : lockstep_indist_ind _ nil (_ :: _) |- _ ] => inversion H
    | [H : lockstep_indist_ind _ (_ :: _) nil |- _ ] => inversion H
    | [IH : ends_with ?t1 ?s1' -> ends_with ?t2 ?s2' -> _,
       H1 : ends_with (?s1 :: ?t1) ?s1',
       H2 : ends_with (?s2 :: ?t2) ?s2' |- _] => inv H1; inv H2
    end; tauto.
Qed.

Lemma lockstep_ind_ni_start_to_end_ni :
  lockstep_ind_ni -> start_to_end_ni.
Proof.
  unfold lockstep_ind_ni, start_to_end_ni.
  intros. specialize (H o s1 s2 _ _ H0 H1 H2). clear H0 H1 H2. apply H_weak.
  eauto using helper_lockstep_ind_ni_start_to_end_ni.
Qed.

(* Now let's show that on finite traces the coinductive and the
   inductive definition coincide *)

Lemma list_to_trace_TNil : forall (l : list A),
  TNil = list_to_trace l -> l = nil.
Proof. intros. destruct l; simpl in *; congruence. Qed.

Lemma list_to_trace_TCons : forall l1 (s1 : A) t1,
  TCons s1 t1 = list_to_trace l1 ->
  exists l1', l1 = s1 :: l1' /\ list_to_trace l1' = t1.
Proof. induction l1; intros; inv H; eauto. Qed.

(* The hard and useful direction of the implication
   -- induction on sum of list lengths *)
Lemma lockstep_indist_lockstep_indist_ind_gen :
  forall o n l1 l2,
  length l1 + length l2 < n ->
  lockstep_indist o (list_to_trace l1) (list_to_trace l2) ->
  lockstep_indist_ind o l1 l2.
Proof.
  induction n; intros l1 l2 H H0. inversion H. inversion H0;
    repeat (match goal with
    | [H: TNil = list_to_trace _ |- _] =>
        apply list_to_trace_TNil in H; subst
    | [H: list_to_trace _ = TNil |- _] =>
        symmetry in H; apply list_to_trace_TNil in H; subst
    | [H: TCons _ _ = list_to_trace _ |- _] =>
        apply list_to_trace_TCons in H; destruct H as [? [? ?]]; subst
    | [H: list_to_trace _ = TCons _ _ |- _] =>
        symmetry in H;
        apply list_to_trace_TCons in H; destruct H as [? [? ?]]; subst
    | [H: TCons _ _ = TNil |- _] => inversion H
    | [H: TCons _ _ = TCons _ _ |- _] => inv H
    end; simpl in *; subst).
    apply lii_lockstep_end.
    apply lii_low_lockstep; try assumption. apply IHn. omega. assumption.
    apply lii_high_end1; assumption.
    apply lii_high_end2; assumption.
    apply lii_high_high1; try assumption.
      apply IHn. simpl; omega. assumption.
    apply lii_high_high2; try assumption.
      apply IHn. simpl; omega. assumption.
    apply lii_high_low_lockstep; try assumption.
      apply IHn. simpl; omega. assumption.
Qed.

Lemma lockstep_indist_lockstep_indist_ind : forall o l1 l2,
  lockstep_indist o (list_to_trace l1) (list_to_trace l2) ->
  lockstep_indist_ind o l1 l2.
Proof. intros. eauto using lockstep_indist_lockstep_indist_ind_gen. Qed.

Lemma lockstep_ni_lockstep_ind_ni : lockstep_ni -> lockstep_ind_ni.
Proof.
  unfold lockstep_ni, lockstep_ind_ni. intros.
  apply lockstep_indist_lockstep_indist_ind. simpl in *. eauto.
Qed.

Corollary lockstep_ni_start_to_end_ni : lockstep_ni -> start_to_end_ni.
Proof. eauto using lockstep_ni_lockstep_ind_ni,
                   lockstep_ind_ni_start_to_end_ni. Qed.

(* The easy (but not so useful) direction
   -- can use either induction or coninduction.
   Not so useful, because we don't actually have that
   lockstep_ind_ni -> lockstep_ni because lockstep_ni also
   talks about infinite traces *)
Lemma lockstep_indist_ind_lockstep_indist : forall o l1 l2,
  lockstep_indist_ind o l1 l2 ->
  lockstep_indist o (list_to_trace l1) (list_to_trace l2).
Proof.
  intros. induction H; simpl.
    apply li_lockstep_end.
    apply li_low_lockstep; assumption.
    apply li_high_end1; assumption.
    apply li_high_end2; assumption.
    apply li_high_high1; assumption.
    apply li_high_high2; assumption.
    apply li_high_low_lockstep; assumption.
Qed.

(** * Proof that lockstep non-interference implies semantic
      non-interference *)

Lemma lockstep_indist_cons : forall o s1 t1 s2 t2,
  lockstep_indist o (TCons s1 t1) (TCons s2 t2) ->
  equiv o s1 s2.
Proof. intros. inv H; tauto. Qed.

Lemma lockstep_indist_semantic_indist : forall o t1 t2,
  t1 <> TNil ->
  t2 <> TNil ->
  lockstep_indist o t1 t2 -> semantic_indist o t1 t2.
Proof.
  intros o.
  destruct (H_weak_equiv o) as [_ H_weak_trans H_weak_sym].
  cofix. intros t1 t2 Ht1 Ht2 H. inv H.
  Case "li_lockstep_end". congruence.
  Case "li_low_lockstep". rename t0 into t1. rename t3 into t2.
    destruct t1 as [| s1' t1'].
      apply si_step_end1; eauto using H_weak.
      destruct t2 as [| s2' t2'].
        apply si_step_end2; eauto using H_weak.
        destruct (weak_equiv_dec o s1 s1'); destruct (weak_equiv_dec o s2 s2').
        SCase "2 x stutter".
          apply si_stutter1. assumption. apply si_stutter2. assumption.
          eapply lockstep_indist_semantic_indist ; try congruence ; assumption.
        SCase "stutter + non-stutter".
          apply lockstep_indist_cons in H2. apply H_weak in H2.
          assert (G : weak_equiv o s2 s2') by eauto using H_weak_trans.
          tauto.
        SCase "non-stutter + stutter (symmetric)".
          apply lockstep_indist_cons in H2. apply H_weak in H2.
          assert (G : weak_equiv o s1 s1') by eauto using H_weak_trans.
          tauto.
        SCase "non-stutter + non-stutter".
          apply si_step; eauto using H_weak.
          eapply lockstep_indist_semantic_indist ; try congruence.
  Case "li_high_end1".
    apply si_step_end1; eauto using H_weak.
  Case "li_high_end2".
    apply si_step_end2; eauto using H_weak.
  Case "li_high_high1".
    apply si_stutter1; eauto using H_weak.
    eapply lockstep_indist_semantic_indist ; try congruence.
  Case "li_high_high2".
    apply si_stutter2; eauto using H_weak.
    eapply lockstep_indist_semantic_indist ; try congruence.
  Case "li_high_low_lockstep (similar to li_low_lockstep)".
    destruct (weak_equiv_dec o s1 s1'); destruct (weak_equiv_dec o s2 s2').
    SCase "2 x stutter".
      apply si_stutter1. assumption. apply si_stutter2. assumption.
      apply lockstep_indist_semantic_indist; try congruence ; assumption.
    SCase "stutter + non-stutter".
      apply lockstep_indist_cons in H5. apply H_weak in H5.
      assert (G : weak_equiv o s2 s2') by eauto using H_weak_trans.
      tauto.
    SCase "non-stutter + stutter (symmetric)".
      apply lockstep_indist_cons in H5. apply H_weak in H5.
      assert (G : weak_equiv o s1 s1') by eauto using H_weak_trans.
      tauto.
    SCase "non-stutter + non-stutter".
      apply si_step; eauto using H_weak.
      eapply lockstep_indist_semantic_indist ; try congruence.
Qed.

Theorem lockstep_ni_semantic_ni : lockstep_ni -> semantic_ni.
Proof. unfold lockstep_ni, semantic_ni.
       intros.
       eapply (lockstep_indist_semantic_indist); eauto.
       congruence.
       congruence.
Qed.

(** * Dead code -- things that didn't really work*)
(*Section DeadCode.

Hypothesis Hequiv : equivalence _ equiv.

(* More (potential) properties of Low -- not yet used *)
Hypothesis Low_dec: forall s, {Low s} + {~Low s}.

Hypothesis equiv_Low : forall s s',
  equiv s s' -> (Low s <-> Low s').
Lemma Low_not_equiv_not_Low : forall s s',
  Low s -> ~Low s' -> ~equiv s s'.
Proof. intros. intro Hc. rewrite equiv_Low in H; eauto. Qed.

Fixpoint lockstep_indist_ind_try1 (xs ys : list A) : Prop :=
  match xs, ys with
  | nil, nil => True
  | x :: xs', y :: ys' =>
    equiv x y /\
      (if Low_dec x then
         lockstep_indist_ind_try1 xs' ys'
       else
         match xs' with
         | nil => True
         | x' :: xs'' =>
             if Low_dec x' then
               match ys' with
               | nil => True
               | y' :: ys'' =>
                 if Low_dec y' then
                   equiv x' y' /\ lockstep_indist_ind_try1 xs'' ys''
                 else
                   equiv y y' /\ True
                   (* XXX: wanted to write: lockstep_indist_ind_try1 xs ys'
                    Error: Cannot guess decreasing argument of fix. *)
               end
             else
               equiv x x' /\ lockstep_indist_ind_try1 xs'' ys
         end)
  | x :: _, nil => ~Low x
  | nil, y :: _ => ~Low y
  end.

Definition same_pc x y :=
  if Low_dec x then
    if Low_dec y then true else false
  else
    if Low_dec y then false else true.

Definition and_list xs := fold_left and xs True.

(* assumptions: all elements in xs have same_pc, same for ys;
   none of the lists is empty *)
Definition lockstep_sub_inds (xs ys : list A) : Prop :=
  match xs with
  | nil => False (* won't happen *)
  | x :: xs' =>
    if Low_dec x then
      length xs = length ys /\ and_list (zip_with equiv xs ys)
    else
      match ys with
      | nil => False (* won't happen *)
      | y :: ys' =>
        equiv x y /\ and_list (consecutive_with equiv xs)
                  /\ and_list (consecutive_with equiv ys)
      end
  end.

Definition lockstep_indist_ind_try2 (xs ys : list A) : Prop :=
  let xxs := group_by same_pc xs in
  let yys := group_by same_pc ys in
  let (p, rests) := zip_with_keep_rests lockstep_sub_inds xxs yys in
  let (rx, ry) := rests in
  let prest := fun r o =>
        match r with
        | nil => True
        | _ => match last_opt o with
               | None => False
               | Some los =>
                 match last_opt los with
                 | None => False
                 | Some llo => ~Low llo
                 end
               end
        end in
    and_list p /\ prest rx yys /\ prest ry xxs.

Definition lockstep_ni_try2 : Prop := forall s1 s2 l1 l2,
  equiv s1 s2 ->
  sys_trace (list_to_trace (s1 :: l1)) ->
  sys_trace (list_to_trace (s2 :: l2)) ->
  lockstep_indist_ind_try2 (s1 :: l1) (s2 :: l2).

Lemma ends_with_init : forall xs x x',
  ends_with (x :: xs) x' ->
  x :: xs = init (x :: xs) ++ x' :: nil.
Proof.
  induction xs; intros; inversion H; subst; clear H.
    reflexivity.
    simpl. rewrite (IHxs _ _ H4) at 1. reflexivity.
Qed.

Lemma lockstep_implies_start_to_end_try2 :
  lockstep_ni_try2 -> start_to_end_ni.
Proof.
  unfold lockstep_ni_try2, start_to_end_ni.
  intros. specialize (H s1 s2 _ _ H0 H1 H2). clear H0 H1 H2. apply H_weak.
  rewrite (ends_with_init H3) in H. clear H3.
  rewrite (ends_with_init H4) in H. clear H4.
Admitted.

Lemma helperX :  forall l1 s1' l2 s2',
  lockstep_indist_ind_try2 (l1 ++ s1' :: nil) (l2 ++ s2' :: nil) ->
  Low s1' ->
  Low s2' ->
  equiv s1' s2'.
Proof.
  induction l1 as [| s1 l1']; destruct l2 as [| s2 l2']; intros.
  Case "nil nil".
    unfold lockstep_indist_ind_try2 in H. simpl in H.
    destruct (Low_dec s1'); [| tauto].
      unfold zip_with, and_list in H. simpl in H. tauto.
  Case "nil cons". simpl in H.
    admit. (* XXX contradiction in H *)
  Case "cons nil". simpl in H.
    admit. (* XXX contradiction in H *)
  Case "cons cons".
    eapply IHl1'; try assumption. clear IHl1'. simpl in H.
    (* would assuming that s1 and s2 are low help? seems so, see below *)
Admitted.

End DeadCode.
*)
End Everything.




(* XXX wrong definiton,
       now fixed by additionally requiring that s1' and s2' are Low

Definition start_to end_noninterference_wrong : Prop :=
  forall s1 s2 t1 t2 s1' s2',
    equiv s1 s2 ->
    sys_trace (TCons s1 t1) ->
    sys_trace (TCons s2 t2) ->
    ends_with (TCons s1 t1) s1' ->
    ends_with (TCons s2 t2) s2' ->
    weak_equiv s1' s2'.
Will the two traces really match up at the end?
   - If "halt" happens in a low context than both machines will perform
     this operation at the same time, because the pcs will match
     - however, this didn't follow directly from the current
       lockstep non-interference below!
     - we strengthened lockstep non-interference to require
       that low states also have to terminate in lockstep
       - Q: So would it be enough to change li_nil as follows?
       | li_nil : lockstep_indist (TNil _) (TNil _)
   - If one of the machine "halts" in a high context, then we have no
     guarantees whatsoever about what the other machine does
     - The other machine can in fact continue ... PROPERTY BROKEN!
     - The WHILE language people avoid this issue by not allowing
       programs to (succesfully) halt in a high context -- structured
       programming saves the day for them
     - we could also turn halting in a high context into an error ...
     - or we could even say that the only way to succesfully terminate
       is to return to an ARet L -1 which we initially put at the
       beginning of the stack *)

(* XXX The original definition of start_to_end_noninterference using
       traces instead of lists

Inductive ends_with : trace A -> A -> Prop :=
| ends_sing : forall a, ends_with (TCons a (TNil _)) a
| ends_dcons : forall a1 a2 t a,
                 ends_with (TCons a2 t) a ->
                 ends_with (TCons a1 (TCons a2 t)) a.

Definition start_to_end_noninterference : Prop :=
  forall s1 s2 l1 l2 s1' s2',
    equiv s1 s2 ->
    sys_trace (TCons s1 t1) ->
    sys_trace (TCons s2 t2) ->
    ends_with (TCons s1 t1) s1' ->
    ends_with (TCons s2 t2) s2' ->
    Low s1' ->
    Low s2' ->
    weak_equiv s1' s2'.

(* XXX: Since these are finite traces why not represent them as such? *)
*)
*)
