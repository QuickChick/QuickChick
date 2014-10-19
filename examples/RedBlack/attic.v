Definition showDiscards (r : Result) :=
  match r with
  | Success ns nd _ _ => "Success: number of successes " ++ show ns ++ newline ++
                         "         number of discards "  ++ show nd ++ newline
  | _ => showResult r
  end.

Definition testInsertNaiveShowDiscards :=
  showDiscards (quickCheck (insert_is_redblack_checker genAnyTree)).

(* QuickCheck testInsertNaiveShowDiscards. *)

(* CH: the following implementation seems to me rather inefficient
   (quadratic in the tree height); there seems to be too much
   redundancy between the two fixpoints (as shown formally by
   has_black_height), can't they be merged? Or can't at least the
   checks in black_height be all removed?

   Matt Might has a simpler and more efficient implementation:
   http://matt.might.net/articles/quick-quickcheck/
   Implemented above as is_redblack_bool
   That is simpler and much more efficient (overall time: 5.19s vs 8.53s) *)

Fixpoint is_redblack_bool (t : tree) (c: color) : bool  :=
  match t with
    | Leaf => true
    | Node c' tl _ tr =>
      match c' with
        | Black =>
          (black_height_bool tl == black_height_bool tr) &&
          is_redblack_bool tl Black && is_redblack_bool tr Black
        | Red =>
          match c with
            | Black =>
              (black_height_bool tl == black_height_bool tr) &&
              is_redblack_bool tl Red && is_redblack_bool tr Red
            | Red => false
          end
      end
  end.

Lemma has_black_height :
  forall t c, is_redblack_bool t c -> exists n, black_height_bool t = Some n.
Proof.
  move=> t. induction t; move => c' Hdec; first by exists 0.
  destruct c'; destruct c; simpl in *; (try by discriminate);
  move/andP: Hdec => [/andP [/eqP Heq  /IHt1 [n1 Ht1]]  /IHt2 [n2 Ht2]];
  remember (black_height_bool t1) as h1;
  remember (black_height_bool t2) as h2;
  destruct h1, h2; (try discriminate);
  inversion Heq; subst; eexists; by rewrite eq_refl.
Qed.

Lemma is_redblackP :
  forall (t : tree) (c : color) n,
    reflect (is_redblack t c n)
            (is_redblack_bool t c && (black_height_bool t == Some n)).
Proof.
  move => t c n.
  apply (@iffP (is_redblack_bool t c && (black_height_bool t == Some n)));
    first by apply/idP.
  - move: c n. induction t; intros c' n' Hrb.
    + move/andP : Hrb => [_ /= /eqP [Hn]]; subst. by constructor.
    + move/andP : Hrb => [Hdec /eqP Hheight].
      destruct c'; destruct c; simpl in *; (try by discriminate);
      move/andP: Hdec => [/andP [/eqP Heq  Ht1]  Ht2];
      remember (black_height_bool t1) as h1;
      remember (black_height_bool t2) as h2;
      destruct h1, h2; (try discriminate);
      inversion Heq; subst; rewrite eq_refl in Hheight;
      inversion Hheight; subst;
      constructor;
      (try by (apply IHt1; apply/andP; split => //));
      by (apply IHt2; apply/andP; split => //).
  - move=> Hrb. induction Hrb; (try by reflexivity);
    move/andP: IHHrb1 => [Htl /eqP Hhtl];
    move/andP: IHHrb2 => [Htr /eqP Hhtr]; subst; simpl;
    rewrite Hhtl Hhtr; repeat (apply/andP; split => //);
    by rewrite eq_refl.
Qed.

Lemma is_redblack_exP :
  forall (t : tree) (c : color),
    reflect (exists n, is_redblack t c n)
            (is_redblack_bool t c).
Proof.
  move=> t c.
  apply (@iffP (is_redblack_bool t c));
    first by apply/idP.
  - move=> Hrb.  move/has_black_height: (Hrb) => [n Hh]. exists n.
    apply/is_redblackP. apply/andP; split. exact Hrb.
      by apply/eqP.
  - by move => [n /is_redblackP/andP [Hrb _]].
Qed.

*)
