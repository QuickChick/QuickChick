
Definition testInsertNaiveShowDiscards :=
  showDiscards (quickCheck (insert_is_redblack_checker genAnyTree)).

(* QuickCheck testInsertNaiveShowDiscards. *)

(* replacing bind with liftGen4 doesn't help *)
  Fixpoint genAnyTree_max_height' (h : nat) : Gen tree :=
    match h with 
    | 0 => returnGen Leaf
    | S h' => liftGen4 Node genColor
                            (genAnyTree_max_height h')
                            arbitraryNat
                            (genAnyTree_max_height h')
    end.

  Definition genAnyTree' : Gen tree := sized genAnyTree_max_height'.

(* making the property trivial (discard everything) doesn't help much *)
  Definition insert_is_redblack_checker : Gen QProp :=
    (forAll genTree (fun t =>
      (false ==> true) : Gen QProp)).

(* Generating 2000 trees natively takes 83s! (the same for size 5 and 10!) *)
Require Import Gen.
Fixpoint repeatn (n : nat) (f : nat -> nat) : nat :=
  match n with
  | 0 => f 0
  | S n' => f n + repeatn n' f
  end.

Extract Constant defSize => "5".
Definition testSample := show (repeatn 100 (fun _ => (List.length (sample' genAnyTree)))).
QuickCheck testSample.

(* It has to do with discards though, since if I make the property
   true => true, then it runs fast, as fast as the property at the
   bottom of the file *)

  Definition insert_is_redblack_checker : Gen QProp :=
    forAll arbitraryNat (fun n =>
    (forAll genTree (fun t =>
      (true ==>
       true) : Gen QProp)) : Gen QProp).

Extract Constant defSize => "10".
Extract Constant Test.defNumTests => "10000".
QuickCheck testInsertNaive.

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
