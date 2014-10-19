Require Import ssreflect ssrnat ssrbool eqtype.

(* Formalization inspired from
   https://www.cs.princeton.edu/~appel/papers/redblack.pdf *)

Inductive color := Red | Black.

Inductive tree :=
  | Leaf : tree
  | Node : color -> tree -> nat -> tree -> tree.


(* RedBlack invariant *)

(* Inductive *)
Inductive is_redblack : tree -> color -> nat -> Prop :=
  | IsRB_leaf: forall c, is_redblack Leaf c 0
  | IsRB_r: forall n tl tr h,
              is_redblack tl Red h -> is_redblack tr Red h ->
              is_redblack (Node Red tl n tr) Black h
  | IsRB_b: forall c n tl tr h,
              is_redblack tl Black h -> is_redblack tr Black h ->
              is_redblack (Node Black tl n tr) c (S h).

(* Boolean *)
Fixpoint black_height_bool (t: tree) : option nat :=
  match t with
    | Leaf => Some 0
    | Node c tl _ tr =>
      let h1 := black_height_bool tl in
      let h2 := black_height_bool tr in
      match h1, h2 with
        | Some n1, Some n2 =>
          if n1 == n2 then
            match c with
              | Black => Some (S n1)
              | Red => Some n1
            end
          else None
        | _, _ => None
      end
  end.

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


(* insertion *)

Definition balance rb t1 k t2 :=
  match rb with
    | Red => Node Red t1 k t2
    | _ =>
      match t1 with
        | Node Red (Node Red a x b) y c =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | Node Red a x (Node Red b y c) =>
          Node Red (Node Black a x b) y (Node Black c k t2)
        | a => match t2 with
                 | Node Red (Node Red b y c) z d =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | Node Red b y (Node Red c z d) =>
                   Node Red (Node Black t1 k b) y (Node Black c z d)
                 | _ => Node Black t1 k t2
               end
      end
  end.

Fixpoint ins x s :=
  match s with
    | Leaf => Node Red Leaf x Leaf
    | Node c a y b => if x < y then balance c (ins x a) y b
                      else if y < x then balance c a y (ins x b)
                           else Node c a x b
  end.

Definition makeBlack t :=
  match t with
    | Leaf => Leaf
    | Node _ a x b => Node Black a x b
  end.

Definition insert x s := makeBlack (ins x s).


Definition insert_preserves_redblack :=
  forall x s h, is_redblack s Red h ->
                exists h', is_redblack (insert x s) Red h'.

Definition insert_preserves_redblack_bool :=
  forall x s, is_redblack_bool s Red -> is_redblack_bool (insert x s) Red.

Lemma insert_preserves_redblack_equiv:
  insert_preserves_redblack <-> insert_preserves_redblack_bool.
Proof.
  rewrite /insert_preserves_redblack /insert_preserves_redblack_bool. split.
  - move => H x s /is_redblack_exP [n /H Hrb]. apply/is_redblack_exP.
    apply Hrb.
  - move => H x s n Hrb. apply/is_redblack_exP. apply H. apply/is_redblack_exP.
    by exists n.
Qed.