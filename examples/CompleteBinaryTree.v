From QuickChick Require Import QuickChick EnumerationQC.

From ExtLib Require Import Monads. Import MonadNotation.
Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Open Scope bool_scope.

(* Another enumeration testing example using complete binary trees.

   If you want to generate something very specific, like a complete
   binary search tree, then it's possible that earlier choices can
   make it difficult to satisfy the completeness and binary search
   tree conditions later on.
*)

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).


Inductive perfect : nat -> Tree -> Prop :=
| perfect_leaf : perfect 0 Leaf
| perfect_node : forall n x l r,
    perfect n l ->
    perfect n r ->
    perfect (S n) (Node x l r).


Fixpoint is_perfect' (t : Tree) : (nat * bool) :=
  match t with
  | Leaf => (0, true)
  | Node _ l r =>
    let (ln, lp) := is_perfect' l in
    let (rn, rp) := is_perfect' r in
    if (lp && rp && beq_nat ln rn)
    then (S ln, true)
    else (0, false)
  end.


Fixpoint is_perfect (t : Tree) : bool :=
  match is_perfect' t with
  | (_, b) => b
  end.


Lemma is_perfect_if_is_perfect' :
  forall (t : Tree),
    is_perfect t = true -> exists d, is_perfect' t = (d, true).
Proof.
  induction t; intros H.
  - exists 0. reflexivity.
  - simpl in *.
    destruct (is_perfect' t1) eqn:Ht1.
    destruct (is_perfect' t2) eqn:Ht2.
    exists (S n0).
    destruct (b && b0 && PeanoNat.Nat.eqb n0 n1); auto.
    inversion H.
Qed.


Theorem is_perfect_iff_perfect' :
  forall (t : Tree) (n : nat), perfect n t <-> is_perfect' t = (n, true).
Proof.
  induction t; intros.
  - split; intros;
      destruct n; auto; try constructor; inversion H.
  - split; intros.
    + inversion H; subst.
      simpl.

      rename H3 into Hperft1; rename H5 into Hperft2.
      apply IHt1 in Hperft1; apply IHt2 in Hperft2.
      rewrite Hperft1; rewrite Hperft2.

      repeat rewrite andb_true_l.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl in H.
      destruct (is_perfect' t1) as [n1 b1] eqn:Hist1.
      destruct b1.
      * destruct (is_perfect' t2) as [n2 b2] eqn:Hist2.
        destruct b2.
        -- repeat rewrite andb_true_l in H.
           destruct (PeanoNat.Nat.eqb n1 n2) eqn:Hn1n2.
           ++ apply beq_nat_true in Hn1n2.
              inversion H; subst.
              constructor.
              ** apply IHt1; auto.
              ** apply IHt2; auto.
           ++ inversion H.
        -- simpl in H. inversion H.
      * simpl in H. destruct (is_perfect' t2) as [n2 b2] eqn:Hist2.
        inversion H.
Qed.


Theorem is_perfect_if_perfect :
  forall (t : Tree) (n : nat), perfect n t -> is_perfect t = true.
Proof.
  intros t n H.
  apply is_perfect_iff_perfect' in H. unfold is_perfect.
  destruct t; rewrite H; auto.
Qed.


(* Complete with relative level... *)
Inductive complete : nat -> Tree -> Prop :=
| complete_leaf : complete 0 Leaf
| complete_node_perfect : forall n x l r,
    perfect n l ->
    complete n r ->
    complete (S n) (Node x l r)
| complete_node_imperfect : forall n x l r,
    complete (S n) l ->
    perfect n r ->
    complete (S n) (Node x l r).

Fixpoint is_complete' (t : Tree) : (nat * bool) :=
  match t with
  | Leaf => (0, true)
  | Node x l r =>
    match is_perfect' l with
    | (n, true) => let (d, b) := is_complete' r in (S d, b)
    | (n1, false) =>
      match is_complete' l with
      | (n1', true) =>
        match is_perfect' r with
        | (n2, true) =>
          if PeanoNat.Nat.eqb n1' (S n2)
          then (n1', true)
          else (0, false)
        | (_, false) => (0, false)
        end
      | (_, false) => (0, false)
      end
    end
  end.

Definition is_complete (t : Tree) : bool := snd (is_complete' t).


Theorem perfect_is_complete :
  forall (t : Tree) (n : nat), perfect n t -> complete n t.
Proof.
  intros t n H; induction H; constructor; auto.
Qed.


(*
Theorem is_complete_iff_complete' :
  forall (t : Tree) (n : nat), complete n t <-> is_complete' t = (n, true).
Proof.
  split; revert n; induction t; intros.
  - inversion H; reflexivity.
  - inversion H; subst.
    + apply IHt2 in H5.
      apply is_perfect_iff_perfect' in H3.

      simpl; rewrite H3; rewrite H5.
      reflexivity.
    + apply IHt1 in H3.
      pose proof H5 as Ht2iscomp.
      apply perfect_is_complete in Ht2iscomp.
      apply is_perfect_iff_perfect' in H5.
      apply IHt2 in Ht2iscomp.

      simpl. rewrite H5. rewrite H3. rewrite Ht2iscomp.

      destruct (is_perfect' t1) eqn:Ht1perf.
      destruct b; auto.
      rewrite PeanoNat.Nat.eqb_refl; auto.
  - inversion H; constructor.
Qed.
 *)


(* Want to build up a largish BST randomly, and then enumerate.

 *)

(* How can we motivate this example? *)