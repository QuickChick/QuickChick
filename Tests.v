Require Import QuickChick Gen SetOfOutcomes.

Require Import List seq ssreflect ssrbool ssrnat ZArith.
Import ListNotations.
Require Import EqNat.
Require Import NPeano.

(* Small example with default arbitrary instances *)

Fixpoint my_delete (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: my_delete x t
  end.

Definition prop_delete_removes_every_x (x : nat) (l : list nat) :=
  negb (existsb (fun y => beq_nat y x) (my_delete x l)).

Definition test0 := 
  showResult (quickCheck prop_delete_removes_every_x).
 
QuickCheck test0.

(* Tree example showing custom datatypes *)

Inductive Tree (A : Type) :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A. 

(* Step one: Write custom generators *)
Section CustomGen.
  Context {M : Type -> Type}
          `{AbstractGen.GenMonad M}.


  Fixpoint genTreeS {A} (g : M A) (n : nat) : M (Tree A):= 
    match n with
      | O => returnGen (Leaf A)
      | S n' => 
        frequency' (returnGen (Leaf A)) 
                  [(1, returnGen (Leaf A));
                    (n, liftGen3 (Node A) g (genTreeS g n') (genTreeS g n'))]
    end.

  Definition genTree {A : Type} (g : M A) : M (Tree A) := sized (genTreeS g).
End CustomGen.

(* Step two: Use them for generation .. *)
Instance arbTree {A : Type} `{_ : Arbitrary A}
: Arbitrary (Tree A) :=
{|
  arbitrary := (genTree arbitrary);
  shrink t := 
      let fix shrinkTree (t : Tree A) := 
          match t with 
            | Leaf => []
            | Node x l r => 
              map (fun x' => Node A x' l r) (shrink x) ++ 
              map (fun l' => Node A x l' r) (shrinkTree l) ++
              map (fun r' => Node A x l r') (shrinkTree r)
          end
      in shrinkTree t
|}.

Require Import String.
Open Scope string.
Instance showTree {A : Type} `{_ : Show A} : Show (Tree A) :=
{| 
  show t := 
    let fix showTree (t : Tree A) :=
        match t with
          | Leaf => "Leaf"
          | Node x l r => "Node " ++ show x 
                                  ++ " ( " ++ showTree l ++ " ) " 
                                  ++ " ( " ++ showTree r ++ " ) "
        end
    in showTree t
|}.

(* Step 3 : .. or prove them correct   *)

Fixpoint height {A} (t : Tree A) :=
  match t with
    | Leaf => 0
    | Node a t1 t2 =>
      (max (height t1) (height t2)) + 1
  end.

Lemma leq_geq : forall n m, (n >= m)%coq_nat <-> (m <= n)%coq_nat.
Proof.
  move=> n m. split; auto.
Qed.

Lemma genTreeS_correct :
  forall {A} (g : Pred A) n,
    peq g (fun _ => True) ->
    peq (genTreeS g n) (fun t => (height t) <= n).
Proof.
  move=> A g n.
  rewrite /peq. move => Hg t. split => [H | Hleq].
  + elim: t n H => [| a t1 IHt1 t2 IHt2] n H //=.
    case: n H => // n H.
    rewrite /genTreeS -/genTreeS in H.
    rewrite -[X in _ <= X]addn1 leq_add2r.
    apply/leP/Nat.max_lub_iff. Opaque nat_compare.
    rewrite /frequency' /liftGen3 /bindGen /returnGen /PredMonad /bindP
            /returnP /choose /cmp /Randomnat //= in H.
    move:  H => //= [a' [H1 H2]].
    move : H1 => [/nat_compare_le/leP Hlow /nat_compare_ge/leq_geq/leP Hhi].
    rewrite addn0 add1n in Hhi. rewrite leq_subLR add1n Hhi in H2.
    case: (a' <= 1) H2; try discriminate.
    move => [a'' [ga' [t1' [gent1 [t2' [gent2 [Heq1 Heq2 Heq3]]]]]]] ; subst.
    split; apply/leP; auto. 
  + elim : t  n Hleq => //= [| a t1 IHt1 t2 IHt2] n Hleq.
    * case: n Hleq => //= n Hleq.
      rewrite /bindP /cmp /Randomnat.
      exists 1. split=> //=.
    * case: n Hleq => //=.
      + by rewrite addn1 ltn0.
      + move => n. rewrite -[n.+1]addn1 leq_add2r addn0.
        move=> /leP Hleq.
        rewrite /bindP /returnP.
        exists (n+2).
        split. split.
          by apply/nat_compare_le/leP;
          rewrite addn_gt0; apply/orP; right.
          by apply/nat_compare_ge/leP;
          rewrite addn1 add1n addn2.
      rewrite {1}addn2 -addnBA // leqnn.
      have -> : forall n, n.+2 <= 1 = false by elim.
      exists a; split. by apply/Hg.
      eexists; split. apply/IHt1/leP/(Max.max_lub_l _ _ _ Hleq).
      eexists; split => //=.
      apply/IHt2/leP/(Max.max_lub_r _ _ _ Hleq).
Qed.

Lemma genTree_correct :
  forall {A} (g : Pred A),
    peq g (fun _ => True) ->
    peq ((@genTree Pred _ _) g) (fun _ => True).
Proof.
  move=> A g.
  rewrite /peq /genTree. move=> H tree; split => //= _.
  exists (height tree). apply genTreeS_correct => //=.
Qed.

Open Scope list.
(* Faulty mirror function *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf A
    | Node x l r => Node A x r l
  end.

Fixpoint tree_to_list {A : Type} (t : Tree A) : list A :=
  match t with
    | Leaf => []
    | Node x l r => [x] ++ tree_to_list l ++ tree_to_list r
  end.

Definition prop_mirror_reverse (t : Tree nat) :=
  if list_eq_dec Nat.eq_dec (tree_to_list t) (rev (tree_to_list (mirror t)))
  then true 
  else false.

Definition testTree :=
  showResult (quickCheck prop_mirror_reverse).
 
QuickCheck testTree.