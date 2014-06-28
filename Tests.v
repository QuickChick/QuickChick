Require Import QuickChick.

Require Import List seq ssreflect ssrbool ssrnat ZArith eqtype.
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


  Fixpoint genTreeS {A} (g : M A) (n : nat) : M (Tree A):= nosimpl (
    match n with
      | O => returnGen (Leaf A)
      | S n' => 
        frequency' (returnGen (Leaf A)) 
                  [(1, returnGen (Leaf A));
                    (n, liftGen3 (Node A) g (genTreeS g n') (genTreeS g n'))]
    end).

  Definition genTree {A : Type} (g : M A) : M (Tree A) := sized (genTreeS g).

End CustomGen. 
 
Instance arbTree {A} `{Arbitrary A} : Arbitrary (Tree A) :=
{|
  arbitrary gen genM := @genTree gen genM A arbitrary;
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


Open Scope list.

(* Step 2: Use them for generation .. *)

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

(* Step 3 : .. or prove them correct   *)

Require Import SetOfOutcomes.

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
    g <--> (fun _ => True) ->
    (genTreeS g n) <--> (fun t => (height t) <= n).
Proof.
  move=> A g n. 
  Opaque frequency' liftGen3 returnGen bindGen. 
  elim : n => //= [| n IHn] Hg t. 
  * split.
    + rewrite returnGen_def. by move => <-.  
    + case: t => //= a t1 t2. by rewrite addn1 ltn0. 
  * move/IHn : (Hg)=> HgenT. split => [| Hheight].  
    + move/frequency_equiv. move => 
      [[n' [gTree [[[Heq1 Heq2] | [[Heq1 Heq2] | //=]] [H2 _]]]] | [H1 H2]]; subst;
      try (by rewrite returnGen_def in H2; rewrite -H2).
      rewrite liftGen3_def in H2.
      move : H2 => [a1 [ga1 [t1 [/HgenT Hgt1 [t2 [/HgenT Hgt2 Heq]]]]]]; subst.
      simpl. rewrite -[X in _ <= X]addn1 leq_add2r. 
        by apply/leP/Nat.max_lub_iff; split; apply/leP. 
    + apply/frequency_equiv. left.  
      case: t Hheight => [| a t1 t2] //=.
      - move => _. exists 1. eexists. split. by constructor.
        by split.
      - rewrite -[X in _ <= X]addn1 leq_add2r.  
        move/leP/Nat.max_lub_iff => [/leP/HgenT leq1 /leP/HgenT leq2]. 
        exists n.+1. exists (liftGen3 (Node A) g (genTreeS g n) (genTreeS g n)).
        split => //=. by right; left. 
        split => //=. rewrite liftGen3_def. 
        by repeat (eexists; split); auto; apply/Hg. 
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