From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import String.

(* Standard Binary Trees *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(* Show instance - to print counterexamples *)
Open Scope string.

Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show := 
       let fix aux t :=
         match t with
           | Leaf => "Leaf"
           | Node x l r => "Node (" ++ show x ++ ") (" ++ aux l ++ ") (" ++ aux r ++ ")"
         end
       in aux
  |}.

(* Sized Generator *)
Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf 
    | S sz' => freq [ (1,  returnGen Leaf) ;
                      (sz, liftGen3  Node g (genTreeSized' sz' g) (genTreeSized' sz' g))
                    ]
  end.

Open Scope list.

(* Shrinker - to report minimal counterexamples *)
Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : seq (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node x' l r) (s x) ++
                    map (fun l' => Node x l' r) (shrinkTree s l) ++
                    map (fun r' => Node x l r') (shrinkTree s r)
  end.

(* Grouping in a typeclass *)
Instance arbTree {A} `{_ : Arbitrary A} : Arbitrary (Tree A) :=
  {| arbitrary := sized (fun n => genTreeSized' n arbitrary) ;
     shrink := shrinkTree shrink
  |}.

(* Simple equality on Trees *)
Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.


(* Faulty mirroring function *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror l) (mirror l)
  end.

(* Mirroring twice yields the original tree *)
Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.

QuickCheck mirrorP.

DeriveShow Tree as "showTree'".
Print showTree'.
DeriveArbitrary Tree as "arbTree'" "genTreeSized".
Print genTreeSized.
Print arbTree'.

DebugDerive Tree.

(*
Theorem genTreeCorrect {A} `{_ : Arbitrary A} (size : nat) :
  semGen (@genTreeSized size A _) <--> [set tree | sizeOf tree <= size].
*)

DeriveSize Tree as "sizeTree".
Print sizeTree.

Theorem genTreeCorrect {A} `{_ : Arbitrary A} `{_ : CanonicalSize A}
        (size : nat) :
  semGen (@genTreeSized size A _) <--> [set tree | sizeOf tree <= size].
Admitted.

DeriveSizeEqs Tree as "sizeTree".
Print sizeTree_eqT.


Lemma max_lub_l_ssr n m p:
  max n m < p -> n < p.
Proof.
  move /ltP/NPeano.Nat.max_lub_lt_iff => [/ltP H1 _].
  assumption.
Qed.

Lemma max_lub_r_ssr n m p:
  max n m < p -> m < p.
Proof.
  move /ltP/NPeano.Nat.max_lub_lt_iff => [_ /ltP H1].
  assumption.
Qed.

Lemma max_lub_ssr n m p :
  n < p -> m < p -> max n m < p.
Proof.
  move => /ltP H1 /ltP H2.
  apply/ltP/NPeano.Nat.max_lub_lt; eassumption.
Qed.

DeriveSizeEqsProof Tree as "sizeTree".
Print sizeTree_eq_proof.