From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Lemmas.

Require Import String.

(* Standard Binary Trees in Gallina *)

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

(* Sized Generator - generate trees up to a given depth *)
Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf 
    | S sz' => freq [ (1,  returnGen Leaf) ;
                      (sz, liftGen3  Node g
                               (genTreeSized' sz' g)
                               (genTreeSized' sz' g))
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
  {| arbitrary := sized (fun n => 
                    genTreeSized' n arbitrary) ;
     shrink := shrinkTree shrink
  |}.

(* Faulty mirroring function *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror l) (mirror l)
  end.

(* Simple equality on Trees *)
Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.


(* Mirroring twice yields the original tree *)
Definition mirrorP (t : Tree nat) := 
  eq_tree (mirror (mirror t)) t.

QuickCheck mirrorP.

(* Derive printers and generators automatically *)

DeriveShow Tree as "showTree'".
Print showTree'.
DeriveArbitrary Tree as "arbTree'" "genTreeSized".
Print genTreeSized.
Print arbTree'.

(* How do you know your generators are correct? *)
(* Well, the comment said generate everything up to a depth... *)

(*
Theorem genTreeCorrect {A} `{_ : Arbitrary A} (size : nat) :
  semGen (@genTreeSized size A _) <--> 
  [set tree | sizeOf tree <= size].
*)

Print CanonicalSize.
DeriveSize Tree as "sizeTree".
Print sizeTree.

Theorem genTreeCorrect {A} `{_ : Arbitrary A} `{_ : CanonicalSize A}
        (size : nat) :
  semGen (@genTreeSized size A _) <--> [set tree | sizeOf tree <= size].
Admitted.

DeriveSizeEqs Tree as "sizeTree".
Print sizeTree_eqT.

(* 
sizeTree_eqT = fun (size : nat) (A : Type) (H : CanonicalSize A) =>
Leaf
|: \bigcup_(f0 in (fun _ : A => True))
   \bigcup_(f1 in (fun f1 : Tree A => sizeOf f1 < size))
   \bigcup_(f2 in (fun f2 : Tree A => sizeOf f2 < size))
        [set Node f0 f1 f2] 

<--> 

(fun x : Tree A => sizeOf x <= size)

: nat -> forall A : Type, CanonicalSize A -> Prop
*) 

DeriveSizeEqsProof Tree as "sizeTree".
Print sizeTree_eq_proof.

Definition bindGenOpt {A B} (g : G (option A)) (f : A -> G (option B)) : G (option B) :=
  bindGen g (fun ma => 
  match ma with
    | None => returnGen None
    | Some a => f a
  end).

Fixpoint genBST (size low high : nat)
  (glt : nat -> G (option nat)) (clt : forall (x y : nat), {x < y} + {~ (x < y)})
: G (option (Tree nat)) :=
  match size with
    | O => backtrack [(1, returnGen (Some Leaf))]
    | S size' => 
      backtrack [ (1,    returnGen (Some Leaf))
                ; (size, bindGenOpt (glt low) (fun x => 
                         if (clt x high) then returnGen None
                         else bindGenOpt (genBST size' low  x glt clt) (fun l =>
                              bindGenOpt (genBST size' x high glt clt) (fun r =>
                              returnGen (Some (Node x l r))))))
                ]
  end.
