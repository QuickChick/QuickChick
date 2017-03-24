From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import String.

(* Tech demo / Tutorial *)

(* Property-based testing requires 4 elements :
   - Executable properties
   - Generators 
   - Shrinkers
   - Printers 
 *)

(* Out-of-the-box QuickChick : 
   basic types (nats, lists, tuples, etc.)
   - Generators, Shrinkers and Printers provided
 *)

(* Simple function to remove an element from a list *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t
              else h :: remove x t
  end.

(* Executable specification 
-  An element x is not present after removing it 
   from a list  *)
Definition removeP (x : nat) (l : list nat) :=
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).

(* QuickChick : TopLevel command *)
QuickChick removeP.

(* Now-out-of-the-box : ADTs *)

(* Standard Binary Trees in Gallina *)

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(* Show instance - to print counterexamples *)
Open Scope string.

(* Show typeclass provides "show" function *)
(* Boilerplate overhead because Coq doesn't support 
   recursion in the definition *)
Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show := 
       let fix aux t :=
         match t with
           | Leaf => "Leaf"
           | Node x l r =>
             "Node (" ++ show x ++ ") ("
                      ++ aux l ++ ") ("
                      ++ aux r ++ ")"
         end
       in aux
  |}.

(* Generate trees up to a given depth *)
(* G is a monad that is used to handle low-level
   seed plumbing *)
(* frequency is a combinator that takes [(nat, G A)] 
   and picks a generator *)
Fixpoint genTreeSized {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf (* Base case *)
    | S sz' => freq [ (1,  returnGen Leaf) ;
                      (sz, liftGen3  Node g
                               (genTreeSized sz' g)
                               (genTreeSized sz' g))
                    ]
  end.

Sample (@genTreeSized nat 3 arbitrary).

Open Scope list.

(* Shrinker - to report minimal counterexamples *)
(* Given an A, return a list of "immediately smaller" 
   ones *)
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
                    genTreeSized n arbitrary) ;
     shrink := shrinkTree shrink
  |}.

(* On to test something... need a property *)

(* Faulty mirroring function *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror l) (mirror l)
  end.

(* Simple structural equality on Trees *)
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
DeriveArbitrary Tree as "arbTree'" "genTreeSized'".
Print genTreeSized'.
Print arbTree'.

(* How do you know your generators are correct? *)
(* Well, the comment said generate everything up to a depth... *)

Print CanonicalSize.
DeriveSize Tree as "sizeTree".
Print sizeTree.

Theorem genTreeCorrect {A} `{_ : Arbitrary A} `{_ : CanonicalSize A}
        (size : nat) :
  semGen (@genTreeSized' size A _) <--> [set tree | sizeOf tree <= size].
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

(* Next in line : restricted predicates *)
(* This is actually the most common/interesting case.
   Already used inside DeepSpec:
   - Generate well-typed lambda terms (vellvm)
    
   Could be used for more:
   - Generate Haskell Core
   - CertikOS?
   - Any other ideas/suggestions?
 *)

(* Binary search tree specification *)
Inductive isBST (low high : nat) : Tree nat -> Prop :=
| BST_Leaf : isBST low high Leaf
| BST_Node : forall x l r,
               low < x -> x < high ->
               isBST low x l -> isBST x high r ->
               isBST low high (Node x l r).

(* Generator for search trees *)
Fixpoint genBST (size low high : nat)
  (glt : nat -> G (option nat)) 
  (clt : forall (x y : nat), {x < y} + {~ (x < y)})
: G (option (Tree nat)) :=
match size with
  | O => backtrack [(1, returnGen (Some Leaf))]
  | S size' => 
    backtrack
    [ (1,    returnGen (Some Leaf))
    ; (size, 
       bindGenOpt (glt low) (fun x => 
       if (clt x high) then 
         bindGenOpt (genBST size' low  x glt clt) (fun l =>
         bindGenOpt (genBST size' x high glt clt) (fun r =>
         returnGen (Some (Node x l r))))
       else returnGen None))
    ]
end.
