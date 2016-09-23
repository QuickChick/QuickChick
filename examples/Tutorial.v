From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import List ZArith.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

(* Find a bug in the following definition... *)
Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

(* ... with this specification :) *)
Definition removeP (x : nat) (l : list nat) :=
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).

QuickChick removeP.

(** First limitation: removeP must be executable. Can't QuickCheck the following! *)

Definition remove_spec :=
  forall x l, ~ In x (remove x l).

(** Ingredients: 

  - Executable property   

  - Printer
  - Generator 
  - Shrinker

 *)

(** Printing *)

(* For printing QuickChick uses a "Show" typeclass, like Haskell *)
(* Provides function "show" *)

Print Show. 

(* Built-in instances for 
   
   - string :)
   - nat, bool, Z : via Extraction to "Prelude.show"
   - list, pair, option 
*)

(* Writing your own show instance is easy! *)
Inductive Color := Red | Green | Blue | Yellow.

Require Import String. Open Scope string.
Instance show_color : Show Color :=
  {| show c :=
       match c with
         | Red    => "Red"
         | Green  => "Green"
         | Blue   => "Blue"
         | Yellow => "Yellow"
       end
  |}.

Eval compute in (show Green).

(** Generators *)

(* A Generator for elements of some type A is a monadic object of type G A 

   G is a monad that serves as an abstraction over 

   - random seeds
   - size information

   Standard monadic functions have the "Gen" suffix
 *)

Check bindGen.
(* bindGen
     : G ?20 -> (?20 -> G ?21) -> G ?21
*)

Check returnGen.
(* returnGen
     : ?22 -> G ?22
*)

(* QuickChick also provides "liftM" functions (1-5), "sequence" and "foldM" *)

(* Primitive generators (for bool, nat, Z) are provided via extraction *)

Check choose.

(* Sample is a command that runs a generator a bunch of times *)
Sample (choose(0, 10)).

(* For lists, there are two combinators *)

Check listOf.
(* listOf
     : G ?25 -> G (list ?25)

   Takes as input a generator for the elements and returns a generator for lists 
 *)
Sample (listOf (choose (0,4))).

Check vectorOf.
(* listOf
     : nat -> G ?26 -> G (list ?26)

   Takes as input a number n, a generator for the elements and returns a generator for lists
   of length n.
*)

(** Sizes 

    How does "listOf" decide how big of a list to generate?

    Answer: G hides size information!
      
      - QC progressively tries larger and larger sizes
      - Every generator can choose to interpret input size however it wants
*)

(** More combinators *)

Definition genColor : G Color :=
  elems [ Red ; Green ; Blue ; Yellow ].

(* elems is notation for "elements", which takes an additional "default" *)
Check elements.
(* elements : ?33 -> list ?33 -> G ?33 *)

Sample genColor.

(** A More Comprehensive Example: Trees! *)
Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show := 
       let fix aux t :=
         match t with
           | Leaf => "Leaf"
           | Node x l r => "Node (" ++ show x ++ ") (" ++ aux l ++ ") (" ++ aux r ++ ")"
         end
       in aux
  |}.

(* New combinators: oneof, frequency *)

(*
Fixpoint genTree {A} (g : G A) : G (Tree A) :=
  oneOf [ returnGen (Leaf A) ;
          liftGen3 (Node A)  g (genTree g) (genTree g) ].
*)

Fixpoint genTreeSized {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen (Leaf A)
    | S sz' => oneOf [ returnGen (Leaf A) ;
                       liftGen3  (Node A) g (genTreeSized sz' g) (genTreeSized sz' g)
                     ]
  end.

Sample (genTreeSized 3 (choose(0,3))).

(* Problem: way too many Leafs! 
   Solution: frequency 
 *)

Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen (Leaf A)
    | S sz' => freq [ (1,  returnGen (Leaf A)) ;
                      (sz, liftGen3  (Node A) g (genTreeSized' sz' g) (genTreeSized' sz' g))
                    ]
  end.

Sample (genTreeSized' 3 (choose(0,3))).

(* Bugs are not only in the implementation, they can be in the specification as well! *)
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf A
    | Node x l r => Node A x (mirror r) (mirror l)
  end.

Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.

(* mirror should be unipotent *)
Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) mirrorP).

(* Let's try a wrong property *)
Definition faultyMirrorP (t : Tree nat) := eq_tree (mirror t) t.

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) faultyMirrorP).

(* Is this really helpful though? What's the bug? Are the numbers relevant? *)

(** Shrinking *)
(*  There is another variant of "forAll", called "forAllShrink" that takes 
    an additional argument of type "A -> list A". 
 *)
Print shrinkList.

Open Scope list.
Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : seq (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node A x' l r) (s x) ++
                    map (fun l' => Node A x l' r) (shrinkTree s l) ++
                    map (fun r' => Node A x l r') (shrinkTree s r)
  end.

QuickChick (forAllShrink (genTreeSized' 5 (choose (0,5))) (shrinkTree shrink) faultyMirrorP).

(* Putting it all together: Typeclass magic! *)
Print sized.

Instance arbTree {A} `{_ : Arbitrary A} : Arbitrary (Tree A) :=
  {| arbitrary := sized (fun n => genTreeSized' n arbitrary) ;
     shrink := shrinkTree shrink
  |}.

QuickCheck faultyMirrorP.

(* quickCheck : forall prop. Checkable prop => prop -> Result 
   But what *is* Checkable? 

   Easy - booleans: We can always tell if a boolean is true or not :)

   Magic - functions!
 *)
Print testFun.

(* collect : Show B => B -> prop -> prop *)

Fixpoint size {A} (t : Tree A) : nat :=
  match t with
    | Leaf => O
    | Node _ l r => 1 + size l + size r
  end.

Definition treeProp (g : nat -> G nat -> G (Tree nat)) n :=
  forAll (g n (choose (0,n))) (fun t => 
  collect (size t) true).

QuickChick (treeProp genTreeSized  5).
QuickChick (treeProp genTreeSized' 5).

(* New! Experimental! Deriving magic! *)
DeriveShow Tree as "showTree'".
Print showTree'.

DeriveArbitrary Tree as "arbTree'".
Print arbTree'.

(* TALK END POINT - Probably end here... *)

(* Future directions: dependent inductives! *)
Inductive Foo :=
| Foo1 : Foo
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

(* Good Foos! *)
Inductive goodFoo : nat -> Foo -> Prop :=
    Good1 : forall n : nat, goodFoo n Foo1
  | Good2 : forall (n : nat) (foo : Foo),
            goodFoo 0 foo -> goodFoo n (Foo2 foo)
  | Good3 : forall (n : nat) (foo2 : Foo),
            goodFoo n foo2 -> goodFoo n (Foo3 n Foo1 foo2).

Fixpoint genGoodFooS (sz : nat) (n : nat) : G {foo | goodFoo n foo} :=
  match sz with
    | O => returnGen (exist (goodFoo n) Foo1 (Good1 n))
    | S sz' =>
      freq [ (1, returnGen (exist (goodFoo n) Foo1 (Good1 n)))
           ; (4, bindGen (genGoodFooS sz' 0) (fun foo => 
                 let (f, bf) := foo in 
                 returnGen (exist (goodFoo n) (Foo2 f) (Good2 n f bf))))
           ; (sz,let f1 := Foo1 in
                 bindGen (genGoodFooS sz' n) (fun foo2 =>
                 let (f2, bf2) := foo2 in
                 returnGen (exist (goodFoo n) (Foo3 n f1 f2) 
                                  (Good3 n f2 bf2))))
           ]
  end.

(*
Inductive goodFoo' (n : nat) : Foo -> Prop :=
| Good1'' : _W 1  -> goodFoo' n Foo1
| Good2'' : _W 4  -> forall foo, goodFoo' 0 foo -> goodFoo' n (Foo2 foo)
| Good3'' : _Size -> forall foo2,
            goodFoo' n foo2 ->
            goodFoo' n (Foo3 n Foo1 foo2).

DeriveGenerators goodFoo' as "goodFooDerived" and "g".
Print goodFooDerived.
*)
