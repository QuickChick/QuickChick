 From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Inductive Foo (A : Type) :=
| Foo1 : Foo A
| Foo2 : A -> Foo A -> Foo A -> Foo A.

Arguments Foo1 {A}.
Arguments Foo2 {A}.

Inductive Good {A : Type} : Foo A -> Prop :=
| Good1 : Good Foo1
| Good2 : forall a f, Good (Foo2 a f f).

QuickChickDebug Debug On.
MergeTest (fun x => Good x).

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Inductive bal : nat -> Tree -> Prop :=
| bal_leaf0 : bal 0 Leaf
| bal_leaf1 : bal 1 Leaf
| bal_node : forall n t1 t2 m,
    bal n t1 -> bal n t2 -> bal (S n) (Node m t1 t2).

Derive (Arbitrary, Show) for Tree.



Merge (fun t => bst lo hi t) With (fun t => bal n t)
      As bst_bal.

Print bst_bal.

Fixpoint size (t : Tree) : nat :=
  match t with
  | Leaf => 0
  | Node x l r => 1 + max (size l) (size r)
  end.

(*
Inductive bstbal : nat -> nat -> nat -> Tree -> Prop :=
| leafleaf0 : forall lo hi, bstbal lo hi 0 Leaf
| leafleaf1 : forall lo hi, bstbal lo hi 1 Leaf
| nodenode : forall lo hi n x l r,
    le (S lo) x -> le (S x) hi ->
    bstbal lo hi n l -> bstbal x hi n r -> bstbal lo hi (S n) (Node x l r).

Derive ArbitrarySizedSuchThat for (fun t => bal n t).
Derive DecOpt for (bal n t).
Derive EnumSizedSuchThat for (fun n => bal n t).

Definition Empty {A} (e : E A) (n : nat) : bool :=
  match (Enumerators.run e n) with
  | LazyList.lnil => false
  | LazyList.lcons _ _ => true
  end.

Derive DecOpt for (le x y).

Derive ArbitrarySizedSuchThat for (fun x => le y x).

QuickChickWeights [ (bst_leaf, 1) ; (bst_node, size) ].
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive ArbitrarySizedSuchThat for (fun t => bstbal a b c t).

Sample (@arbitrarySizeST _ (fun t => bst 0 10 t) _ 5).

Print GenSizedSuchThatbst.

Sample (@arbitrarySizeST _ (fun t => bst 0 42 t) _ 10).

Derive DecOpt for (bst lo hi t).

Check @decOpt.
Check GenSizedSuchThatbst.
 
Compute (@decOpt (bal 0 Leaf) _ 5).

Definition balBst_any_test :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 42 t) _ 10)
              (fun t =>
                 if Empty (@enumSizeST _ (fun n => bal n t) _ 10) 10
                 then (collect (size t) (checker true)) else (checker tt)).

(*QuickChick balBst_any_test.*)

Definition balBst_merged :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bstbal 0 42 3 t) _ 10)
              (fun t => checker true).

(* QuickChick balBst_merged. *)

(*An issue is that these two aren't really comparing the same thing.
Ideally, we should generate trees for which all three parameters can be
anything.*)

Inductive foo : nat -> Prop :=
| Foo1 : foo O
| Foo2 : forall n, foo n -> foo (S n)
| Foo3 : forall n1 n2, foo 0 -> foo (S n1) -> foo (S n2).



(*
Merge (fun t => bst lo hi t) With (fun t => bal n t)
      As bstbalmerged.
*)

 *)

(*Same variable name test:*)

Inductive P : nat -> Prop :=
| bla_P : forall n, P n.

Inductive Q : nat -> Prop :=
| bla_Q : forall n, Q (S n).

Merge (fun n => P n) With (fun n => Q n) As doesntgetusedanyway.

(*This should have a constructor!*)
Print doesntgetusedanyway.

(*Simple definition test*)
Definition naaat := nat.

Inductive P3 : naaat -> Prop:=.
Inductive Q3 : naaat -> Prop:=.

Merge (fun n => P3 n) With (fun n => Q3 n) As PQ3.

Print PQ3.

Inductive Term : Type :=
| var : nat -> Term
| app : Term -> Term -> Term
| lam : Term -> Term
| const : nat -> Term
| add : Term -> Term -> Term.

Inductive Ty : Type :=
| arr : Ty -> Ty -> Ty
| number : Ty.

(*
Definition Context := list Ty.
 *)

Inductive Var : list Ty -> Ty -> nat -> Prop :=
| zero : forall t g, Var (cons t g) t 0
| suc : forall a b g n, Var g a n -> Var (cons b g) a (S n).

Inductive typed : list Ty -> Ty -> Term -> Prop :=
| t_var : forall g n t, Var g t n -> typed g t (var n)
| t_app : forall a b g e1 e2, typed g (arr a b) e1 -> typed g a e2
                              -> typed g b (app e1 e2)
| t_lam : forall a b g e, typed (cons a g) b e -> typed g (arr a b) (lam e)
| t_const : forall n g, typed g number (const n)
| t_add : forall e1 e2 g, typed g number e1 -> typed g number e2 -> typed g number (add e1 e2).

Theorem falses : nat -> list bool.
Proof.
  intros n.
  induction n.
  - apply nil.
  - apply cons. apply false. apply IHn.
Defined.

Inductive nand : bool -> bool -> bool -> Prop :=
| nand_ff : nand false false true
| nand_ft : nand false true true
| nand_tf : nand true false true
| nand_tt : nand true true false.

Inductive combine : list bool -> list bool -> list bool -> Prop :=
| combine_nil : combine nil nil nil
| combine_cons : forall as1 as2 as3 a1 a2 a3, nand a1 a2 a3
      -> combine as1 as2 as3 -> combine (cons a1 as1) (cons a2 as2) (cons a3 as3).

Inductive var_linear : list bool -> nat -> Prop :=
| zero_lin : forall n, var_linear (true :: falses n) 0
| suc_lin : forall u n, var_linear u n -> var_linear (cons false u) (S n).

(*
Inductive linear : list bool -> Term -> Prop :=
| l_var : forall u n, var_linear u n -> linear u (var n)
| l_app : forall u1 u2 u3 e1 e2, linear u1 e1 -> linear u2 e2
                                 -> combine u1 u2 u3 -> linear u3 (app e1 e2)
| l_con  : forall len n, linear (falses len) (const n)
| l_lam : forall u e, linear (true :: u) e -> linear u (lam e)
| l_add : forall u1 u2 u3 e1 e2, linear u1 e1 -> linear u2 e2
                                 -> combine u1 u2 u3 -> linear u3 (add e1 e2).
*)

Inductive linear : list bool -> Term -> Prop :=
| l_var : forall u_ n_, var_linear u_ n_ -> linear u_ (var n_)
| l_app : forall u1_ u2_ u3_ e1_ e2_, linear u1_ e1_ -> linear u2_ e2_
                                 -> combine u1_ u2_ u3_ -> linear u3_ (app e1_ e2_)
| l_con  : forall len_ n_, linear (falses len_) (const n_)
| l_lam : forall u_ e_, linear (true :: u_) e_ -> linear u_ (lam e_)
| l_add : forall u1_ u2_ u3_ e1_ e2_, linear u1_ e1_ -> linear u2_ e2_
                                 -> combine u1_ u2_ u3_ -> linear u3_ (add e1_ e2_).

Merge (fun t => typed gamma ty t) With (fun t => linear used t) As typed_and_linear.
Print typed_and_linear.

Axiom sub : Term -> Term -> Term.

Inductive Even : nat -> Prop :=
| Z_Even : Even 0
| SS_Even : forall n, Even n -> Even (S (S n)).

Inductive Odd : nat -> Prop :=
| SZ_Odd : Odd 1
| SS_Odd : forall n, Odd n -> Odd (S (S n)).

Merge (fun n => Even n) With (fun n => Odd n) As EO.

Print EO.

Inductive step : Term -> Term -> Prop :=
| beta_step : forall e1 e2,
    step (app (lam e1) e2) (sub e1 e2).

Print typed.

Merge (fun t => typed gamma ty t) With (fun t => step t t2) As steptype.

Print steptype.

Inductive less : nat -> nat -> Prop :=
| less_n : forall n, less n n
| less_S : forall m n, less n m -> less n (S m).

Merge (fun y => less x y) With (fun y => less y z) As between.
Print between.


(*I think this doesn't work because of parameters!*)

Print le.

Merge (fun y => le x y) With (fun y => le z y) As between2.

(*Make sure that list works
merge length and sorted*)

(*red balck trees, 1) is red-black alternating
2) bst*)

(*write algorithm*)
