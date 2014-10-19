Require Import QuickChick.
Require Import SetOfOutcomes EndToEnd.
Require Import NPeano.

Require Import ssreflect ssrnat ssrbool eqtype.

Require Import redblack.

Require Import List String.
Import ListNotations.

Open Scope string.

Open Scope Checker_scope.

(* Red-Black Tree invariant: executable definition *)

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

Definition is_black_balanced (t : tree) : bool :=
  isSome (black_height_bool t).

Fixpoint has_no_red_red (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node Red (Node Red _ _ _) _ _ => false
  | Node Red _ _ (Node Red _ _ _) => false
  | Node _ tl _ tr => has_no_red_red tl && has_no_red_red tr
  end.

Definition is_redblack_bool (t : tree) : bool  :=
  is_black_balanced t && has_no_red_red t.

Fixpoint showColor (c : color) :=
  match c with
    | Red => "Red"
    | Black => "Black"
  end.

Fixpoint tree_to_string (t : tree) :=
  match t with
    | Leaf => "Leaf"
    | Node c l x r => "Node " ++ showColor c ++ " "
                            ++ "(" ++ tree_to_string l ++ ") "
                            ++ show x ++ " "
                            ++ "(" ++ tree_to_string r ++ ")"
  end.

Instance showTree {A : Type} `{_ : Show A} : Show tree :=
  {|
    show t := "" (* CH: tree_to_string t causes a 9x increase in runtime *)
  |}.

Section Checker.
  Context {Gen : Type -> Type}
          {H: GenMonad Gen}.

  Variable genTree : Gen tree.

  Definition insert_is_redblack_checker : Gen QProp :=
    forAll arbitraryNat (fun n =>
    (forAll genTree (fun t =>
      (is_redblack_bool t ==>
       is_redblack_bool (insert n t)) : Gen QProp)) : Gen QProp).

  Definition genColor := elements Red [Red; Black].

  Fixpoint genAnyTree_max_height (h : nat) : Gen tree :=
    match h with 
    | 0 => returnGen Leaf
    | S h' =>
        bindGen genColor (fun c =>
        bindGen (genAnyTree_max_height h') (fun t1 =>
        bindGen (genAnyTree_max_height h') (fun t2 =>
        bindGen arbitraryNat (fun n =>
        returnGen (Node c t1 n t2)))))
    end.

  Definition genAnyTree : Gen tree := sized genAnyTree_max_height.

End Checker.

Definition testInsertNaive :=
  showResult (quickCheck (insert_is_redblack_checker genAnyTree)).

Extract Constant defSize => "5".
Extract Constant Test.defNumTests => "10".
QuickCheck testInsertNaive.
Extract Constant Test.defNumTests => "10000".

Section Generators.
  Context {Gen : Type -> Type}
          {H: GenMonad Gen}.

  Fixpoint genRBTree_height (h : nat) (c : color) :=
    match h with
      | 0 =>
        match c with
          | Red => returnGen Leaf
          | Black => oneof (returnGen Leaf)
                           [returnGen Leaf;
                             bindGen arbitraryNat (fun n =>
                             returnGen (Node Red Leaf n Leaf))]
        end
      | S h =>
        match c with
          | Red =>
            bindGen (genRBTree_height h Black) (fun t1 =>
            bindGen (genRBTree_height h Black) (fun t2 =>
            bindGen arbitraryNat (fun n =>
            returnGen (Node Black t1 n t2))))
          | Black =>
            bindGen genColor (fun c' =>
            match c' with
              | Red =>
                bindGen (genRBTree_height h Black) (fun tl1 =>
                bindGen (genRBTree_height h Black) (fun tl2 =>
                bindGen (genRBTree_height h Black) (fun tr1 =>
                bindGen (genRBTree_height h Black) (fun tr2 =>
                bindGen arbitraryNat (fun n =>
                bindGen arbitraryNat (fun nl =>
                bindGen arbitraryNat (fun nr =>
                returnGen (Node Red (Node Black tl1 nl tr1) n
                                (Node Black tl2 nr tr2)))))))))
              | Black =>
                bindGen (genRBTree_height h Black) (fun t1 =>
                bindGen (genRBTree_height h Black) (fun t2 =>
                bindGen arbitraryNat (fun n =>
                returnGen (Node Black t1 n t2))))
            end)
        end
    end.

  Definition genRBTree := sized (fun h => genRBTree_height h Red).

End Generators.

Definition testInsert :=
  showResult (quickCheck (insert_is_redblack_checker genRBTree)).

Extract Constant defSize => "10".
QuickCheck testInsert.
