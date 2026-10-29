From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

#[local]
Instance DecOpt_and 
    {P1} `{DO1 : DecOpt P1}
    {P2} `{DO2 : DecOpt P2} : 
    DecOpt (P1 /\ P2) := {
  decOpt := 
    fun n => 
    match @decOpt P1 DO1 n with
    | Some true => @decOpt P2 DO2 n
    | _ => Some false
    end
}.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Sized, Show) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_Leaf : forall lo hi, bst lo hi Leaf
| bst_Node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun x => le x y).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive DecOpt for (bst lo hi t).

Definition genBetween lo hi: G (option nat) :=
  if (lo <= hi)?
    then
      bindGenOpt (genST (fun x => le x (hi - lo))) (fun x => 
      ret (Some (x + lo)))
    else ret None.

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo <= x /\ x <= hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

(* Instance Decbst : forall lo hi t, Dec (bst lo hi t). *)

Fixpoint maxNode x t: nat :=
  match t with 
  | Leaf => x
  | Node y l r => maxNode y r
  end.

Fixpoint minNode x t: nat :=
  match t with 
  | Leaf => x
  | Node y l r => minNode y l
  end.

(* How much to weight branches, as a function of their size *)
Definition mut_bst_branch_weighting (n: nat): nat := 2 * n.

(* Keeps generating values that satisfy the first property until one also 
   satisfies the second property. *)
Definition genSTF {A : Type} 
    (P1 : A -> Prop) `{GenSuchThat A P1}
    (P2 : A -> bool) :
    G (option A) :=
  backtrack [
    ( 1
    , bindGenOpt (@arbitraryST A P1 _) (fun a =>
      if P2 a then
        ret (Some a)
      else 
        ret None)
    )
  ].

(* Keeps generating values that satisfy the first property until one also 
   satisfies the second property. *)
Definition genSTF'
    {A : Type}
    (P : A -> Prop * bool) `{GenSuchThat A (fun a => fst (P a))} :
    G (option A) :=
  backtrack [
    ( 1
    , bindGenOpt (@arbitraryST A (fun a => fst (P a)) _) (fun a =>
      if snd (P a)
        then ret (Some a)
        else ret None
      )
    )
  ].

Definition allb (l : list bool) : bool := forallb id l.

Fixpoint mut_bst (lo hi: nat) (t: Tree) : G (option Tree) :=
  let n := size t in 
  (* preserves size *)
  let regenerate : G (option Tree) :=
        @arbitrarySizeST _ (fun t => bst lo hi t) _ n in
  match t return G (option Tree) with 
  | Leaf => 
    backtrack [ 
      (* regenerate *)
      
      ( 1
      , regenerate )

      (* -------------------------------------------------------------------- *)
      (* recombine *)
      
      (* recombine: Leaf [EMPTY] *)
      (*    nothing to recombine with *)
      (*    nothing to recombine into *)
      (*    so, result will be same  *)
      
      (* -------------------------------------------------------------------- *)
      (* recombine: Node x Leaf r via bst_Node *)
      (*    generate: x, l *)
    ; ( 1
      (* , bindGenOpt (genSTF (fun x => lo <= x) (fun x => allb [(x <= hi)? ; is_bst lo x Leaf])) (fun x =>
        bindGenOpt (genSTF (fun r => bst x hi r) (fun r => allb [])) (fun r => *)
      , bindGenOpt (genSTF' (fun x => (lo <= x, allb [(x <= hi)? ; is_bst lo x Leaf] ))) (fun x =>
        bindGenOpt (genSTF' (fun r => bst x hi r, allb [])) (fun r =>
        ret (Some (Node x Leaf r))))
      )
      
      (* recombine: Node x l Leaf via bst_Node *)
      (*    generate: x, l *)
    ; ( 1
      , bindGenOpt (genSTF (fun x => x <= hi) (fun x => allb [(lo <= x)? ; is_bst x hi Leaf])) (fun x =>
        bindGenOpt (genSTF (fun l => bst lo x l) (fun l => allb [])) (fun l =>
        ret (Some (Node x l Leaf))))
      )
      
      (* -------------------------------------------------------------------- *)
      (* mutate child *)
      (* no children to mutate *)  
    ]
  | Node x l r =>
    backtrack [
      (* -------------------------------------------------------------------- *)
      (* regenerate *)
        
      ( 1
      , regenerate )

      (* -------------------------------------------------------------------- *)
      (* recombine *)

      (* recombine: Leaf [EMPTY] *)
      (*    nothing to recombine into *)
      
      (* recombine: Node x' l' r  via bst_Node *)
      (*    regenerate x', l' *)
      ; ( 1
        , bindGenOpt (genSTF (fun x' => x' <= lo) (fun x' => allb [(x' <= hi)? ; is_bst x' hi r])) (fun x' =>
          bindGenOpt (genSTF (fun l' => bst lo x' l') (fun l' => allb [])) (fun l' =>
          ret (Some (Node x' l' r))))
        )    
      
      (* recombine: Node x' l  r' via bst_Node *)
      (*    regenerate x', r' *)
      ; ( 1
        , bindGenOpt (genSTF (fun x' => x' <= lo) (fun x' => allb [(x' <= hi)? ; is_bst lo x' l])) (fun x' =>
          bindGenOpt (genSTF (fun r' => bst lo x' r') (fun r' => allb [])) (fun r' =>
          ret (Some (Node x' l r'))))
        )
      
      (* recombine: Node x  l' r' via bst_Node *)
      (*    regenerate l', r' *)
      ; ( 1
        , bindGenOpt (genSTF (fun l' => bst lo x l') (fun l' => allb [])) (fun l' =>
          bindGenOpt (genSTF (fun r' => bst x hi r') (fun r' => allb [])) (fun r' =>
          ret (Some (Node x l' r'))))
        )
      
      (* recombine: Node x' l  r  via bst_Node *)
      (*    regenerate x' *)
      ; ( 1
        , bindGenOpt (genSTF (fun x' => x' <= lo) (fun x' => allb [(x' <= hi)? ; is_bst lo x' l ; is_bst x' hi r])) (fun x' =>
          ret (Some (Node x' l r)))
        )
      
      (* recombine: Node x  l' r  via bst_Node *)
      (*    regenerate l' *)
      ; ( 1
        , bindGenOpt (genSTF (fun l' => bst lo x l') (fun l' => allb [])) (fun l' =>
          ret (Some (Node x l' r))) 
        )
      
      (* recombine: Node x  l  r' via bst_Node *)
      (*    regenerate r' *)
      ; ( 1
        , bindGenOpt (genSTF (fun r' => bst x hi r') (fun r' => allb [])) (fun r' =>
          ret (Some (Node x l r')))
        )

      (* -------------------------------------------------------------------- *)
      (* mutate child *)

      (* mutate child: l *)
      ; ( size l
        , mut_bst lo x l
        )

      (* mutate child: r *)
      ; ( size r
        , mut_bst x hi r
        )
    ]
  end.
  
  match t return G (option Tree) with
  | Leaf => mut_here 
  | Node x l r =>
    backtrack
      [ (* here *)
        ( 1 , mut_here )
      ; (* x *)
        ( 1
        (* specialized *)
        (* , bindGenOpt (genBetween (maxNode lo l) (minNode hi r)) (fun x' => *)
        (* generalized *)
        , bindGenOpt
            (backtrack [
              ( 1
              , bindGenOpt (genST (fun x => lo <= x)) (fun x' =>
                  if
                    (andb ((x' <= hi)?)
                    (andb (is_bst lo x' l)
                          (is_bst x' hi r)))
                  then ret (Some x)
                  else ret None)
              )
            ])
            (fun x' => ret (Some (Node x' l r)))
        )
      ; (* l *)
        ( mut_bst_branch_weighting (size l)
        , bindGenOpt (mut_bst lo x l) (fun l' => 
          ret (Some (Node x l' r)))
        )
      ; (* r *)
        ( mut_bst_branch_weighting (size r)
        , bindGenOpt (mut_bst x hi r) (fun r' => 
          ret (Some (Node x l r')))
        )
      ]
  end.    

Definition mut_preserves_bst :=
  forAll (arbitrary: G nat) (fun hi =>
  forAllMaybe (genST (fun lo => lo <= hi)) (fun lo =>
  forAllMaybe (@arbitraryST _ (fun t => bst lo hi t) _) (fun t =>
  forAllMaybe (mut_bst lo hi t) (fun t' =>
  ret (is_bst lo hi t')
  )))).

QuickChick mut_preserves_bst.

Sample (mut_bst 0 100 (Node 50 (Node 25 Leaf Leaf) (Node 75 Leaf Leaf))).