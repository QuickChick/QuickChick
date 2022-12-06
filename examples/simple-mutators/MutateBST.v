From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

#[local] Instance GenNat : Gen nat :=
  {| arbitrary := choose (0, 10) |}.

#[local] Instance MutateNat : Mutate nat :=
  {| mutate n := choose (n - 1, n + 1) |}.
#[local] Instance FuzzyNat : Fuzzy nat :=
  {| fuzz n := choose (n - 1, n + 1) |}.
Derive (Sized) for nat.

(* -------------------------------------------------------------------------- *)
(* Impl.v *)
(* -------------------------------------------------------------------------- *)

Inductive Tree :=
| E 
| T : Tree -> nat -> nat -> Tree -> Tree.

Derive (Sized, Arbitrary, Fuzzy, Mutate, Show) for Tree.

Axiom fuel : nat. Extract Constant fuel => "100".

Fixpoint insert (k : nat) (v: nat) (t : Tree) :=
  match t with
  | E => T E k v E
  | T l k' v' r => 
  (*!          
  if k <? k' then T (insert k v l) k' v' r 
  else if k' <? k then T l k' v' (insert k v r) 
  else T l k' v r
  *)
  (*!! insert_1  *)
  (*!
  T E k v E
  *)
  (*!! insert_2 *)
(*! *)
  if k <? k' then T (insert k v l) k' v' r
  else T l k' v r 
 
  (*!! insert_3 *)
  (*!
  if k <? k' then T (insert k v l) k' v' r
  else if k' <? k then T l k' v' (insert k v r)
  else T l k' v' r
  *)
  end.

Fixpoint join (l: Tree) (r: Tree) :=
  match l, r with
  | E, _ => r
  | _, E => l
  | T l k v r, T l' k' v' r' =>
  T l k v (T (join r l') k' v' r')
  end
.
  

Fixpoint delete (k: nat) (t: Tree) :=
  match t with
  | E => E
  | T l k' v' r =>
  (*! *)
  if k <? k' then T (delete k l) k' v' r
  else if k' <? k then T l k' v' (delete k r)
  else join l r
  (*!! delete_4 *)
  (*!
  if k <? k' then delete k l
  else if k' <? k then delete k r
  else join l r
  *)
  (*!! delete_5 *)
  (*!
  if k' <? k then T (delete k l) k' v' r
  else if k <? k' then T l k' v' (delete k r)
  else join l r
  *)
  end.



Fixpoint below (k: nat) (t: Tree) :=
  match k, t with
  | _, E => E
  | k, T l k' v r =>
  if k <=? k' then below k l
  else T l k' v (below k r)
  end.

Fixpoint above (k: nat) (t: Tree) :=
  match k, t with
  | _, E => E
  | k, (T l k' v r) =>
  if k' <=? k then above k r
  else T (above k l) k' v r
  end.




Fixpoint union_ (l: Tree) (r: Tree) (f: nat) :=
  match f with
  | 0 => E
  | S f' =>
  match l, r with
  | E, _ => r
  | _, E => l
  (*! *)
  | (T l k v r), t =>
    T (union_ l (below k t) f') k v (union_ r (above k t) f')
  (*!! union_6 *)
  (*!
  | (T l k v r), (T l' k' v' r') =>
    T l k v (T (union_ r l' f') k' v' r')
  *)
  (*!! union_7 *)
  (*!   
  | (T l k v r), (T l' k' v' r') =>
    if k =? k' then T (union_ l l' f') k v (union_ r r' f')
    else if k <? k' then T l k v (T (union_ r l' f') k' v' r')
    else union_ (T l' k' v' r') (T l k v r) f'
  *)
  (*!! union_8 *)
  (*!
  | (T l k v r), (T l' k' v' r') =>
  if k =? k'  then T (union_ l l' f') k v (union_ r r' f')
  else if k <? k'   then T (union_ l (below k l') f') k v
              (union_ r (T (above k l') k' v' r') f')
    else union_ (T l' k' v' r') (T l k v r) f' 
  *)
  end
  end
.

Definition union (l: Tree) (r: Tree) :=
  union_ l r fuel.


Fixpoint find (k: nat) (t: Tree): option nat :=
  match k, t with
  | _, E => None
  | k, (T l k' v' r) =>
  if k <? k' then find k l
  else if k' <? k then find k r
  else Some v'
  end
.

Fixpoint size (t: Tree) :=
  match t with
  | E => 0
  | T l k v r => 1 + size l + size r
  end
.

(* -------------------------------------------------------------------------- *)
(* Spec.v *)
(* -------------------------------------------------------------------------- *)

Notation "A =?= B" := (option_eqb A B) (at level 100, right associativity).
Notation "A =~= B" := (list_eqb A B) (at level 100, right associativity).
  
  
Fixpoint keys (t: Tree): list nat :=
  match t with
  | E => nil
  | T l k v r => 
  let lk := keys l in
  let rk := keys r in
  [k] ++ lk ++ rk
  end.

  
Fixpoint all {A: Type} (f: A -> bool) (l: list A): bool :=
  match l with
  | nil => true
  | (x::xs) => 
    f x && all f xs
  end
  .
  

Local Open Scope nat_scope.

Definition Nat_gtb (n1 n2: nat) : bool :=
  negb (n1 <=? n2).

Fixpoint isBST (t: Tree): bool:=
  match t with
  | E => true
  | (T l k _ r) =>
  isBST l
    && isBST r
    && all (Nat_gtb k) (keys l)
    && all (Nat.ltb k) (keys r)
  end.
  
  
  
  
Fixpoint toList (t: Tree): list (nat * nat) :=
  match t with
  | E => nil
  | T l k v r =>
  toList l ++ [(k, v)] ++ toList r
  end.

(* -- Validity properties. *)

Definition prop_InsertValid (t: Tree) (k: nat) (v: nat) :=
  isBST t -=> Some(isBST (insert k v t)).

Definition prop_DeleteValid (t: Tree) (k: nat) :=
  isBST t -=> Some(isBST (delete k t)).


Definition prop_UnionValid (t1: Tree) (t2: Tree) :=
  (isBST t1 && isBST t2) -=> (isBST (union t1 t2)).

(* ---------- *)


(* -- Postcondition properties. *)

Definition prop_InsertPost (t: Tree) (k: nat) (k': nat) (v: nat) :=
  isBST t
  -=> (find k' (insert k v t) =?= if k =? k' then Some v else find k' t).

Definition prop_DeletePost (t: Tree) (k: nat) (k': nat) :=
  isBST t
  -=> (find k' (delete k t) =?= if k =? k' then None else find k' t).

Definition prop_UnionPost (t: Tree) (t': Tree) (k: nat) :=
  isBST t
  -=> 
  let lhs := find k (union t t') in
  let rhs := find k t in
  let rhs':= find k t' in
  ((lhs =?= rhs) || (lhs =?= rhs')) .

(* ---------- *)

(* -- Model-based properties. *)

Definition deleteKey  (k: nat) (l: list (nat * nat)): list (nat * nat) :=
  filter (fun x => negb (fst x =? k)) l.

Fixpoint L_insert (kv: nat * nat) (l: list (nat * nat)) : list (nat * nat) :=
  match l with
  | nil => [kv]
  | (k, v)::xs =>
  if fst kv =? k then (fst kv, snd kv)::xs
  else if fst kv <? k then (fst kv, snd kv)::l
  else (k, v)::(L_insert kv xs)
  end.


Fixpoint sorted (l: list (nat * nat)): bool :=
  match l with
  | nil => true
  | (k, v)::l' =>
  match l' with
  | nil => true
  | (k', v')::l'' =>
    (k <? k') && sorted l'
  end
  end.


Definition prop_InsertModel (t: Tree) (k: nat) (v: nat) :=
  isBST t
  -=> (toList (insert k v t) =~= L_insert (k, v) (deleteKey k (toList t))).


Definition prop_DeleteModel (t: Tree) (k: nat) :=
  isBST t
  -=> Some(toList (delete k t) =~= deleteKey k (toList t)).


Fixpoint L_sort (l: list (nat * nat)): list (nat * nat) :=
  match l with
  | nil => nil
  | (k, v)::l' =>
  L_insert (k, v) (L_sort l')
  end.

Definition L_find (k: nat) (l: list (nat * nat)): option nat :=
  match filter (fun x => fst x =? k) l with
  | nil => None
  | (k, v)::l' => Some v
  end.

Fixpoint L_unionBy (f: nat -> nat -> nat) (l1: list (nat * nat)) (l2: list (nat * nat)): list (nat * nat) :=
  match l1 with
  | nil => l2
  | (k, v)::l1' =>
  let l2' := deleteKey k l2 in
  let v' := match L_find k l2 with
        | None => v
        | Some v' => f v v'
        end
  in
  L_insert (k, v') (L_unionBy f l1' l2')
  end.


Definition prop_UnionModel (t: Tree) (t': Tree) :=
  (isBST t && isBST t')
  -=> (toList (union t t') =~= L_sort (L_unionBy (fun x y => x) (toList t) (toList t'))).


(* ---------- *)

Fixpoint tree_eqb (t: Tree) (t': Tree) : bool :=
  toList t =~= toList t'.

Notation "A =|= B" := (tree_eqb A B) (at level 100, right associativity).
(* -- Metamorphic properties. *)

Definition prop_InsertInsert (t: Tree) (k: nat) (k': nat) (v: nat) (v': nat) :=
  isBST t
  -=> (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t)).

Definition prop_InsertDelete (t: Tree) (k: nat) (k': nat) (v: nat) :=
  isBST t
  -=> (insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t)).

Definition prop_InsertUnion (t: Tree) (t': Tree) (k: nat) (v: nat) :=
  (isBST t && isBST t')
  -=> (insert k v (union t t') =|= union (insert k v t) t').

Definition prop_DeleteInsert (t: Tree) (k: nat) (k': nat) (v': nat) :=
  isBST t
  -=> 
  (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)).

Definition prop_DeleteDelete (t: Tree) (k: nat) (k': nat) :=
  isBST t
  -=> (delete k (delete k' t) =|= delete k' (delete k t)).

Definition prop_DeleteUnion (t: Tree) (t': Tree) (k: nat) :=
  (isBST t && isBST t')
  -=> Some(delete k (union t t')
  =|= union (delete k t) (delete k t')).

Definition prop_UnionDeleteInsert (t :Tree) (t': Tree) (k: nat) (v: nat) :=
  (isBST t && isBST t')
  -=> Some(union (delete k t) (insert k v t')
  =|= insert k v (union t t')).

Definition prop_UnionUnionIdem (t: Tree) :=
  isBST t
  -=> union t t =|= t.

Definition prop_UnionUnionAssoc (t1: Tree) (t2: Tree) (t3: Tree) :=
  (isBST t1 && isBST t2 && isBST t3)
  -=> (union (union t1 t2) t3 =|= union t1 (union t2 t3)).

(* ---------- *)

Definition sizeBST (t: Tree) : nat :=
  length (toList t).

(* -------------------------------------------------------------------------- *)
(* fuzzing *)
(* -------------------------------------------------------------------------- *)

ManualExtract Tree.
QuickChickDebug Debug On.

Definition make_fuzzer_fuzz {A} `{Gen A} `{Fuzzy A} `{Show A} prop (_ : unit) := 
  @fuzzLoop A arbitrary fuzz show prop.
  Check @fuzzLoop.
Definition make_fuzzer_mutate {A} `{Gen A} `{Mutate A} `{Show A} prop (_ : unit) := 
  @fuzzLoop A arbitrary mutate show prop.
Definition make_fuzzer_trivial prop (_ : unit) := 
  @fuzzLoop Tree arbitrary (fun _ => returnGen E) show prop.

(* fuzzing: isBST *)

Definition prop_isBST (t : Tree) := 
  if isBST t then Some true else None.

FuzzChick prop_isBST (make_fuzzer_fuzz prop_isBST tt).
(* FuzzChick prop_isBST (make_fuzzer_mutate prop_isBST tt). *)

(* fuzzing: prop_InsertValid *)
Definition prop_InsertValid' t := prop_InsertValid t 2 0.

(* FuzzChick prop_InsertValid' (make_fuzzer_fuzz prop_InsertValid' tt). *)

(* FuzzChick prop_InsertValid' (make_fuzzer_mutate prop_InsertValid' tt). *)

(* FuzzChick prop_InsertValid' (make_fuzzer_trivial prop_InsertValid' tt). *)
