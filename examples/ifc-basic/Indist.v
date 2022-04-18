From QuickChick Require Import QuickChick.
Require Import ZArith.
Require Import List.

From QuickChick.ifcbasic Require Import Machine.

(* Manual, handwritten indist instances *)

Fixpoint forallb2 {A : Type} (f : A -> A -> bool) (l1 l2 :list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | cons h1 t1, cons h2 t2 => f h1 h2 && forallb2 f t1 t2
    | _, _ => false
  end.

(* Indistinguishability type class *)
Class Indist (A : Type) : Type :=
{
  indist : A -> A -> bool
}.

Instance indist_atom : Indist Atom :=
{|
  indist a1 a2 :=
    let '(x1@l1) := a1 in
    let '(x2@l2) := a2 in
    match l1, l2 with
      | L, L => Z.eqb x1 x2
      | H, H => true
      | _, _ => false
    end
|}.

Instance indist_mem : Indist Mem :=
{|
  indist m1 m2 := forallb2 indist m1 m2
|}.

Fixpoint cropTop (s:Stack) : Stack :=
  match s with
    | Mty        => Mty
    | x::s'      => cropTop s'
    | (x@H:::s') => cropTop s'
    | (_@L:::_)  => s
  end.

(* Assumes stacks have been cropTopped! *)
Instance indist_stack : Indist Stack :=
{|
  indist s1 s2 :=
    let fix aux s1 s2 :=
        match s1, s2 with
          | a1::s1', a2::s2' => indist a1 a2 && aux s1' s2'
          | a1:::s1', a2:::s2' => indist a1 a2 && aux s1' s2'
          | Mty, Mty => true
          | _, _ => false
        end
    in aux s1 s2
|}.

Instance indist_state : Indist State :=
{|
  indist st1 st2 :=
    let '(St imem1 mem1 stk1 pc1) := st1 in
    let '(St imem2 mem2 stk2 pc2) := st2 in
    if negb (indist mem1 mem2) then (* trace "Memory" *) false
    else if negb (indist pc1 pc2) then (* trace "PC" *) false
    else let (stk1',stk2') :=
           match pc1 with
             | _ @ H => (cropTop stk1, cropTop stk2)
             | _ => (stk1, stk2)
           end in
    if negb (indist stk1' stk2') then (* trace "Stack" *) false
    else true
|}.

(* Inductive versions *)

Inductive IndistAtom : Atom -> Atom -> Prop :=
| IAtom_Lo : forall x, IndistAtom (x@L) (x@L)
| IAtom_Hi : forall x y, IndistAtom (x@H) (y@H).

Derive DecOpt for (IndistAtom a1 a2).

Inductive IndistMem : Mem -> Mem -> Prop :=
| IMem_Nil  : IndistMem nil nil
| IMem_Cons : forall a1 a2 m1 m2,
    IndistAtom a1 a2 -> IndistMem  m1 m2 ->
    IndistMem (cons a1 m1) (cons a2 m2).

Derive DecOpt for (IndistMem m1 m2).

Inductive IndistStack : Stack -> Stack -> Prop :=
| IStack_Mty  : IndistStack Mty Mty
| IStack_Cons : forall a1 a2 s1 s2,
    IndistAtom a1 a2 -> IndistStack s1 s2 ->
    IndistStack (Cons a1 s1) (Cons a2 s2)
| IStack_RetCons : forall a1 a2 s1 s2,
    IndistAtom a1 a2 -> IndistStack s1 s2 ->
    IndistStack (RetCons a1 s1) (RetCons a2 s2).

Derive DecOpt for (IndistStack s1 s2).

Instance Label_DecEq (l1 l2 : Label) : Dec (l1 = l2).
Proof. dec_eq. Defined.

Inductive IndistState : State -> State -> Prop :=
| IState_Low : forall im1 im2 m1 m2 s1 s2 pc1 pc2,
    IndistAtom pc1 pc2 ->
    IndistMem m1 m2 ->
    pc_lab pc1 = L ->
    IndistStack s1 s2 ->
    IndistState (St im1 m1 s1 pc1) (St im2 m2 s2 pc2)
| IState_High : forall im1 im2 m1 m2 s1 s2 pc1 pc2,
    IndistAtom pc1 pc2 ->
    IndistMem m1 m2 ->
    pc_lab pc1 = H ->
    IndistStack (cropTop s1) (cropTop s2) ->
    IndistState (St im1 m1 s1 pc1) (St im2 m2 s2 pc2).

Derive DecOpt for (IndistState s1 s2).

