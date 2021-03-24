From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.
Open Scope qc_scope.
From Coq Require Import Init.Nat.
Open Scope nat_scope.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

Inductive term :=
| Var : nat -> term
| Abs : nat ->  term -> term
| App : term -> term -> term.
Derive Show for term.
Derive Sized for term.
Derive Arbitrary for term.

Sample (arbitrary : G term).

Inductive elem : nat -> list nat -> Prop :=
| ElemMatch : forall n1 n2 lst,
    n1 = n2 -> elem n1 (n2 :: lst)
| ElemRecur : forall n1 n2 rst,
    elem n1 rst ->
    elem n1 (n2 :: rst).
(* This fails *)
Derive (DecOpt) for (elem n l).
(* Derive ArbitrarySizedSuchThat for (fun l => elem n l). *)
Derive ArbitrarySizedSuchThat for (fun n => elem n l).
Sample (@arbitrarySizeST _ (fun n => elem n [1;2;3;4;5;6;7]) _ 20).


Inductive closedunder : list nat -> term -> Prop :=
| ClosedVar : forall n ctxt,
    elem n ctxt -> closedunder ctxt (Var n)
| ClosedAbs : forall n body ctxt,
    closedunder (n :: ctxt) body ->
    closedunder ctxt (Abs n body)
| ClosedApp : forall t1 t2 ctxt,
    closedunder ctxt t1 ->
    closedunder ctxt t2 ->
    closedunder ctxt (App t1 t2).
Derive DecOpt for (closedunder lst t).
Derive ArbitrarySizedSuchThat for (fun t => closedunder l t).

Inductive closed : term -> Prop :=
| Closed : forall t, closedunder [] t -> closed t.
Derive DecOpt for (closed t).
Derive ArbitrarySizedSuchThat for (fun t => closed t).

Sample (@arbitrarySizeST _ (fun t => closed t) _ 10).
