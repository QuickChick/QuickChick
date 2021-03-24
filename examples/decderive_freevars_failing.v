From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.
Open Scope qc_scope.
From Coq Require Import Init.Nat.
Open Scope nat_scope.
From Coq Require Import Lists.List.
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
(* Derive (DecOpt) for elem. *)

Search Dec.

Instance elemdec (n : nat) (lst : list nat) : Dec (elem n lst).
Proof.
  induction lst;
    constructor;
    unfold ssrbool.decidable.
  - right. unfold not. intros. inversion H.
  - destruct (@dec (n = a)).
    constructor.
    apply dec_eq.
    + left. apply ElemMatch. auto.
    + destruct (@dec (elem n lst)). auto.
      * left. apply ElemRecur. auto.
      * right. unfold not. intros. inversion H; congruence.
Qed.

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
(* Also doesn't work *)
(* Derive DecOpt for closedunder. *)

Instance decclosed lst t : Dec (closedunder lst t).
Proof.
  generalize dependent lst.
  induction t;
    intros;
    constructor;
    unfold ssrbool.decidable.
  - destruct (@dec (elem n lst)). apply elemdec.
    + left. apply ClosedVar. auto.
    + right. unfold not. intros. inversion H. congruence.
  - destruct (@dec (closedunder (n :: lst) t)).
    apply IHt.
    + left. apply ClosedAbs. auto.
    + right. unfold not. intros. inversion H. congruence.
  - destruct (@dec (closedunder lst t1));
      destruct (@dec (closedunder lst t2)); auto;
        try (right; unfold not; intros; inversion H; congruence).
    + left. apply ClosedApp; auto.
Qed.
