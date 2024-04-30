From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import Arith List String Lia.
Require Import Program Relations Wellfounded Lexicographic_Product.
From QuickChick Require Import QuickChick.

Import ListNotations.

QuickChickDebug Debug On.

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof. do 2 decide equality. Defined.



Inductive term : Type :=
| Const : nat -> term
| Id : nat -> term
| App : term -> term -> term
| Abs : term -> term.

#[global] Instance dec_term (t1 t2 : term) : Dec (t1 = t2).
Proof. dec_eq. Defined.

(* Terms that do not have applications *)
Inductive app_free : term -> Prop :=
| ConsNoApp : forall n, app_free (Const n)
| IdNoApp : forall x, app_free (Id x)
| AbsNoApp : forall (t : term),
               app_free t -> app_free (Abs t).

(* Number of applications in a term *)
Fixpoint app_no (t : term) : nat :=
  match t with
    | Const _ | Id _ => 0
    | Abs t => app_no t
    | App t1 t2 => 1 + (app_no t1 + app_no t2)
  end.

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Inductive typing' (e : env) : term -> type -> Prop :=
| TId' :
    forall x tau,
      bind e x tau ->
      typing' e (Id x) tau
| TConst' :
    forall n,
      typing' e (Const n) N
| TAbs' :
    forall t tau1 tau2,
      typing' (tau1 :: e) t tau2 ->
      typing' e (Abs t) (Arrow tau1 tau2)
| TApp' :
    forall t1 t2 tau1 tau2,
      typing' e t1 (Arrow tau1 tau2) ->
      typing' e t2 tau1 ->
      typing' e (App t1 t2) tau2.



Derive Arbitrary for type.
Derive Arbitrary for term.
#[global]
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
(*Derive ArbitrarySizedSuchThat for (fun t => typing' env t tau).*)

Inductive value : term -> Prop :=
| ValueConst : forall n, value (Const n)
| ValueAbs : forall t, value (Abs t)
.

Derive DecOpt for (value t).

Inductive subst (y : nat) (t1 : term) : term -> term -> Prop :=
| SubstId : subst y t1 (Id y) t1
| SubstIdDiff : forall x, x <> y -> subst y t1 (Id x) (Id x)
| SubstConst : forall n, subst y t1 (Const n) (Const n)
| SubstApp : forall t t' t'' t''',
    subst y t1 t t' ->
    subst y t1 t'' t''' ->
    subst y t1 (App t t'') (App t' t''')
| SubstAbs : forall t t',
    subst (S y) t1 t t' ->
    subst y t1 (Abs t) (Abs t').

Derive DecOpt for (subst y t1 t2 t2').
Derive DecOpt for (bind env x tau).

Search Enum.
Derive EnumSized for type.
Derive DecOpt for (typing' env e tau).

Inductive step : term -> term -> Prop :=
| StepApp1 : forall t1 t1' t2,
    step t1 t1' ->
    step (App t1 t2) (App t1' t2)
| StepApp2 : forall t1 t2 t2',
    value t1 ->
    step t2 t2' ->
    step (App t1 t2) (App t1 t2')
| StepAppAbs : forall t t' t2,
    value t2 ->
    subst 0 t2 t t' ->
    step (App (Abs t) t2) t'
.

(*Derive DecOpt for (step e e').*)
Derive GenSizedSuchThat for (fun e' => step e e').
Derive Show for type.
Derive Show for term.

Theorem preservation : forall e e' Gamma tau,
    typing' Gamma e tau ->
    step e e' ->
    typing' Gamma e' tau.
Proof.
 grab_dependencies. derive_and_quickchick. quickchick.
Admitted.

  
Open Scope string.

Fixpoint show_type (tau : type) :=
  match tau with
    | N => "Nat"
    | Arrow tau1 tau2 =>
      "(" ++ show_type tau1 ++ " -> " ++ show_type tau2 ++ ")"
  end.

#[global]
Instance showType : Show type := { show := show_type }.

Fixpoint show_term (t : term) :=
  match t with
    | Const n => show n
    | Id x => "Id" ++ show x
    | App t1 t2 => "(" ++ show_term t1 ++ " " ++ show_term t2 ++ ")"
    | Abs t => "λ.(" ++ show_term t ++ ")"
  end.

Close Scope string.

#[global]
Instance showTerm : Show term := { show := show_term }.
