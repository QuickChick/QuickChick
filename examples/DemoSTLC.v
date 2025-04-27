Inductive typ : Set :=
| TNat
| TArrow (t1 t2 : typ)
.

Inductive term : Set :=
| Var (x : nat)
| Abs (x : nat) (t : typ) (e : term)
| App (e1 e2 : term)
| Const (n : nat)
.

Inductive value : term -> Prop :=
| VAbs : forall x t e, value (Abs x t e)
| VConst : forall n, value (Const n)
.

From QuickChick Require Import QuickChick.

Require Import Init Arith Logic Bool List.
Import ListNotations. 

Fixpoint eq_nat (x y : nat) : bool :=
  match x, y with
  | 0,0 => true
  | S x, S y => eq_nat x y
  | _, _ => false
  end.

Fixpoint mem (x : nat) (l : list nat) :=
  match l with
  | nil => false
  | (cons y l) => if eq_nat x y then true else mem x l
  end.

Definition is_free_in (x : nat) (e : term) : bool := 
  let fix aux (e : term) (env : list nat) : bool :=
    match e with
    | Var y => eq_nat x y
    | Abs y t body => if eq_nat x y then false else aux body (cons y env)
    | App fe xe => aux fe env || aux xe env  
    | Const _ => false
    end in
  aux e nil.

Definition free_vars (e : term) : list nat :=
  let fix aux (e : term) (env : list nat) : list nat :=
    match e with
    | Var y => if mem y env then nil else cons y nil
    | Abs y t body => aux body (cons y env)
    | App fe xe => aux fe env ++ aux xe env
    | Const _ => nil
    end in
  aux e nil.

Definition new_var (l : list nat) : nat := S (list_max l).

Fixpoint subst (x : nat) (v e : term) : term :=
  match e with
  | Var y => if eq_nat x y then v else Var y
  | Abs y t body => if eq_nat x y then Abs y t body else
                    if is_free_in y v then
                      let y' := new_var (y :: free_vars v) in
                      Abs y' t (subst y (Var y') body)
                    else Abs y t (subst x v body)
  | App fe xe => App (subst x v fe) (subst x v xe)
  | Const n => Const n
  end.

Inductive bigstep : term -> term -> Prop :=
| big_abs : forall x t e, bigstep (Abs x t e) (Abs x t e)
| big_app : forall e1 e2 x t body v v',
  bigstep e1 (Abs x t body) ->
  bigstep e2 v ->
  bigstep (subst x v body) v' ->
  bigstep (App e1 e2) v'
| big_const : forall n, bigstep (Const n) (Const n)
.

Inductive env : Set :=
| enil : env
| econs : nat -> typ -> env -> env
.

Inductive bind_typ : env -> nat -> typ -> Prop :=
| bind_here : forall env v t, bind_typ (econs v t env) v t 
| bind_later : forall env v t v' t', v <> v' -> bind_typ env v t -> bind_typ (econs v' t' env) v t 
.

Inductive typing : env -> term -> typ -> Prop :=
| typ_var : forall x ty g, bind_typ g x ty ->
                         typing g (Var x) ty
| typ_abs : forall x t body tbody g, typing (econs x t g) body tbody ->
                                   typing g (Abs x t body) (TArrow t tbody)
| typ_app : forall fe xe tfrom tto g, typing g fe (TArrow tfrom tto) ->
                                    typing g xe tfrom ->
                                    typing g (App fe xe) tto
| typ_const : forall n g, typing g (Const n) TNat
.


Instance DecEq_typ : Dec_Eq typ. dec_eq. Defined.
Instance DeqEq_term : Dec_Eq term. dec_eq. Defined.
Derive Show for typ.
Derive Show for term.
Derive Show for env.

Theorem preservation : forall g e ty e', typing g e ty -> bigstep e e' -> typing g e' ty.
Proof.
QuickChickDebug Debug On.  
schedules.
valid_schedules.
quickchick.





(*
Derive Inductive Schedule typing 1 2 derive "Gen" opt "true". Derive Density typing 1 2 derive "Gen". Derive Valid Schedules bind_typ 1 consnum 0 derive "Gen". Locate sized. Check @quickCheck.*)
