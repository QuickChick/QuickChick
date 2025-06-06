From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

Inductive type :=
| TBool : type
| TFun  : type -> type -> type.

Derive Show for type.
#[export] Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.

Inductive term :=
| Var   : nat -> term
| Bool  : bool -> term
| Abs   : type -> term -> term
| App   : term -> term -> term.

Derive Show for term.
#[export] Instance dec_expr (e1 e2 : term) : Dec (e1 = e2).
Proof. dec_eq. Defined.

Inductive Ctx := Empty | Bind (x : type) (c : Ctx).

Derive Show for Ctx.

Fixpoint lookup (Γ : Ctx) (n : nat) : option type :=
  match n, Γ with
  | 0   , Bind τ _  => Some τ
  | S n', Bind _ Γ' => lookup Γ' n'
  | _, _ => None
  end.

Definition shift  (d: Z) (ex: term) : term :=
    let fix go (c: Z) (e: term):=
        match e with 
        | Var n =>
            (*! *)
            if n <? Z.to_nat c then Var n
            else Var (Z.to_nat ((Z.of_nat n) + d))
            (*!! shift_var_none *)
            (*!
            Var n
            *)
            (*!! shift_var_all *)
            (*!             
            Var (Z.to_nat (Z.of_nat n + d))
            *)
            (*!! shift_var_leq *)
            (*!
            if (Z.leb (Z.of_nat n) c) then Var n
            else Var (Z.to_nat (Z.of_nat n + d)) 
            *)
        | Bool b => 
            Bool b
        | Abs t e =>
            (*! *)
            Abs t (go (1 + c)%Z e)
            (*!! shift_abs_no_incr *)
            (*!
            Abs t (go c e)
            *)
        | (App e1 e2) => 
            App (go c e1) (go c e2)
        end in
    go 0%Z ex.

Fixpoint subst  (n: nat) (s: term) (e: term) : term :=
    match n, s, e with 
    | n, s, (Var m) =>
        (*! *)
        if m =? n then s
        else Var m
        (*!! subst_var_all *)
        (*!
        s
        *)
        (*!! subst_var_none *)
        (*!
        Var m
        *)
    | _, _, (Bool b) => Bool b
    | n, s, (Abs t e) =>
        (*! *)
(*        Abs t (subst (n + 1) (shift 1 s) e)  *)
        (*!! subst_abs_no_shift *)
        Abs t (subst (n + 1) s e)
        (*!! subst_abs_no_incr *)
        (*!
        Abs t (subst n (shift 1 s) e)
        *)
    | n, s, (App e1 e2) => App (subst n s e1) (subst n s e2)
    end.

Definition substTop (s: term) (e: term) : term :=
    (*! *)
    shift (-1) (subst 0 (shift 1 s) e) 
    (*!! substTop_no_shift *)
    (*! 
    subst 0 s e
    *)
    (*!! substTop_no_shift_back *)
    (*!
    subst 0 (shift 1 s) e
    *)
.

Fixpoint pstep  (e: term) : option term :=
    match e with
    | Abs t e => 
        e' <- (pstep e) ;;
        Some (Abs t e')
    | App (Abs _ e1) e2 =>
        e1' <- pstep e1;;
        e2' <- pstep e2;;
        Some (substTop e2' e1')
    | App (Bool _) _ => None             
    | App e1 e2 =>
        e1' <- pstep e1;;
        e2' <- pstep e2;;
        Some (App e1' e2')
    | Var _ => Some e
    | Bool b => Some (Bool b)
    end.

Inductive bind : Ctx -> nat -> type -> Prop :=
| Now   : forall τ Γ, bind (Bind τ Γ) 0 τ
| Later : forall τ τ' Γ x ,
    bind Γ x τ -> bind (Bind τ' Γ) (S x) τ.

Inductive typing : Ctx -> term -> type -> Prop :=
| TyVar :
    forall Γ x τ,
      bind Γ x τ ->
      typing Γ (Var x) τ
| TyBool :
    forall Γ b,
      typing Γ (Bool b) TBool
| TyAbs :
    forall Γ e τ1 τ2,
      typing (Bind τ1 Γ) e τ2 ->
      typing Γ (Abs τ1 e) (TFun τ1 τ2)
| TyApp :
    forall Γ e1 e2 τ1 τ2,
      typing Γ e1 (TFun τ1 τ2) ->
      typing Γ e2 τ1 ->
      typing Γ (App e1 e2) τ2.

Theorem preservation : forall e τ e',
    typing Empty e τ -> pstep e = Some e' ->
    typing Empty e' τ.
Proof. quickchick.
  schedules. valid_schedules. 



























