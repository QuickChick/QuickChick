
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.
Inductive Typ :=
| TBool : Typ
| TFun  : Typ -> Typ -> Typ
.

#[export] Instance dec_type (t1 t2 : Typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.

Derive Show for Typ.

Inductive Expr :=
| Var   : nat -> Expr
| Bool  : bool -> Expr
| Abs   : Typ -> Expr -> Expr
| App   : Expr -> Expr -> Expr
.

Derive Show for Expr.

#[export] Instance dec_expr (e1 e2 : Expr) : Dec (e1 = e2). Proof. dec_eq. Defined.

Inductive Ctx := cnil | ccons (x : Typ) (c : Ctx).

Derive Show for Ctx.
(* Fixpoint typ_eqb (t1 t2: Typ) : bool :=
    match t1, t2 with
    | TBool, TBool => true
    | TBool, TFun _ _ => false
    | TFun _ _, TBool => false
    | TFun t1' t1'', TFun t2' t2'' => (typ_eqb t1'  t2') && (typ_eqb t1'' t2'')
    end.
  
Notation "A == B" := (typ_eqb A B) (at level 100, right associativity). *)

Definition nth_error :=
fix nth_error (l : Ctx) (n : nat) {struct n} : option Typ :=
  match n with
  | 0 => match l with
         | cnil => None
         | ccons x _ => Some x
         end
  | S n0 => match l with
            | cnil => None
            | ccons _ l0 => nth_error l0 n0
            end
  end.


Fixpoint getTyp (ctx: Ctx) (e: Expr) : option Typ :=
    match e with
    | (Var n) =>
        (* if (0 <=? n) && ((List.length ctx) <? n) then (List.nth_error ctx (n)) *)
        nth_error ctx n
        (* else  None *)
    | (Bool _) => 
        Some TBool
    | (Abs t e) =>
        t' <- getTyp (ccons t ctx) e ;;
        Some (TFun t t')
    | (App e1 e2) => 
        t1' <- getTyp ctx e1 ;;
        match t1' with
        | TFun t11 t12 =>
            t2 <- getTyp ctx e2 ;;
            if (t11 = t2)? then Some t12 else None
        | _ => None
        end
    end
.

Definition typeCheck (ctx: Ctx) (e: Expr) (t: Typ) : bool :=
    match getTyp ctx e with
    | Some t' => (t = t')?
    | None => false
    end
.



Definition shift  (d: Z) (ex: Expr) : Expr :=
    let fix go (c: Z) (e: Expr):=
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
    go 0%Z ex
.



Fixpoint subst  (n: nat) (s: Expr) (e: Expr) : Expr :=
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
        Abs t (subst (n + 1) (shift 1 s) e)
        (*!! subst_abs_no_shift *)
        (*!
        Abs t (subst (n + 1) s e)
        *)
        (*!! subst_abs_no_incr *)
        (*!
        Abs t (subst n (shift 1 s) e)
        *)
    | n, s, (App e1 e2) => App (subst n s e1) (subst n s e2)
    end.



Definition substTop (s: Expr) (e: Expr) : Expr :=
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

Definition fromMaybe {A} (a: A) (a' : option A) : A :=
    match a' with
    | Some value => value
    | None => a
    end.

Fixpoint pstep  (e: Expr) : option Expr :=
    match e with
    | (Abs t e) => 
        e' <- (pstep e) ;;
        Some (Abs t e')
    | (App (Abs _ e1) e2) =>
        let e1' := fromMaybe e1 (pstep e1) in
        let e2' := fromMaybe e2 (pstep e2) in
            Some (substTop e2' e1')
    | (App e1 e2) =>
        match pstep e1, pstep e2 with
        | None, None => None
        | me1, me2 =>
            let e1' := fromMaybe e1 me1 in
            let e2' := fromMaybe e2 me2 in
                Some (App e1' e2')
        end
    | _ => None
    end.

Inductive bind : Ctx -> nat -> Typ -> Prop :=
| BindNow   : forall tau env, bind (ccons tau env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (ccons tau' env) (S x) tau.
Inductive typing (G : Ctx) : Expr -> Typ -> Prop :=
| TyVar :
    forall x T,
      bind G x T ->
      typing G (Var x) T
| TyBool :
    forall b,
      typing G (Bool b) TBool
| TyAbs :
    forall e T1 T2,
      typing (ccons T1 G) e T2 ->
      typing G (Abs T1 e) (TFun T1 T2)
| TyApp :
    forall e1 e2 T1 T2,
      typing G e1 (TFun T1 T2) ->
      typing G e2 T1 ->
      typing G (App e1 e2) T2.

#[export] Instance dec_eq_option {A} `{forall (a b : A), Dec (a = b)} (a b : option A) : Dec (a = b). Proof. dec_eq. Defined.

Compute (Some (Var 0) = Some (Var 0) ?? 1).

Definition eq_gen_iio := let funn := (fun (size' : Coq.Init.Datatypes.nat) (init_size : Coq.Init.Datatypes.nat) (A : Type) (v_x357_ : A) =>
   @QuickChick.Generators.backtrack _
     (@Coq.Init.Datatypes.cons _
        (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
           (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v_x357_))))
        (@Coq.Init.Datatypes.nil _))) in
                         fun size : Coq.Init.Datatypes.nat => @funn size size.

  
  
Theorem preservation : forall g e t e', typing g e t -> pstep e = Some e' -> typing g e' t.
Proof. schedules. valid_schedules. quickchick.  
