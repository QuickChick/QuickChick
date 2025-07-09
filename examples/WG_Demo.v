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

Inductive sorted_le : list nat -> Prop :=
| sorted_nil :
    sorted_le []
| sorted_singleton :
    forall x,
      sorted_le [x]
| sorted_cons :
    forall x y l,
      x <= y ->
      sorted_le (y :: l) ->
      sorted_le (x :: y :: l).

Derive Inductive Schedule sorted_le 0 derive "Gen" opt "true".

Sample (GenSizedSuchThat_sorted_le_O 5). Check true.

Inductive term :=
| Var   : nat -> term
| Bool  : bool -> term
| Abs   : type -> term -> term
| App   : term -> term -> term.

Derive Show for term.
#[export] Instance dec_expr (e1 e2 : term) : Dec (e1 = e2).
Proof. dec_eq. Defined.

(*Inductive Ctx A := Empty | Bind  (c : Ctx).

Derive Show for Ctx.*)

(*Inductive list (A : Type) :=
| nil : list A
| cons : forall (a : A) (l : list A), list A.*)

Fixpoint lookup (Γ : list type) (n : nat) : option type :=
  match n, Γ with
  | 0   , @cons _ τ _  => Some τ
  | S n', @cons _ _ Γ' => lookup Γ' n'
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
            (*! *)
           (* if (Z.leb (Z.of_nat n) c) then Var n
            else Var (Z.to_nat (Z.of_nat n + d)) *)
          (*  *)
        | Bool b => 
            Bool b
        | Abs t e =>
            (*! *)
            Abs t (go (1 + c)%Z e)
            (*!! shift_abs_no_incr *)
            (*! *)
           (* Abs t (go c e)*)
          (*  *)
        | (App e1 e2) => 
            App (go c e1) (go c e2)
        end in
    go 0%Z ex.

Import Lia.

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
        Abs t (subst (n + 1) (shift 1 s) e)  
        (*!! subst_abs_no_shift *)
        (*Abs t (subst (n + 1) s e)*)
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


Derive GenSized for type.
Derive GenSized for term.

(*Theorem shift_unshift : forall s n, shift (-n) (shift n s) = s.
Proof.  Locate opp.

  quickchick.*)

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

Inductive bigstep : term -> term -> Prop :=
| bs_Abs t e e' : bigstep e e' -> bigstep (Abs t e) (Abs t e')
| bs_AppAbs t e1 e2 e1' e2' es :
  bigstep e1 e1' ->
  bigstep e2 e2' ->
  substTop e2' e1' = es ->
  bigstep (App (Abs t e1) e2) es
| bs_AppApp a1 a2 a' e e' :
  bigstep (App a1 a2) a' ->
  bigstep e e' ->
  bigstep (App (App a1 a2) e) (App a' e')
| bs_AppVar v e e' :
  bigstep e e' ->
  bigstep (App (Var v) e) (App (Var v) e')
| bs_Var v : bigstep (Var v) (Var v)
| bs_Bool b : bigstep (Bool b) (Bool b)
.

Inductive bind {A : Type} : list A -> nat -> A -> Prop :=
| Now   : forall τ Γ, bind (@cons _ τ Γ) 0 τ
| Later : forall τ τ' Γ x ,
    bind Γ x τ -> bind (@cons _ τ' Γ) (S x) τ.
QuickChickDebug Debug On.

Derive GenSized for list.
Derive GenSized for type.
(*Derive Inductive Schedule bind 1 2 derive "Gen" opt "true".*)

Inductive typing : list type -> term -> type -> Prop :=
| TyVar :
    forall Γ x τ,
      bind Γ x τ ->
      typing Γ (Var x) τ
| TyBool :
    forall Γ b,
      typing Γ (Bool b) TBool
| TyAbs :
    forall Γ e τ1 τ2,
      typing (cons τ1 Γ) e τ2 ->
      typing Γ (Abs τ1 e) (TFun τ1 τ2)
| TyApp :
    forall Γ e1 e2 τ1 τ2,
      typing Γ e1 (TFun τ1 τ2) ->
      typing Γ e2 τ1 ->
      typing Γ (App e1 e2) τ2.

#[export] Instance Dec_Eq_type : Dec_Eq type. dec_eq. Defined.

Derive Valid Schedules typing 2 consnum 3 derive "Check".

Derive Inductive Schedule typing derive "Check" opt "true".

Inductive isSome A : option A -> Prop :=
| isSomeSome a : isSome A (Some a).

Derive Inductive Schedule isSome 1 derive "Gen" opt "true".

Theorem checker_backtrack_one : forall p, checker_backtrack [p] = p tt.
Proof. intros. unfold checker_backtrack. destruct (p tt); auto. destruct b; auto. Qed.

Derive GenSized for option.
Derive GenSized for type.
Derive GenSized for term.
#[export] Instance Dec_Eq_option A `{Dec_Eq A} : Dec_Eq (option A).
Proof. dec_eq. Defined.

#[export] Instance Dec_Eq_term : Dec_Eq term.
Proof. dec_eq. Defined.

(*#[export] Instance Dec_eq_Dec_Eq A : (forall (x y : A), Dec (x = y)) -> Dec_Eq A.
Proof. intros. dec_eq. Defined.*)

Theorem preservation : forall g e τ e',
    typing g e τ -> pstep e = Some e' ->
    typing g e' τ.
Proof. QuickChickDebug Debug Off. valid_schedules. quickchick_idx 0. quickchick_idx 1. try_all_quickchick_schedules. quickchick_idx 40.
                                                                  
  schedules. valid_schedules. Abort.


Theorem preservation' : forall g e τ e',
    typing g e τ -> bigstep e e' ->
    typing g e' τ. valid_schedules. quickchick_idx 0.
   
                   
                   QuickChick (sized (fun size : nat =>
                                 let double {A : Set} (g : nat -> G (option A)) := bindGen (g size) (fun r =>  match r with | None => g (2 * (size + 1)) | _ => returnGen r end) in 
forAllMaybeChecker (double (fun size => GenSizedSuchThat_typing_OOO size) )
  (fun '(g, e, τ) =>
   forAllMaybeChecker ( double (fun size => GenSizedSuchThat_bigstep_IO ( size)  e))
     (fun e' : term =>
      match DecOpt_typing_III (2 * (size + 1)) g e' τ with
      | Some true => checker (Some true)
      | Some false => checker (Some false)
      | None => checker false
      end))) ).

Derive Density typing 1 derive "Gen".                   
                   
    
                   
