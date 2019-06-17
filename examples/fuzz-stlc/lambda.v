Require Import Arith List String.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.

Import MonadNotation.
Import ListNotations.

Inductive type : Type :=
| Base  : type
| Fun   : type -> type -> type.

Notation "%" := Base.
Notation "x :-> y" := (Fun x y) (at level 50).

Derive (Arbitrary, Show, Fuzzy) for type.

Instance dec_eq_type (τ1 τ2 : type) : Dec (τ1 = τ2).
Proof. dec_eq. Defined.

Inductive term : Type :=
| Unit  : term
| Var   : nat -> term
| Lam   : type -> term -> term
| App   : term -> term -> term.

Notation "#" := Unit.

Derive (Arbitrary, Show, Fuzzy) for term.

Definition env := list type.

Inductive typing (Γ : env) : term -> type -> Prop :=
| TBase : typing Γ Unit Base
| TVar  : forall x τ, nth_error Γ x = Some τ -> typing Γ (Var x) τ
| TLam  : forall e τ1 τ2, typing (τ1 :: Γ) e τ2 -> typing Γ (Lam τ1 e) (τ1 :-> τ2)
| TApp  : forall e1 e2 τ1 τ2, typing Γ e1 (τ1 :-> τ2) ->
                              typing Γ e2 τ1 ->
                              typing Γ (App e1 e2) τ2.

Fixpoint typeOf (Γ : env) (e : term) : option type :=
  match e with
  | Unit => Some Base
  | Var x => nth_error Γ x
  | Lam τ e' => τ' <- typeOf (τ :: Γ) e';;
                Some (τ :-> τ')
  | App e1 e2 => τ12 <- typeOf Γ e1;;
                 τ1 <- typeOf Γ e2;;
                 match τ12 with
                 | τ1' :-> τ2 =>
                   if τ1 = τ1' ? then Some τ2
                   else None
                 | _ => None
                 end
  end.

Definition well_typed (e : term) : bool :=
  match typeOf [] e with
  | Some _ => true
  | _ => false
  end.

Fixpoint lift (n : nat) (e : term) : term :=
  match e with
  | Unit      => Unit
  | Var x     => Var (if x <? n then x else x+1)
  | Lam τ e'  => Lam τ (lift (n+1) e')
  | App e1 e2 => App (lift n e1) (lift n e2)
  end.

Fixpoint subst (n : nat) (s : term) (e : term) : term :=
  match e with
  | Unit  => Unit
  | Var x =>
    if x =? n then s
    else if x <? n then Var (x-1)
    else Var x
  | Lam τ e' => Lam τ (subst (n+1) (lift 0 s) e')
  | App e1 e2 => App (subst n s e1) (subst n s e2)
  end.

(* Parallel reduction *)
Fixpoint pstep (e : term) : term :=
  match e with
  | Unit  => Unit
  | Var x => Var x
  | Lam τ e'  => Lam τ (pstep e')
  | App e1 e2 => let e1' := pstep e1 in
                 let e2' := pstep e2 in
                 match e1' with
                 | Lam τ body => subst 0 e2' body
                 | _ => App e1' e2'
                 end
  end.

(* Generation *)

Fixpoint gen_type (n : nat) : G type :=
  match n with
  | O => ret Base
  | S n' => oneOf  [ ret Base
                   ; τ1 <- gen_type (n' - 1);;
                     τ2 <- gen_type n';;
                     ret (τ1 :-> τ2)
                   ]
  end.

Fixpoint gen_small_expr (Γ : env) (τ : type) : G term :=
  let vars : list term :=
      map (fun '(n, τ') => Var n)
          (filter (fun '(n, τ') => τ = τ'?)
                  (combine (seq 0 (List.length Γ)) Γ)) in
  let base := match τ with
              | Base => ret Unit
              | τ1 :-> τ2 => e' <- gen_small_expr (τ1 :: Γ) τ2;;
                             ret (Lam τ1 e')
              end  in
  oneOf_ base (base :: map ret vars).

Fixpoint gen_expr (n : nat) (Γ : env) (τ : type) : G term :=
  match n with
  | O    => gen_small_expr Γ τ
  | S n' =>
    let gLam := match τ with
                | τ1 :-> τ2 =>
                  [ e <- gen_expr n' (τ1 :: Γ) τ2 ;;
                    ret (Lam τ1 e) ]
                | _ => []
                end in
    let gApp :=
        τ1 <- gen_type (min n 5);;
        e1 <- gen_expr n' Γ (τ1 :-> τ);;
        e2 <- gen_expr n' Γ τ1;;
        ret (App e1 e2) in
    oneOf_ (gen_small_expr Γ τ)
           ([ gen_small_expr Γ τ] ++ gLam ++ [gApp])
  end.
           
(* Sample (gen_expr 3 [] (Base :-> Base)). *)
Definition prop_gen_wt :=
  forAll (gen_type 5) (fun τ =>
  forAll (gen_expr 6 [] τ) (fun e =>
  typeOf [] e = Some τ?)). 

QuickChick prop_gen_wt.

Definition preservation (e : term) :=
  match typeOf [] e with
  | Some τ =>
     checker (typeOf [] (pstep e) = Some τ?)
  | _ => checker tt
  end.

Definition prop_preservation :=
  forAll (gen_type 5) (fun τ =>
  forAll (gen_expr 6 [] τ) (fun e =>
  preservation e)).

QuickCheck prop_preservation.
