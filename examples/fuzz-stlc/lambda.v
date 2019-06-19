Require Import Arith List String.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.

Import MonadNotation.
Import ListNotations.

(** Types *)

Inductive Typ :=
| Base  : Typ
| Fun   : Typ -> Typ -> Typ.

Notation "%" := Base.
Notation "x :-> y" := (Fun x y) (at level 50).

Derive (Arbitrary, Fuzzy) for Typ.

Instance dec_eq_Typ (τ1 τ2 : Typ) : Dec (τ1 = τ2).
Proof. dec_eq. Defined.

(** Terms *)

Inductive Term :=
| Unit  : Term
| Var   : nat -> Term
| Lam   : Typ -> Term -> Term
| App   : Term -> Term -> Term.

Notation "#" := Unit.

Derive (Arbitrary, Fuzzy) for Term.

(** Printing *)

Inductive Prec := POuter | PApp | PInner.

Definition ltp (p1 p2 : Prec) :=
  match p1, p2 with
  | POuter, PApp => true
  | POuter, PInner => true
  | PApp  , PInner => true
  | _, _ => false
  end.

Definition parens outer inner s := if ltp inner outer then "(" ++ s ++ ")" else s.

Fixpoint showTyp' prec (τ : Typ) :=
  match τ with
  | Base => "()"
  | Fun τ1 τ2 => parens prec PApp (showTyp' PInner τ1 ++ "->" ++ showTyp' PApp τ2)
  end.

Instance show_Typ : Show Typ :=
  { show := showTyp' POuter }.

Fixpoint showExpr' prec (e : Term) :=
  match e with
  | Unit => "#"
  | Var x => show x
  | Lam τ e' => parens prec POuter ("λ" ++ show τ ++ ". " ++ showExpr' POuter e')
  | App e1 e2 => parens prec PApp (showExpr' PApp e1 ++ " " ++ showExpr' PInner e2)
  end.

Instance show_Term : Show Term :=
  { show := showExpr' POuter }.

(** Mutants *)

Inductive Mutant :=
| NoMutant
| SubstNoLift
| SubstNoIncr
| SubstNoDecr
| LiftAllVar
| LiftLamNoIncr
| LiftLamNoLift.

Definition all_mutants :=
  [ NoMutant
  ; SubstNoLift
  ; SubstNoIncr
  ; SubstNoDecr
  ; LiftAllVar
  ; LiftLamNoIncr
  ; LiftLamNoLift
  ].

Derive Show for Mutant.

Instance dec_eq_Mutant (m1 m2 : Mutant) : Dec (m1 = m2).
Proof. dec_eq. Defined.

Fixpoint mut {A} (c : Mutant) (x : A)
                 (my : list (Mutant * A)) : A :=
  match my with
  | [] => x
  | (m,y) :: my' => if c = m? then y else mut c x my'
  end.

(** Typing *)

Definition env := list Typ.

Inductive typing (Γ : env) : Term -> Typ -> Prop :=
| TBase : typing Γ Unit Base
| TVar  : forall x τ, nth_error Γ x = Some τ -> typing Γ (Var x) τ
| TLam  : forall e τ1 τ2, typing (τ1 :: Γ) e τ2 -> typing Γ (Lam τ1 e) (τ1 :-> τ2)
| TApp  : forall e1 e2 τ1 τ2, typing Γ e1 (τ1 :-> τ2) ->
                              typing Γ e2 τ1 ->
                              typing Γ (App e1 e2) τ2.

Fixpoint typeOf (Γ : env) (e : Term) : option Typ :=
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

Definition well_typed (e : Term) : bool :=
  match typeOf [] e with
  | Some _ => true
  | _ => false
  end.

Fixpoint lift (c : Mutant) (n : nat) (e : Term) : Term :=
  match e with
  | Unit      => Unit
  | Var x     => mut c (Var (if x <? n then x else x+1))
                       [(LiftAllVar, Var (x+1))]
  | Lam τ e'  => mut c (Lam τ (lift c (n+1) e'))
                       [ (LiftLamNoIncr, Lam τ (lift c n e'))
                       ; (LiftLamNoLift, Lam τ e') ]
  | App e1 e2 => App (lift c n e1) (lift c n e2)
  end.

Fixpoint subst (c : Mutant) (n : nat) (s : Term) (e : Term) : Term :=
  match e with
  | Unit  => Unit
  | Var x =>
    if x =? n then s
    else if n <? x then mut c (Var (x-1))
                              [ (SubstNoDecr, Var x) ]
    else Var x
  | Lam τ e' => mut c (Lam τ (subst c (n+1) (lift c 0 s) e'))
                      [ (SubstNoIncr, Lam τ (subst c n (lift c 0 s) e'))
                      ; (SubstNoLift, Lam τ (subst c (n+1) s e')) ]
  | App e1 e2 => App (subst c n s e1) (subst c n s e2)
  end.

(* Parallel reduction *)
Fixpoint pstep (c : Mutant) (e : Term) : Term :=
  match e with
  | Unit  => Unit
  | Var x => Var x
  | Lam τ e'  => Lam τ (pstep c e')
  | App e1 e2 => let e1' := pstep c e1 in
                 let e2' := pstep c e2 in
                 match e1' with
                 | Lam τ body => subst c 0 e2' body
                 | _ => App e1' e2'
                 end
  end.

(* Generation *)

Fixpoint gen_Typ (n : nat) : G Typ :=
  match n with
  | O => ret Base
  | S n' => oneOf  [ ret Base
                   ; τ1 <- gen_Typ (n' - 1);;
                     τ2 <- gen_Typ n';;
                     ret (τ1 :-> τ2)
                   ]
  end.

Fixpoint gen_small_expr (Γ : env) (τ : Typ) : G Term :=
  let vars : list Term :=
      map (fun '(n, τ') => Var n)
          (filter (fun '(n, τ') => τ = τ'?)
                  (combine (seq 0 (List.length Γ)) Γ)) in
  let base := match τ with
              | Base => ret Unit
              | τ1 :-> τ2 => e' <- gen_small_expr (τ1 :: Γ) τ2;;
                             ret (Lam τ1 e')
              end  in
  oneOf_ base (base :: map ret vars).

Fixpoint gen_expr (n : nat) (Γ : env) (τ : Typ) : G Term :=
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
        τ1 <- gen_Typ (min n 5);;
        e1 <- gen_expr n' Γ (τ1 :-> τ);;
        e2 <- gen_expr n' Γ τ1;;
        ret (App e1 e2) in
    oneOf_ (gen_small_expr Γ τ)
           ([ gen_small_expr Γ τ] ++ gLam ++ [gApp])
  end.

Fixpoint shrink_expr (τ : Typ) (t : Term) : list Term :=
  List.filter (fun t' => typeOf [] t' = Some τ?) (shrink t ++ List.concat (List.map shrink (shrink t))).

(* Sample (gen_expr 3 [] (Base :-> Base)). *)
Definition prop_gen_wt :=
  forAll (gen_Typ 5) (fun τ =>
  forAll (gen_expr 6 [] τ) (fun e =>
  typeOf [] e = Some τ?)). 

(* QuickChick prop_gen_wt. *)

Definition preservation (c : Mutant) (e : Term) :=
  match typeOf [] e with
  | Some τ =>
    whenFail ("Expr: " ++ show e ++ nl ++
              "With Typ: " ++ show (typeOf [] e) ++ nl ++
              "Steps to: " ++ show (pstep c e) ++ nl ++
              "With Typ: " ++ show (typeOf [] (pstep c e)))
             (typeOf [] (pstep c e) = Some τ?)
  | _ => checker tt
  end.

Definition preservation' (c : Mutant) (e : Term) : option bool := 
  match typeOf [] e with
  | Some τ =>
    Some (typeOf [] (pstep c e) = Some τ?)
  | _ => None
  end.

Definition prop_preservation_smart (c : Mutant) :=
  forAll (gen_Typ 3) (fun τ =>
  forAllShrink (gen_expr 6 [] τ) (shrink_expr τ) (fun e =>
  preservation c e)).

Definition prop_preservation_naive (c : Mutant) := 
  forAll arbitrary (preservation c).

ManualExtract [Term; Typ; Mutant].
Extract Constant defNumTests => "200000".

(* QuickChick (prop_preservation NoMutant). *)