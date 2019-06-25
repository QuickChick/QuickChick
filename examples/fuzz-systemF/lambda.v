Require Import Arith List String.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.

Import MonadNotation.
Import ListNotations.

(** Types *)

Inductive Typ :=
| Base   : Typ
| Fun    : Typ -> Typ -> Typ
| TVar   : nat -> Typ
| ForAll : Typ -> Typ.

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
| App   : Term -> Term -> Term
| TLam  : Term -> Term
| TApp  : Term -> Typ -> Term.

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
  | ForAll τ  => parens prec POuter ("∀" ++ showTyp' POuter τ)
  | TVar n    => show n
  end.

Instance show_Typ : Show Typ :=
  { show := showTyp' POuter }.

Fixpoint showExpr' prec (e : Term) :=
  match e with
  | Unit => "#"
  | Var x => show x
  | Lam τ e' => parens prec POuter ("λ" ++ show τ ++ ". " ++ showExpr' POuter e')
  | App e1 e2 => parens prec PApp (showExpr' PApp e1 ++ " " ++ showExpr' PInner e2)
  | TLam e' => parens prec POuter ("Λ. " ++ showExpr' POuter e')
  | TApp e' τ => parens prec PApp (showExpr' PApp e' ++ " [" ++ showTyp' POuter τ ++ "]")
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
| LiftLamNoLift
| LiftTLamNoIncr
| LiftTLamNoLift
| LiftTAppNoLift
| SubstNoLiftT
| LiftTypeTVar
| LiftTypeForAll
| LiftTNoIncr
| SubstInTypeLT
| SubstInTypeNoDecr
| SubstInTypeNoIncr
| SubstInTypeNoLift
| TSubstNoIncr
| TSubstNoLift
.

Definition all_mutants :=
  [ NoMutant
  ; SubstNoLift
  ; SubstNoIncr
  ; SubstNoDecr
  ; LiftAllVar
  ; LiftLamNoIncr
  ; LiftLamNoLift
  ; LiftTLamNoIncr
  ; LiftTLamNoLift
  ; LiftTAppNoLift
  ; SubstNoLiftT
  ; LiftTypeTVar
  ; LiftTypeForAll
  ; LiftTNoIncr
  ; SubstInTypeLT
  ; SubstInTypeNoDecr
  ; SubstInTypeNoIncr
  ; SubstInTypeNoLift
  ; TSubstNoIncr
  ; TSubstNoLift
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

(* Lifting and substitution *)

Fixpoint lift (c : Mutant) (n : nat) (e : Term) : Term :=
  match e with
  | Unit      => Unit
  | Var x     => mut c (Var (if x <? n then x else x+1))
                       [(LiftAllVar, Var (x+1))]
  | Lam τ e'  => mut c (Lam τ (lift c (n+1) e'))
                       [ (LiftLamNoIncr, Lam τ (lift c n e'))
                       ; (LiftLamNoLift, Lam τ e') ]
  | App e1 e2 => App (lift c n e1) (lift c n e2)
  | TLam e'   => mut c (TLam (lift c (n+1) e'))
                       [ (LiftTLamNoLift, TLam e')
                       ; (LiftTLamNoIncr, TLam (lift c n e')) ]
  | TApp e' τ => mut c (TApp (lift c n e') τ)
                       [ (LiftTAppNoLift, (TApp e' τ)) ]
  end.

(* Increase (by one) all indices above n in t *)
Fixpoint lift_type c n τ :=
  match τ with
  | TVar x => mut c (TVar (if x <? n then x else x + 1))
                    [ (LiftTypeTVar, TVar (x + 1)) ]
  | ForAll τ' => mut c (ForAll (lift_type c (n+1) τ'))
                       [ (LiftTypeForAll, ForAll τ') ]
  | τ1 :-> τ2 => lift_type c n τ1 :-> lift_type c n τ2
  | Base => Base
  end.

Fixpoint lift_types c n e :=
  match e with
  | Unit => Unit
  | Var x => Var x
  | Lam τ e'  => Lam (lift_type c n τ)   (lift_types c n e')
  | App e1 e2 => App (lift_types c n e1) (lift_types c n e2)
  | TLam e'   => mut c (TLam (lift_types c (n+1) e'))
                       [ (LiftTNoIncr, TLam e') ]
  | TApp e' τ => TApp (lift_types c n e') (lift_type c n τ)
  end.

Fixpoint subst_in_type c n σ τ :=
  match τ with
  | Base => Base
  | TVar x =>
    if x =? n then σ
    else mut c (TVar (if n <? x then (x - 1) else x))
               [ (SubstInTypeLT, TVar (if x <? n then (x-1) else x))
               ; (SubstInTypeNoDecr, TVar x) ]
  | ForAll τ' =>
    mut c (ForAll (subst_in_type c (n+1) (lift_type c 0 σ) τ'))
        [ (SubstInTypeNoIncr, ForAll (subst_in_type c n (lift_type c 0 σ) τ'))
        ; (SubstInTypeNoLift, ForAll (subst_in_type c (n+1) σ τ')) ]
  | τ1 :-> τ2 => subst_in_type c n σ τ1 :-> subst_in_type c n σ τ2
  end.

Fixpoint type_subst c n σ e :=
  match e with
  | Unit => Unit
  | Var x => Var x
  | Lam τ e' => Lam (subst_in_type c n σ τ) (type_subst c n σ e')
  | App e1 e2 => App (type_subst c n σ e1) (type_subst c n σ e2)
  | TLam e' => mut c (TLam (type_subst c (n+1) (lift_type c 0 σ) e'))
                   [ (TSubstNoIncr, TLam (type_subst c n (lift_type c 0 σ) e'))
                   ; (TSubstNoLift, TLam (type_subst c (n+1) σ e')) ]
  | TApp e' τ => TApp (type_subst c n σ e') (subst_in_type c n σ τ)
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
  | TLam e'   => mut c (TLam (subst c n (lift_types c 0 s) e'))
                     [ (SubstNoLiftT, TLam (subst c n s e')) ]
  | TApp e' τ => TApp (subst c n s e') τ
  end.

(** Typing *)

Definition env := list Typ.

(*
Inductive typing (Γ : env) : Term -> Typ -> Prop :=
| TyBase : typing Γ Unit Base
| TVar  : forall x τ, nth_error Γ x = Some τ -> typing Γ (Var x) τ
| TLam  : forall e τ1 τ2, typing (τ1 :: Γ) e τ2 -> typing Γ (Lam τ1 e) (τ1 :-> τ2)
| TApp  : forall e1 e2 τ1 τ2, typing Γ e1 (τ1 :-> τ2) ->
                              typing Γ e2 τ1 ->
                              typing Γ (App e1 e2) τ2
*)



Definition guard (b : bool) : option unit :=
  match b with
  | true => Some tt
  | false => None
  end.

Fixpoint well_formed_type (ftv : nat) (τ : Typ) : bool :=
  match τ with
  | Base => true
  | TVar n => n <? ftv
  | τ1 :-> τ2 => well_formed_type ftv τ1 && well_formed_type ftv τ2
  | ForAll τ' => well_formed_type (ftv + 1) τ'
  end.

Fixpoint typeOf (ftv : nat) (Γ : env) (e : Term) : option Typ :=
  match e with
  | Unit => Some Base
  | Var x => nth_error Γ x
  | Lam τ e' =>
     guard (well_formed_type ftv τ);;
     τ' <- typeOf ftv (τ :: Γ) e';;
     Some (τ :-> τ')
  | App e1 e2 => τ12 <- typeOf ftv Γ e1;;
                 τ1 <- typeOf ftv Γ e2;;
                 match τ12 with
                 | τ1' :-> τ2 =>
                   if τ1 = τ1' ? then Some τ2
                   else None
                 | _ => None
                 end
  | TLam e' =>
    τ <- typeOf (ftv+1) (List.map (lift_type NoMutant 0) Γ) e';;
    Some (ForAll τ)
  | TApp e' τ =>
    τ' <- typeOf ftv Γ e';;
    guard (well_formed_type ftv τ);;
    match τ' with
    | ForAll τ'' => Some (subst_in_type NoMutant 0 τ τ'')
    | _ => None
    end
  end.

Definition well_typed (e : Term) : bool :=
  match typeOf 0 [] e with
  | Some _ => true
  | _ => false
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
  | TLam e' => TLam (pstep c e')
  | TApp e' τ => match pstep c e' with
                 | TLam body => type_subst c 0 τ body
                 | e => e
                 end
  end.

(* Generation *)
Definition gen_base_type (ftv : nat) : G Typ :=
  let vars := match ftv with
              | O => []
              | S max => seq 0 max
              end in
  elems_ Base (Base :: map TVar vars).

Fixpoint gen_type (ftv n : nat) : G Typ :=
  match n with
  | O => gen_base_type ftv
  | S n' => oneOf  [ gen_base_type ftv
                   ; τ1 <- gen_type ftv (n' - 1);;
                     τ2 <- gen_type ftv n';;
                     ret (τ1 :-> τ2)
                   ; τ' <- gen_type (ftv+1) n';;
                     ret (ForAll τ')
                   ]
  end.

Definition lift_env :=
  map (lift_type NoMutant 0).

Fixpoint gen_base_expr (ftv : nat) (Γ : env) (τ : Typ) : G (option Term) :=
  let vars : list Term :=
      map (fun '(n, τ') => Var n)
          (filter (fun '(n, τ') => τ = τ'?)
                  (combine (seq 0 (List.length Γ)) Γ)) in
  let base : G (option Term) :=
      match τ with
      | Base => ret (Some Unit)
      | τ1 :-> τ2 => e' <- gen_base_expr ftv (τ1 :: Γ) τ2;;
                     ret (Lam τ1 e')
      | ForAll τ' => e' <- gen_base_expr (ftv + 1) (lift_env Γ) τ';;
                     ret (TLam e')
      | TVar x =>
        match vars with
        | v :: vs => χ <- elems_ v vars;;
                     ret (Some (Var x))
        | [] => ret (@None Term)
        end
      end in
  oneOf_ base (base :: map ret vars).

Fixpoint closed tc τ : bool :=
  match τ with
  | TVar x => x <? tc
  | Base => true
  | ForAll τ' => closed (tc+1) τ'
  | τ1 :-> τ2 => closed tc τ1 && closed tc τ2
  end.

(* Calculates whether a type is closed and its possible closed subtypes. *)
Fixpoint all_closed_subtypes tc (τ : Typ) : (bool * list Typ) :=
  match τ with
  | TVar x => if x <? tc then (true, [TVar x]) else (false, [])
  | Base => (true, [Base])
  | ForAll τ' =>
    let (b, τs) := all_closed_subtypes (tc+1) τ' in
    if b then (true, ForAll τ' :: τs) else (false, τs)
  | τ1 :-> τ2 =>
    let (b1, τs1) := all_closed_subtypes tc τ1 in
    let (b2, τs2) := all_closed_subtypes tc τ2 in
    if (b1 && b2)%bool then (true, τ :: τs1 ++ τs2) else (false, τs1 ++ τs2)
  end%list.
  
Fixpoint fetch_sub_type τ : G (option Typ) :=
  elems_ (None)
         (map Some (snd (all_closed_subtypes 0 τ))).
                              
(* Replace (some occurrences of) closed type σ in type τ by (TVar n) *)
Fixpoint replace_sub_type n σ τ : G Typ :=
  if σ = τ ? then
    freq_ (ret τ)
          [ (5, ret (TVar n))
          ; (1, ret τ) ]
  else match τ with
       | Base   => ret τ
       | TVar x => ret τ
       | τ1 :-> τ2 => τ1' <- replace_sub_type n σ τ1;;
                      τ2' <- replace_sub_type n σ τ2;;
                      ret (τ1' :-> τ2')
       | ForAll τ' => τ'' <- replace_sub_type n σ τ';;
                      ret (ForAll τ'')
       end.

(* Generate t1 t2 such that t1{0:=t2} = t *)
Definition genUnsubst τ : G (option (Typ * Typ)) :=
  let τ' := lift_type NoMutant 0 τ in
  bindGenOpt (fetch_sub_type τ') (fun τ2 =>
  bindGen  (replace_sub_type 0 τ2 τ') (fun τ1 =>
  returnGen (Some (τ1, τ2)))).                                         

Fixpoint gen_expr (n ftv : nat) (Γ : env) (τ : Typ) : G (option Term) :=
  match n with
  | O    => gen_base_expr ftv Γ τ
  | S n' =>
    let gLam : list (G (option Term)) :=
        match τ with
        | τ1 :-> τ2 =>
          [ e <- gen_expr n' ftv (τ1 :: Γ) τ2 ;;
            ret (Lam τ1 e)
          ]
        | _ => []
        end in
    let gTLam : list (G (option Term)) :=
        match τ with
        | ForAll τ' =>
          [ e <- gen_expr n' (ftv + 1) (lift_env Γ) τ' ;;
            ret (TLam e)
          ] 
        | _ => []
        end in
    let gApp : G (option Term) :=
        bindGen (gen_type (min n 5) ftv) (fun τ1 =>
        e1 <- gen_expr n' ftv Γ (τ1 :-> τ);;
        e2 <- gen_expr n' ftv Γ τ1;;
        ret (App e1 e2)) in
    let gTApp : G (option Term) :=
        τ12 <- genUnsubst τ;;
        let (τ1, τ2) := (τ12 : Typ * Typ) in 
        e <- gen_expr n' ftv Γ τ1;;
        ret (TApp e τ2)
    in
    oneOf_ (gen_base_expr ftv Γ τ)
           ([ gen_base_expr ftv Γ τ] ++ gLam ++ gTLam ++ [gApp ; gTApp])
  end.

Fixpoint shrink_expr (τ : Typ) (t : Term) : list Term :=
  List.filter (fun t' => typeOf 0 [] t' = Some τ?)
              (shrink t ++ List.concat (List.map shrink (shrink t))).

(* Sample (gen_expr 3 [] (Base :-> Base)). *)
Definition prop_gen_wt :=
  forAll (gen_type 0 5) (fun τ =>
  forAllMaybe (gen_expr 6 0 [] τ) (fun e =>
  typeOf 0 [] e = Some τ?)). 

QuickChick prop_gen_wt. 

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