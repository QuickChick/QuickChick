From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import Arith List String Lia.
From QuickChick Require Import QuickChick.
Import ListNotations.

(* Types *)

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Derive (Arbitrary, Show, EnumSized) for type.
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.

(* Terms *)

Definition var := nat.

Inductive term : Type :=
| Const : nat -> term
| Id : var -> term
| App : term -> term -> term
| Abs : type -> term -> term.

(* Environments *)

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall t G, bind (t :: G) 0 t
| BindLater : forall t t' x G,
    bind G x t -> bind (t' :: G) (S x) t.

(* Generate variables of a specific type in an env. *)
Derive ArbitrarySizedSuchThat for (fun x => bind G x t).
(* Get the type of a given variable in an env. *)
Derive EnumSizedSuchThat for (fun t => bind G x t).
(* Check whether a variable has a given type in an env. *)
Derive DecOpt for (bind G e t).

(* Typing *)

Inductive typing (G : env) : term -> type -> Prop :=
| TId :
    forall x t,
      bind G x t ->
      typing G (Id x) t
| TConst :
    forall n,
      typing G (Const n) N
| TAbs :
    forall e t1 t2,
      typing (t1 :: G) e t2 ->
      typing G (Abs t1 e) (Arrow t1 t2)
| TApp :
    forall e1 e2 t1 t2,
      typing G e2 t1 ->
      typing G e1 (Arrow t1 t2) ->
      typing G (App e1 e2) t2.

Fixpoint typeOf G e : option type :=
  match e with
  | Id x => nth_error G x
  | Const n => Some N
  | Abs t e' =>
    match typeOf (t::G) e' with
    | Some t' => Some (Arrow t t')
    | None => None
    end
  | App e1 e2 =>
    match typeOf G e1, typeOf G e2 with
    | Some (Arrow t1 t2), Some t1' =>
      if t1 = t1'? then Some t2 else None
    | _, _ => None
    end
  end.

(* Generate terms of a specific type in an env. *)
Derive ArbitrarySizedSuchThat for (fun e => typing G e t).
Derive EnumSizedSuchThat for (fun t => typing G e t).

(* Check whether a variable has a given type in an env. *)
Derive DecOpt for (typing G e t).

(* Small step CBV semantics *)
Inductive value : term -> Prop :=
| VConst : forall n, value (Const n)
| VAbs   : forall t e, value (Abs t e).

Derive DecOpt for (value e).

Definition is_value (e : term) : bool :=
  match e with
  | Const _ | Abs _ _ => true
  | _ => false
  end.

Fixpoint subst (y : var) (e1 : term) (e2 : term) : term :=
  match e2 with
    | Const n => Const n
    | Id x =>
      if eq_nat_dec x y then e1 else e2
    | App e e' =>
      App (subst y e1 e) (subst y e1 e')
    | Abs t e =>
      Abs t (subst (S y) e1 e)
  end.

Fixpoint step (e : term) : option term :=
  match e with
    | Const _ | Id _ => None | Abs _ x => None
    | App (Abs t e1) e2 =>
      if is_value e2 then Some (subst 0 e2 e1)
      else
        match step e2 with
        | Some e2' => Some (App (Abs t e1) e2')
        | None => None
        end
    | App e1 e2 =>
      match step e1 with
      | Some e1' => Some (App e1' e2)
      | None => None
      end
  end.

Eval compute in (step (App (Abs N (Id 0)) (Const 42))).
Eval compute in (step (App (Abs N (Abs N (Id 0))) (Const 42))).
Eval compute in (subst 0 (Const 42) (Abs N (Id 0))).

(* Printing *)

Open Scope string.

Fixpoint show_type (tau : type) :=
  match tau with
    | N => "N"
    | Arrow tau1 tau2 =>
      "(Arrow " ++ show_type tau1 ++ " -> " ++ show_type tau2 ++ ")"
  end.

Instance showType : Show type := { show := show_type }.

Fixpoint show_term (e : term) :=
  match e with
    | Const n => "(Const " ++ show n ++ ")"
    | Id x => "(Id " ++ show x ++ ")"
    | App e1 e2 => "(App " ++ show_term e1 ++ " " ++ show_term e2 ++ ")"
    | Abs t e => "(Abs " ++ show t ++ " " ++ show_term e ++ ")"
  end.

Close Scope string.

Instance showTerm : Show term := { show := show_term }.

Instance dec_eq_opt_type : Dec_Eq (option type).
Proof. dec_eq. Defined.

Definition preservation (e : term) (t: type) : Checker :=
  match step e with
  | Some e' => checker ((typeOf nil e' = Some t)?)
  | None => checker true
  end.

Definition preservation' (e : term) (t: type) : Checker :=
  match step e with
  | Some e' => typing nil e' t ?? 10
  | None => checker true
  end.

Definition preservation_prop (c : term -> type -> Checker) :=
  forAll (@arbitrary type _) (fun t =>
  forAllMaybe ((genST (fun e => typing nil e t))) (fun e =>
                                                   c e t)).

Extract Constant defNumTests => "20000".
QuickChick (preservation_prop preservation).
QuickChick (preservation_prop preservation').
























