From QuickChick Require Import QuickChick.
From Coq Require Import Bool ZArith List.
Import ListNotations.

(* A small de Bruijn-indexed simply typed lambda calculus. *)

Inductive typ :=
| TBool : typ
| TFun  : typ -> typ -> typ.

Derive GenSized for typ.

Open Scope string.

Fixpoint show_typ_depth (depth : nat) (t : typ) : string :=
  match depth with
  | 0 => "_"
  | S depth' =>
      match t with
      | TBool => "Bool"
      | TFun tin tout =>
          "(" ++ show_typ_depth depth' tin ++ " -> " ++
          show_typ_depth depth' tout ++ ")"
      end
  end.

Definition show_typ (t : typ) : string := show_typ_depth 3 t.

#[export] Instance show_typ_instance : Show typ :=
  {| show := show_typ |}.

#[export] Instance dec_typ (t1 t2 : typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.

Inductive term :=
| Var  : nat -> term
| Bool : bool -> term
| Abs  : typ -> term -> term
| App  : term -> term -> term.

Derive GenSized for term.

Fixpoint show_term (e : term) : string :=
  match e with
  | Var n => "#" ++ show n
  | Bool b => show b
  | Abs t body => "(lambda " ++ show_typ t ++ ". " ++ show_term body ++ ")"
  | App e1 e2 => "(" ++ show_term e1 ++ " " ++ show_term e2 ++ ")"
  end.

#[export] Instance show_term_instance : Show term :=
  {| show := show_term |}.

Close Scope string.

#[export] Instance dec_eq_term : Dec_Eq term.
Proof. dec_eq. Defined.

Definition context := list typ.

(* Deliberately buggy shift for the live demo. *)
Definition shift (d : Z) (ex : term) : term :=
  let fix go (cutoff : Z) (e : term) :=
      match e with
      | Var n =>
          if n <? Z.to_nat cutoff
          then Var n
          else Var (Z.to_nat (Z.of_nat n + d))
      | Bool b => Bool b
      | Abs t body => Abs t (go cutoff body)
      | App e1 e2 => App (go cutoff e1) (go cutoff e2)
      end
  in go 0%Z ex.

Fixpoint subst (n : nat) (s e : term) : term :=
  match e with
  | Var m => if m =? n then s else Var m
  | Bool b => Bool b
  | Abs t body => Abs t (subst (n + 1) (shift 1 s) body)
  | App e1 e2 => App (subst n s e1) (subst n s e2)
  end.

Definition subst_top (s e : term) : term :=
  shift (-1) (subst 0 (shift 1 s) e).

Inductive value : term -> Prop :=
| VBool : forall b,
    value (Bool b)
| VAbs : forall t body,
    value (Abs t body).

#[export] Instance dec_value (e : term) : Dec (value e).
Proof.
  constructor.
  destruct e.
  - right. intros H. inversion H.
  - left. constructor.
  - left. constructor.
  - right. intros H. inversion H.
Defined.

Inductive Step : term -> term -> Prop :=
| StBeta : forall t body arg out,
    value arg ->
    subst_top arg body = out ->
    Step (App (Abs t body) arg) out
| StAppLeft : forall e1 e1' e2 out,
    Step e1 e1' ->
    App e1' e2 = out ->
    Step (App e1 e2) out
| StAppRight : forall v e2 e2' out,
    value v ->
    Step e2 e2' ->
    App v e2' = out ->
    Step (App v e2) out.

Inductive bind : context -> nat -> typ -> Prop :=
| BindNow : forall t Gamma,
    bind (t :: Gamma) 0 t
| BindLater : forall t t' x Gamma,
    bind Gamma x t ->
    bind (t' :: Gamma) (S x) t.

Inductive typing (Gamma : context) : term -> typ -> Prop :=
| TyVar : forall x t,
    bind Gamma x t ->
    typing Gamma (Var x) t
| TyBool : forall b,
    typing Gamma (Bool b) TBool
| TyAbs : forall body tin tout,
    typing (tin :: Gamma) body tout ->
    typing Gamma (Abs tin body) (TFun tin tout)
| TyApp : forall e1 e2 tin tout,
    typing Gamma e1 (TFun tin tout) ->
    typing Gamma e2 tin ->
    typing Gamma (App e1 e2) tout.

Extract Constant defSize => "4".
Extract Constant defNumDiscards => "50000".
QuickChickDebug Debug Off.

(* ---------------------------------------------------------------------- *)
(* Live demo starts here. *)

Theorem preservation : forall e e' t,
    typing [] e t ->
    Step e e' ->
    typing [] e' t.
Proof.
  quickchick.
Abort.
