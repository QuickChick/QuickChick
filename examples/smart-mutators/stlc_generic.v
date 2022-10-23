From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Ty :=
| Unt : Ty
| Arr : Ty -> Ty -> Ty.

Derive (Arbitrary, Sized) for Ty.

Program Instance show_Ty : Show Ty := {
  show :=
    fix show' (ty: Ty) := 
    match ty with 
    | Unt => "*"
    | Arr A B => "(" ++ show' A ++ " -> " ++ show' B ++ ")"
    end
}.

Instance eq_Ty (t1 t2 : Ty) : Dec (t1 = t2).
Proof. dec_eq. Qed.

Inductive Tm :=
| Tt : Tm (* : Unt *)
| Var : nat -> Tm
| Lam : Ty -> Tm -> Tm
| App : Tm -> Tm -> Tm.

Derive (Arbitrary, Sized) for Tm.

Program Instance show_Tm : Show Tm := {
  show :=
    fix show' (tm: Tm) :=
    match tm with 
    | Tt => "*"
    | Var n => show n
    | Lam A b => "(λ " ++ show A ++ " => " ++ show' b ++ ")"
    | App f a => "(" ++ show' f ++ " " ++ show' a ++ ")"
    end
}.

Definition Ctx := list Ty.

Inductive typed_var : Ctx -> Ty -> nat -> Prop :=
| typed_var_O : forall gamma alpha, 
    typed_var (alpha :: gamma) alpha O
| typed_var_S : forall gamma alpha beta n, 
    typed_var gamma alpha n -> 
    typed_var (beta :: gamma) alpha (S n).

Inductive typed : Ctx -> Ty -> Tm -> Prop :=
| typed_Tt : forall gamma, 
    typed gamma Unt Tt
| typed_Var : forall gamma alpha n, 
    typed_var gamma alpha n -> 
    typed gamma alpha (Var n)
| typed_Lam : forall gamma alpha beta bod,
    typed (alpha :: gamma) beta bod ->
    typed gamma (Arr alpha beta) (Lam alpha bod)
| typed_App : forall gamma alpha beta apl arg,
    typed gamma (Arr alpha beta) apl ->
    typed gamma alpha arg ->
    typed gamma beta (App apl arg).

Fixpoint infer_type_var (gamma: Ctx) (n: nat): option Ty :=
  match gamma with
  | [] => None 
  | alpha :: gamma' => 
    match n with 
    | O => Some alpha
    | S n' => infer_type_var gamma' n'
    end 
  end.

(* TODO: is this sufficient? *)
Derive DecOpt for (typed_var gamma alpha n).

Fixpoint is_typed_var (gamma: Ctx) (ty: Ty) (n: nat): bool :=
  match infer_type_var gamma n with 
  | Some ty' => (ty = ty')?
  | None => false
  end.

(* TODO: why fail? *)
Fail Derive DecOpt for (typed gamma alpha t).
  
Fixpoint infer_type (gamma: Ctx) (tm: Tm): option Ty :=
  match tm with 
  | Tt => Some Unt
  | Var n => infer_type_var gamma n
  | Lam alpha b => 
    match infer_type (alpha :: gamma) b with 
    | None => None 
    | Some beta => Some (Arr alpha beta)
    end 
  | App f a =>
    match infer_type gamma f with 
    | Some (Arr alpha beta) =>
      if is_typed gamma alpha a 
        then Some beta
        else None
    | _ => None
    end
  end

with is_typed (gamma: Ctx) (ty: Ty) (tm: Tm): bool :=
  match tm with
  | Tt => (ty = Unt)?
  | Var n => is_typed_var gamma ty n 
  | Lam alpha b => 
    match ty with
    | Arr alpha' beta => 
      andb ((alpha = alpha')?)
           (is_typed (alpha :: gamma) beta b)
    | _ => false
    end
  | App f a =>
    match infer_type gamma f with 
    | Some (Arr alpha beta) =>
      andb (is_typed gamma alpha a)
           ((beta = ty)?)
    | _ => false
    end
  end. 

Derive ArbitrarySizedSuchThat for (fun n => typed_var gamma alpha n).
Derive ArbitrarySizedSuchThat for (fun t => typed gamma alpha t).

(* mutation *)

Fixpoint mut_typed (gamma: Ctx) (ty: Ty) (tm: Tm): G (option Tm) :=
  let mut_this: G (option Tm) :=
        bind (genST (fun tm' => typed gamma ty tm')) (fun opt_tm' =>
        match opt_tm' with 
        | None => ret (Some tm)
        | Some tm' => ret (Some tm')
        end)
  in
  match tm return G (option Tm) with
  (* no constructors of  *)
  | Tt =>
    backtrack
      [ (* mut this *)
        ( 1 , mut_this )
        (* can't mutate via typed_Tt since everything is fixed *)
      ]
  | Var n =>
    backtrack
      [ (* mut this *)
        ( 1 , mut_this )
      (* cons of `typed .. (Var n)`: `typed_Var` *)
      ; (* mut n *)
        ( List.length gamma (* TODO: how to derive this weight? *)
        , bindGenOpt (genST (fun n' => typed_var gamma ty n')) (fun n' =>
          ret (Some (Var n')) )
        )
      ]
  | Lam alpha b =>
    backtrack
      [ (* mut this*)
        ( 1 , mut_this )
      (* cons of `typed .. (Lam alpha b)`: `typed_Lam` *)
      ; (*  *)
      ]
  | _ => ret None
  end.