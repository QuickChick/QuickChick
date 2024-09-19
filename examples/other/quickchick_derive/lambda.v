From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import Arith List String Lia.
Require Import Program Relations Wellfounded Lexicographic_Product.
From QuickChick Require Import QuickChick.

Import ListNotations.

QuickChickDebug Debug On.

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof. do 2 decide equality. Defined.



Inductive term : Type :=
| Const : nat -> term
| Id : nat -> term
| App : term -> term -> term
| Abs : term -> term.

#[global] Instance dec_term (t1 t2 : term) : Dec (t1 = t2).
Proof. dec_eq. Defined.

(* Terms that do not have applications *)
Inductive app_free : term -> Prop :=
| ConsNoApp : forall n, app_free (Const n)
| IdNoApp : forall x, app_free (Id x)
| AbsNoApp : forall (t : term),
               app_free t -> app_free (Abs t).

(* Number of applications in a term *)
Fixpoint app_no (t : term) : nat :=
  match t with
    | Const _ | Id _ => 0
    | Abs t => app_no t
    | App t1 t2 => 1 + (app_no t1 + app_no t2)
  end.

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Inductive typing' (e : env) : term -> type -> Prop :=
| TId' :
    forall x tau,
      bind e x tau ->
      typing' e (Id x) tau
| TConst' :
    forall n,
      typing' e (Const n) N
| TAbs' :
    forall t tau1 tau2,
      typing' (tau1 :: e) t tau2 ->
      typing' e (Abs t) (Arrow tau1 tau2)
| TApp' :
    forall t1 t2 tau tau1 tau2,
      typing' e t2 tau1 ->
      typing' e t1 tau ->
      tau = Arrow tau1 tau2 ->
      typing' e (App t1 t2) tau2.

Check typing'.

Derive Arbitrary for type.
Derive Arbitrary for term.
#[global]
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
(*Derive ArbitrarySizedSuchThat for (fun t => typing' env t tau).*)

Inductive value : term -> Prop :=
| ValueConst : forall n, value (Const n)
| ValueAbs : forall t, value (Abs t)
.

Derive DecOpt for (value t).

Inductive subst (y : nat) (t1 : term) : term -> term -> Prop :=
| SubstId : subst y t1 (Id y) t1
| SubstIdDiff : forall x, x <> y -> subst y t1 (Id x) (Id x)
| SubstConst : forall n, subst y t1 (Const n) (Const n)
| SubstApp : forall t t' t'' t''',
    subst y t1 t t' ->
    subst y t1 t'' t''' ->
    subst y t1 (App t t'') (App t' t''')
| SubstAbs : forall t t',
    subst (S y) t1 t t' ->
    subst y t1 (Abs t) (Abs t').

Derive DecOpt for (subst y t1 t2 t2').
Derive DecOpt for (bind env x tau).
(*Derive DecOpt for (typing' env e tau).*)

Search Enum.

QuickChickDebug Debug On.
Derive EnumSized for type.
Derive EnumSizedSuchThat for (fun typ => bind env x typ).
Derive EnumSizedSuchThat for (fun typ => typing' env e typ).
Derive DecOpt for (typing' env e tau).

Inductive step : term -> term -> Prop :=
| StepApp1 : forall t1 t1' t2,
    step t1 t1' ->
    step (App t1 t2) (App t1' t2)
| StepApp2 : forall t1 t2 t2',
    value t1 ->
    step t2 t2' ->
    step (App t1 t2) (App t1 t2')
| StepAppAbs : forall t t' t2,
    value t2 ->
    subst 0 t2 t t' ->
    step (App (Abs t) t2) t'
.

(*Derive DecOpt for (step e e').*)
Derive GenSizedSuchThat for (fun e' => step e e').
Derive ArbitrarySizedSuchThat for (fun e => typing' env e tau).
Derive Show for type.
Derive Show for term.

Axiom segev_fuel_nat : nat.

Extract Constant segev_fuel_nat => "1000".

Derive DecOpt for (step e e').



(*Check decopt_step.
Compute decopt_step (Const 1) (Const 2) 1000.

Definition a := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun e =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun e' =>
         if
          match @QuickChick.Decidability.decOpt (@step (Const 0) e') _ segev_fuel_nat with
          | Coq.Init.Datatypes.Some res => res
          | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
          end 
         then
           QuickChick.Checker.checker true
         else
           QuickChick.Checker.checker false
                ))).*)

(*Definition b := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun e =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun e' =>
         if
          match @QuickChick.Decidability.decOpt (@step e e') _ segev_fuel_nat with
          | Coq.Init.Datatypes.Some res => res
          | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
          end 
         then
           QuickChick.Checker.checker Coq.Init.Datatypes.tt
         else
           QuickChick.Checker.checker Coq.Init.Datatypes.tt
       ))).*)

(* QuickChick a.


Definition a' := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun e => let e := App (Id 1) (Const 0) in 
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun e' => let e' := App (Id 0) (Const 0) in
       QuickChick.Checker.forAll QuickChick.Classes.arbitrary
         (fun Gamma => let Gamma := [N] in 
          QuickChick.Checker.forAll QuickChick.Classes.arbitrary
            (fun tau => let tau := N in
             if
              if false then true else match @QuickChick.Decidability.decOpt (@typing' Gamma e tau) _ segev_fuel_nat with
              | Coq.Init.Datatypes.Some res => res
              | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
              end
             then
              if
               match @QuickChick.Decidability.decOpt (@step e e') _ 100 with
               | Coq.Init.Datatypes.Some res => res
               | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
               end 
              then
               QuickChick.Checker.checker
                 match @QuickChick.Decidability.decOpt (@typing' Gamma e' tau) _ segev_fuel_nat with
                 | Coq.Init.Datatypes.Some res => res
                 | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
                 end
              else QuickChick.Checker.checker Coq.Init.Datatypes.tt
             else QuickChick.Checker.checker Coq.Init.Datatypes.tt))))).

Check a'.

Check checker. Print Checker.

QuickChick a'. *)

(* QuickChick a'.

Compute @decOpt (@typing' [] (Const 0) (Arrow N N)) _ 1000.

Derive GenSizedSuchThat for (fun e => typing' Gamma e tau).

Definition b := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun tau =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun Gamma =>
       QuickChick.Checker.forAll (@QuickChick.DependentClasses.arbitraryST _ (fun e => @typing' Gamma e tau) _)
         (fun e =>
          match e with
          | @Coq.Init.Datatypes.Some _ e =>
              QuickChick.Checker.forAll (@QuickChick.DependentClasses.arbitraryST _ (fun e' => @step e e') _)
                (fun e' =>
                 match e' with
                 | @Coq.Init.Datatypes.Some _ e' =>
                     QuickChick.Checker.checker
                       match @QuickChick.Decidability.decOpt (@typing' Gamma e' tau) _ 1000%nat with
                       | Coq.Init.Datatypes.Some res => res
                       | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
                       end
                 | _ => QuickChick.Checker.checker Coq.Init.Datatypes.tt
                 end)
          | _ => QuickChick.Checker.checker Coq.Init.Datatypes.tt
          end)))).

QuickChick b. *)

From QuickChick Require Import Tyche.
Check size.
Locate size. Check size.

Derive Sized for term.
Derive Sized for type.
Derive Sized for list.

Extract Constant defNumTests => "10000".

Definition a := 3.

Definition prop := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun e =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun e' =>
       QuickChick.Checker.forAll QuickChick.Classes.arbitrary
         (fun Gamma =>
          QuickChick.Checker.forAll QuickChick.Classes.arbitrary
            (fun tau =>
             if
              match @QuickChick.Decidability.decOpt (@typing' Gamma e tau) _ a with
              | Coq.Init.Datatypes.Some res => res
              | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
              end
             then
              if
               match @QuickChick.Decidability.decOpt (@step e e') _ 1 with
               | Coq.Init.Datatypes.Some res => res
               | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
               end
              then
               QuickChick.Tyche.tyche_with_features "test"%string
                 (QuickChick.Show.show
                    (Coq.Init.Datatypes.pair
                       (Coq.Init.Datatypes.pair (Coq.Init.Datatypes.pair (QuickChick.Show.show tau) (QuickChick.Show.show Gamma))
                          (QuickChick.Show.show e')) (QuickChick.Show.show e)))
                 (Coq.Lists.List.cons
                    (Coq.Init.Datatypes.pair "tau-size"%string
                       (Coq.Init.Datatypes.inr (Coq.ZArith.BinInt.Z.of_nat (QuickChick.Classes.size tau))))
                    (Coq.Lists.List.cons
                       (Coq.Init.Datatypes.pair "Gamma-size"%string
                          (Coq.Init.Datatypes.inr (Coq.ZArith.BinInt.Z.of_nat (QuickChick.Classes.size Gamma))))
                       (Coq.Lists.List.cons
                          (Coq.Init.Datatypes.pair "e'-size"%string
                             (Coq.Init.Datatypes.inr (Coq.ZArith.BinInt.Z.of_nat (QuickChick.Classes.size e'))))
                          (Coq.Lists.List.cons
                             (Coq.Init.Datatypes.pair "e-size"%string
                                (Coq.Init.Datatypes.inr (Coq.ZArith.BinInt.Z.of_nat (QuickChick.Classes.size e)))) Coq.Lists.List.nil))))
                 (QuickChick.Checker.checker
                    match @QuickChick.Decidability.decOpt (@typing' Gamma e' tau) _ 1 with
                    | Coq.Init.Datatypes.Some res => res
                    | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
                    end)
              else QuickChick.Checker.checker Coq.Init.Datatypes.tt
             else QuickChick.Checker.checker Coq.Init.Datatypes.tt)))))
.

Definition prop' := (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun e =>
    QuickChick.Checker.forAll QuickChick.Classes.arbitrary
      (fun e' =>
       QuickChick.Checker.forAll QuickChick.Classes.arbitrary
         (fun Gamma =>
          QuickChick.Checker.forAll QuickChick.Classes.arbitrary
            (fun tau =>
             if
              match @QuickChick.Decidability.decOpt (@typing' Gamma e tau) _ a with
              | Coq.Init.Datatypes.Some res => res
              | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
              end
             then
              if
               match @QuickChick.Decidability.decOpt (@step e e') _ a with
               | Coq.Init.Datatypes.Some res => res
               | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
               end
              then
               
                 (QuickChick.Checker.checker
                    match @QuickChick.Decidability.decOpt (@typing' Gamma e' tau) _ a with
                    | Coq.Init.Datatypes.Some res => res
                    | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
                    end)
              else QuickChick.Checker.checker Coq.Init.Datatypes.tt
             else QuickChick.Checker.checker Coq.Init.Datatypes.tt)))))
.

Compute @decOpt (@typing' [] (Const 0) N) _ 1000.

QuickCheck prop'.
Check @arbitraryST.

Definition prop'' := 
  forAll arbitrary (fun tau =>
  (* forAll arbitrary (fun Gamma =>   *)
  forAll (@arbitraryST _ (fun e => typing' [] e tau) _) (fun e =>
    match e with 
    | Some e => 
      forAll (@arbitraryST _ (fun e' => step e e') _) (fun e' =>
        match e' with
        | Some e' =>
          checker (match @decOpt (@typing' [] e' tau) _ 1000 with
                   | Some res => res
                   | None => false
                   end)
        | None => checker tt
        end)
    | None => checker tt
    end)).

QuickCheck prop''.







Theorem preservation : forall e e' Gamma tau,
    typing' Gamma e tau ->
    step e e' ->
    typing' Gamma e' tau.
Proof.
  grab_dependencies. print_all_bindings. derive_and_quickchick_index 9.

  derive_and_quickchick_index 2. quickchick.
Admitted.

(*  
Open Scope string.

Fixpoint show_type (tau : type) :=
  match tau with
    | N => "Nat"
    | Arrow tau1 tau2 =>
      "(" ++ show_type tau1 ++ " -> " ++ show_type tau2 ++ ")"
  end.

#[global]
Instance showType : Show type := { show := show_type }.

Fixpoint show_term (t : term) :=
  match t with
    | Const n => show n
    | Id x => "Id" ++ show x
    | App t1 t2 => "(" ++ show_term t1 ++ " " ++ show_term t2 ++ ")"
    | Abs t => "λ.(" ++ show_term t ++ ")"
  end.

Close Scope string.

#[global]
Instance showTerm : Show term := { show := show_term }.
*)
