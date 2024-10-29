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
| Abs : type -> term -> term.

Fixpoint subst' (x : nat) (s : term) (t : term) :=
  match t with
  | Const n => Const n
  | Id y => if Nat.eqb x y then s else t
  | App ef ex =>
      App (subst' x s ef) (subst' x s ex)
  | Abs t e =>
      Abs t (subst' (S x) s e)
  end.

#[global] Instance dec_term (t1 t2 : term) : Dec (t1 = t2).
Proof. dec_eq. Defined.

#[global] Instance dec_type (t t' : type) : Dec (t = t').
Proof. dec_eq. Defined.

(* Terms that do not have applications *)
Inductive app_free : term -> Prop :=
| ConsNoApp : forall n, app_free (Const n)
| IdNoApp : forall x, app_free (Id x)
| AbsNoApp : forall (e : term) t,
               app_free e -> app_free (Abs t e).

(* Number of applications in a term *)
Fixpoint app_no (t : term) : nat :=
  match t with
    | Const _ | Id _ => 0
    | Abs t e => app_no e
    | App t1 t2 => 1 + (app_no t1 + app_no t2)
  end.

Definition env := list type.

Inductive bind : list type -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) O tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Derive Sized for term.

Derive Density bind 2.
Derive Density bind 0.
Derive Density bind 1. 


Inductive Duct : bool -> nat -> bool -> nat -> Prop :=
| DA a b : Duct b a b 0
| DB a : Duct true 0 false a.

Derive Density Duct   1 .

(* Derive Density Duct 1. *)

Inductive typing' (e : list type) : term -> type -> Prop :=
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
      typing' e (Abs tau1 t) (Arrow tau1 tau2)
| TApp' :
  forall t1 t2 tau1 tau2,
      typing' e t1 (Arrow tau1 tau2) ->
      typing' e t2 tau1 ->
      typing' e (App t1 t2) tau2.

Derive Enumerator for (fun tau => bind e x tau).
Derive Checker for (bind e x tau).
Derive EnumSized for type.
Derive Checker for (typing' env e tau).

Derive Enumerator for (fun tau => typing' env e tau).



Derive Density typing' 1.
Derive Density typing' 2. 
Check typing'.

Derive Arbitrary for type.
Derive Arbitrary for term.

(*Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).*)
(*Derive ArbitrarySizedSuchThat for (fun t => typing' env t tau).*)

Inductive value : term -> Prop :=
| ValueConst : forall n, value (Const n)
| ValueAbs : forall t e, value (Abs t e)
.

(*Derive Density value 0.*)

Derive DecOpt for (value t).

Inductive subst (y : nat) (t1 : term) : term -> term -> Prop :=
| SubstId : subst y t1 (Id y) t1
| SubstIdDiff : forall x, x <> y -> subst y t1 (Id x) (Id x)
| SubstConst : forall n, subst y t1 (Const n) (Const n)
| SubstApp : forall t t' t'' t''',
    subst y t1 t t' ->
    subst y t1 t'' t''' ->
    subst y t1 (App t t'') (App t' t''')
| SubstAbs : forall t e e',
    subst (S y) t1 e e' ->
    subst y t1 (Abs t e) (Abs t e').


Derive Density subst 3.
Derive Density eq 2.
Derive DecOpt for (subst y t1 t2 t2').
Derive DecOpt for (bind env x tau).
(*Derive DecOpt for (typing' env e tau).*)


Inductive bigstep : term -> term -> Prop :=
| bs_const n : bigstep (Const n) (Const n)
| bs_id x : bigstep (Id x) (Id x)
| bs_abs t e : bigstep (Abs t e) (Abs t e)
| bs_app ef ex t e e' : bigstep ef (Abs t e) -> subst 0 ex e e' -> bigstep (App ef ex) e'
.

Derive Density bigstep 1.

Inductive bigstep' : term -> term -> Prop :=
| bs_const' n : bigstep' (Const n) (Const n)
| bs_id' x : bigstep' (Id x) (Id x)
| bs_abs' t e : bigstep' (Abs t e) (Abs t e)
| bs_app' ef ex t e : bigstep' ef (Abs t e) -> bigstep' (App ef ex) (subst' 0 ex e)
.

Derive Density bigstep' 1.

Derive (Show, Sized, Shrink) for type.
Derive Sized for list.
Derive Show for term.
Derive EnumSized for term.
Derive DecOpt for (bigstep' e e').

Theorem preservation : forall env' e e' t,
    typing' env' e t ->
    bigstep' e e' ->
    typing' env' e' t.
Proof.
  print_all_bindings.
  valid_bindings.
  Extract Constant defSize        => "2".
  derive_and_quickchick_index 6.
  Admitted.

  Inductive A : nat -> Prop :=
  | Aone : A 1
  .

  Inductive B : nat -> Prop :=
  | Btwo : B 2.
  Derive DecOpt for (B n).
  Derive Sized for nat.
  
  Theorem awg : forall n, A n -> B n.
  Proof.
    print_all_bindings.
    valid_bindings.
    derive_and_quickchick_index 0.
 
Derive GenSizedSuchThat for (fun e' =>  bigstep e e').

Derive Density 

Search Enum.

QuickChickDebug Debug On.
Derive EnumSized for type.
Derive EnumSizedSuchThat for (fun typ => bind env x typ).
(*Derive EnumSizedSuchThat for (fun typ => typing' env e typ).*)
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
   (* value t2 ->*)
    subst 0 t2 t t' ->
    value t2 -> 
    step (App (Abs t) (t2)) t'
.

QuickChickDebug Debug Off.

Derive Density step 1  .

Derive Density typing' 1 2 .

Derive Density eq 2.

Inductive AD {p : bool} : nat -> Prop :=
| AD_r : AD 0.

Derive Density step 0 .

Derive GenSizedSuchThat for (fun x => eq x y).

Print eq.
(*Derive DecOpt for (step e e').*)
(*Derive GenSizedSuchThat for (fun e' => step e e').*)
(*Derive ArbitrarySizedSuchThat for (fun e => typing' env e tau).*)
Derive Show for type.
Derive Show for term.
Axiom segev_fuel_nat : nat.

Extract Constant segev_fuel_nat => "10".

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

(* From QuickChick Require Import Tyche.
Check size.
Locate size. Check size.

Derive Sized for term.
Derive Sized for type.
Derive Sized for list. *)

Extract Constant defNumTests => "10000".

Definition a := 3.
(* 
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
. *)

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

Compute @decOpt (@typing' [] (Const 0) N) _ 1.

(*QuickCheck prop'.*)
Check @arbitraryST.

(*Definition prop'' := 
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
    end)).*)

(*QuickCheck prop''.*)



Search typing'.


Derive Sized for type.
Derive Sized for term.
Derive Sized for list.
Derive Sized for option.

(*Derive ArbitrarySizedSuchThat for (fun e => step e e').*)

(*Definition prop_testing_decopt_step := 
  forAll arbitrary (fun e' =>
  forAll (@arbitraryST _ (fun e => step e e') _) (fun (e : option term) =>
    collect (size e') ((
     (
      match e with
      | Some e => collect (size e)
          (match @decOpt (@step e e') _ 7 with
             | Some res => checker res
             | None => checker false
          end
          )
      | None => checker tt
      end))))).
            

QuickCheck prop_testing_decopt_step.*)

QuickChickDebug Debug On.


Theorem preservation : forall e e' Gamma tau,
    typing' Gamma e tau ->
    step e e' ->
    typing' Gamma e' tau.
Proof.
  Extract Constant defSize => "3".
  typeclass_bindings GenSizedSuchThat typing'.
  Derive Used Inds typing'.
  Derive Used Inds step.
  Derive Density step 0. Print step. Print typing'. Print subst.
  Derive Density typing' 2. Derive Density bind 2. Derive Density app_free 0.

  print_all_bindings.
  valid_bindings.
  derive_index 3.
  derive_and_quickchick_index 2.
  Derive Density step 0.
  Derive Density typing' 1.
  Derive GenSizedSuchThat for (fun x2 => subst x0 x1 x2 x3).
  Derive GenSizedSuchThat for (fun x0 => value x0).
  derive_index 3.
  QuickChickDebug Debug On.
  derive_and_quickchick_index 3.
  typeclass_bindings GenSizedSuchThat typing'.
  Extract Constant defSize        => "2".
  QuickCheck (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
   (fun tau =>
    QuickChick.Checker.collect (Coq.Init.Datatypes.pair "tau-size"%string (QuickChick.Classes.size tau))
      (QuickChick.Checker.forAll QuickChick.Classes.arbitrary
         (fun Gamma =>
          QuickChick.Checker.collect (Coq.Init.Datatypes.pair "Gamma-size"%string (QuickChick.Classes.size Gamma))
            (QuickChick.Checker.forAll (@QuickChick.DependentClasses.arbitraryST _ (fun e => @typing' Gamma e tau) _)
               (fun e =>
                match e with
                | @Coq.Init.Datatypes.Some _ e =>
                    QuickChick.Checker.collect (Coq.Init.Datatypes.pair "e-size"%string (QuickChick.Classes.size e))
                      (QuickChick.Checker.forAll (@QuickChick.DependentClasses.arbitraryST _ (fun e' => @step e e') _)
                         (fun e' =>
                          match e' with
                          | @Coq.Init.Datatypes.Some _ e' =>
                              QuickChick.Checker.collect (Coq.Init.Datatypes.pair "e'-size"%string (QuickChick.Classes.size e'))
                                (QuickChick.Checker.checker
                                   match @QuickChick.Decidability.decOpt (@typing' Gamma e' tau) _ 7%nat with
                                   | Coq.Init.Datatypes.Some res => res
                                   | Coq.Init.Datatypes.None => Coq.Init.Datatypes.false
                                   end)
                          | _ => QuickChick.Checker.checker Coq.Init.Datatypes.tt
                          end))
                | _ => QuickChick.Checker.checker Coq.Init.Datatypes.tt
                end)))))).


  derive_and_quickchick_index 8. theorem_dependencies. derive_index 5. Search typing'.
  Search step. Check @decOpt. Print term. Compute (@decOpt (step (App (Abs (Id 0)) (Const 0)) (Const 0)) _ 7).
  derive_and_quickchick_index 9.

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
