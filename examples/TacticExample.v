Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
From Coq Require Import Nat.
From Coq Require Import Arith.Arith.
(*From Coq Require Import Bool.Bool.*)
(*Require Export Coq.Strings.String.*)
From Coq Require Import Logic.FunctionalExtensionality.
(*From Coq Require Import Lists.List.*)
(*Import ListNotations.*)
Set Default Goal Selector "!".

Definition to_be_generated :=
  forAll arbitrary (fun x =>
  forAll arbitrary (fun y =>                      
  if (x = y)? then checker ((x = 0)?)
  else checker tt)).

QuickChickDebug Debug On.
Theorem foo : forall (x y : nat) , x < 8.
Proof. quickchick. Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. quickchick. Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. quickchick. Admitted.

Local Open Scope nat_scope.

Search (nat -> nat -> bool).
Theorem plus_leb_compat_l : forall (n m p : nat),
  (Nat.leb n m = true) -> (((p + n) <=? (p + m)) = true).
Proof. quickchick. Admitted.

(* ################################################################# *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Derive (Arbitrary, Show) for bin.

Fixpoint bineq (n m : bin) : bool :=
  match n, m with
  | Z, Z => true
  | B0 n, B0 m => bineq n m
  | B1 n, B1 m => bineq n m
  | _,_ => false
  end.

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => double (bin_to_nat m')
  | B1 m' => S (double (bin_to_nat m'))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof. quickchick. Admitted.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof. quickchick. Admitted.
(* ################################################################# *)
Module NatList.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Derive Show for natlist.
Derive Arbitrary for natlist.
#[global] Instance Dec_eq_natlist (l l' : natlist) : Dec (l = l').
Proof. dec_eq. Defined.

Fixpoint app (l l' : natlist) : natlist :=
  match l with
  | nil => l'
  | cons h l => cons h (app l l')
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.

Theorem app_length : forall l1 l2 : natlist,
  length (app l1 l2) = ((length l1) + (length l2)).
Proof. quickchick. Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof. quickchick. Admitted.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof. quickchick. Admitted.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof. quickchick. Admitted.

End NatList.

(*From Coq Require Import Strings.String.*)
Module STLC.

(* ================================================================= *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
#[local] Hint Unfold x : core.
#[local] Hint Unfold y : core.
#[local] Hint Unfold z : core.


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

(*Derive show and Arbitrary*)
Derive Show for ty.
Derive Arbitrary for ty.
Derive Show for tm.
Derive Arbitrary for tm.
Derive Show for value.
Derive Arbitrary for value.

(*Create Dec eq instances*)
#[global] Instance Dec_eq_ty (T T' : ty) : Dec (T = T').
Proof. dec_eq. Defined.

#[global] Instance Dec_eq_tm (t t' : tm) : Dec (t = t').
Proof. dec_eq. Defined.

Hint Constructors value : core.

(* ================================================================= *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).
Check <{[x:=true] x}>.


Print tm.
Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var_eq :
      substi s x (tm_var x) s
  | s_var_neq : forall y,
      x <> y ->
      substi s x (tm_var y) (tm_var y)
  | s_abs_eq : forall T e,
      substi s x (tm_abs x T e) (tm_abs x T e)
  | s_abs_neq : forall y T e e',
      x <> y ->
      substi s x e e' ->
      substi s x (tm_abs y T e) (tm_abs y T e')
  | s_app : forall f y f' y',
      substi s x f f' ->
      substi s x y y' ->
      substi s x (tm_app f y) (tm_app f' y')
  | s_true : substi s x tm_true tm_true
  | s_false : substi s x tm_false tm_false
  | s_if : forall b b' t t' f f',
      substi s x b b' ->
      substi s x t t' ->
      substi s x f f' -> 
      substi s x (tm_if b t f) (tm_if b' t' f')
.

Hint Constructors substi : core.

(*Derive show and arbitrary*)
Derive Show for substi.
Derive Arbitrary for substi.

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof. quickchick. Admitted.

(* ================================================================= *)


Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Reserved Notation "Gamma '|--' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).
 Print Grammar constr.
Inductive has_type : (tm -> option ty) -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).



Hint Constructors has_type : core.

(*Derive show and arbitrary*)
Derive Show for has_type.
Derive Arbitrary for has_type.

Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof. quickchick. Admitted.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof. quickchick. Admitted.

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof. quickchick. Admitted.

Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.
Proof. quickchick. Admitted.

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof. quickchick. Admitted.

End STLC.

(* 2023-08-23 11:31 *)
 (* 2023-10-03 16:40 *)
  
 (*
Create a new file, lots of tests: trees, numbers, lists, etc.

Also do preservation in a separate file STLC. 

ADD THIS FILE TO QUICKCHICK TEST SUITE
add the test file to the makefile.

Push to master

Create baseline.

Create a new tactic that prints info about evarmaps environ, relcontext

*)
