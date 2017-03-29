Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(* id clashes with id function... *)
Inductive ident : Type :=
  Id : nat -> ident.

Theorem eq_id_dec : forall id1 id2 : ident, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   - left. rewrite Heq. reflexivity.
   - right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x); try reflexivity. 
  exfalso; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof. Admitted.

Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : ident -> tm
  | tapp : tm -> tm -> tm
  | tabs : ident -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:ident) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(*
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
*)

(* This can't work *)
(*
Module PartialMap.
 
Definition partial_map (A:Type) := id -> option A.
 
Definition empty {A:Type} : partial_map A := (fun _ => None). 
 
Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.
 
Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.
 
Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->                       
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.
*)

Definition context := list (ident * ty).

Definition empty : context := nil.

Definition extend (Gamma : context) (x:ident) (T : ty) := cons (x, T) Gamma.

Inductive bind : context -> ident -> ty -> Prop :=
  | BindNow   : forall x T Gamma', bind (cons (x, T) Gamma') x T
  | BindLater : forall x x' T T' Gamma', 
                  ~ (x = x') ->
                  bind Gamma' x T -> 
                  bind (cons (x',T') Gamma') x T.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : list (ident * ty) (* context *) -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      bind Gamma x T -> 
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      cons (x, T11) Gamma |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T 

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* Testing starts now *)

From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Set Bullet Behavior "Strict Subproofs".

Instance ident_dep_dec (x y : ident) : Dec (x = y) :=
  { dec := eq_id_dec x y }.

Definition ty_eq_dec : forall (ty1 ty2 : ty), {ty1 = ty2} + {~ (ty1 = ty2)}.
  decide equality.
Qed.

Instance ty_dep_dec (x y : ty) : Dec (x = y) :=
  { dec := ty_eq_dec x y}.

Derive Show for ident.
Derive Show for ty.
Derive Show for tm.
Derive Arbitrary for ty.
Derive Arbitrary for ident.

Derive ArbitrarySizedSuchThat for (fun x => bind Gamma x ty).
Derive ArbitrarySizedSuchThat for (fun tm => has_type Gamme tm ty).

Definition genBool : G (option tm) :=
  @arbitrarySizeST _ (fun tm => has_type 
                                   (cons (Id 0, TBool) 
                                    (cons (Id 1, TArrow TBool TBool) nil))
                                  tm TBool)
                   _ 1.

Sample genBool.

Definition genBool2Bool : G (option tm) := 
  @arbitrarySizeST _ (fun tm => has_type nil tm (TArrow TBool TBool))
                   _ 2.
Sample genBool2Bool.

