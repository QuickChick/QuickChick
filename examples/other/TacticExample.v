From QuickChick Require Import QuickChick.
From Coq Require Import Nat Arith.

Extract Constant Test.defNumTests => "1000".

Definition to_be_generated :=
  forAll arbitrary (fun x =>
  forAll arbitrary (fun y =>
  if (x = y)? then checker ((x = 0)?)
  else checker tt)).

QuickChickDebug Debug On.

Inductive fooo : nat -> nat -> Prop :=
| A : fooo 0 0
| B n : fooo n n -> fooo (S n) n.

Derive DecOpt for (fooo n m).

Derive GenSizedSuchThat for (fun x => fooo x m).
Derive GenSizedSuchThat for (fun k => fooo x k).

Theorem foo : forall (x y : nat) , fooo x y -> fooo x x -> fooo y x -> fooo 0 x -> x < 8.
Proof. grab_dependencies. derive_and_quickchick. tc_bindings GenSizedSuchThat fooo. quickchick. Admitted.

Inductive PL : nat -> bool -> Prop :=
| wg n b : PL n b
.

Derive ArbitrarySizedSuchThat for (fun n => PL n b).
Derive ArbitrarySizedSuchThat for (fun b => PL n b).

QuickCheck foo.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. quickchick. Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. quickchick. Admitted.

Local Open Scope nat_scope.

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

Inductive natlist : Type :=
  | nil'
  | cons' (n : nat) (l : natlist).

Derive Show for natlist.
Derive Arbitrary for natlist.
#[global] Instance Dec_eq_natlist (l l' : natlist) : Dec (l = l').
Proof. dec_eq. Defined.

Fixpoint app' (l l' : natlist) : natlist :=
  match l with
  | nil' => l'
  | cons' h l => cons' h (app' l l')
  end.

Fixpoint rev' (l:natlist) : natlist :=
  match l with
  | nil'    => nil'
  | cons' h t => app' (rev' t) (cons' h nil')
  end.

Fixpoint length' (l : natlist) : nat :=
  match l with
  | nil' => 0
  | cons' _ t => S (length' t)
  end.

Theorem app_length : forall l1 l2 : natlist,
  length' (app' l1 l2) = ((length' l1) + (length' l2)).
Proof. quickchick. Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev' (app' l1 l2) = app' (rev' l2) (rev' l1).
Proof. quickchick. Admitted.
Theorem rev_involutive : forall l : natlist,
  rev' (rev' l) = l.
Proof. quickchick. Admitted.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev' l1 = rev' l2 -> l1 = l2.
Proof. grab_dependencies. quickchick. Admitted.



(*From Coq Require Import Strings.String.*)


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

Inductive value_set : tm -> Set :=
  | vs_abs : forall x T2 t1,
    value_set <{\x : T2, t1}>
  | vs_true : value_set <{true}>
  | vs_false : value_set <{false}>
.


(*Derive show and Arbitrary*)
Derive Show for ty.
Derive Arbitrary for ty.
Check elems_.
#[export] Instance Gen_var : Gen string :=
  {arbitrary := elems_ x (cons x (cons y (cons z nil)))}.

#[export] Instance shrink_var : Shrink string :=
  {shrink := fun s => match s with
                      | "x"%string => cons y (cons z nil)
                      | "y"%string => cons z nil
                      | _ => nil
                      end}.

Derive Arbitrary for tm.
Derive Show for tm.

(*Create Dec eq instances*)
#[export] Instance Dec_eq_ty (T T' : ty) : Dec (T = T').
Proof.
  constructor.
  unfold ssrbool.decidable.
  decide equality.
Defined.

#[export] Instance Dec_Eq_ty : Dec_Eq ty.
Proof. constructor. intros. apply Dec_eq_ty. Defined.

#[global] Instance Dec_eq_option {X} `{Dec_Eq X} (x x' : option X) : Dec (x = x').
Proof. dec_eq. Defined.

#[global] Instance Dec_eq_tm (t t' : tm) : Dec (t = t').
Proof. dec_eq. Defined.

#[export] Instance Dec_value (t : tm) : Dec (value t).
Proof. destruct t; dec_eq; try (right; intros c; inversion c; fail); left; constructor; constructor.
 Defined.

#[global] Hint Constructors value : core.

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

#[global] Hint Constructors substi : core.

(*Derive show and arbitrary*)

Ltac gen x := generalize dependent x.

#[export] Instance Dec_Eq_tm : Dec_Eq tm.
Proof. dec_eq. Defined.

Theorem substi_exists : forall s x t,  { t' | substi s x t t'}.
Proof.
  intros s x0 t; induction t; intros; eauto.
  - destruct (dec_eq x0 s0); subst; eauto.
  - destruct IHt1, IHt2; eauto.
  - destruct (dec_eq x0 s0), IHt; subst; eauto.
  - destruct IHt1, IHt2, IHt3; eauto.
Qed.
Theorem substi_uniq : forall s x t t' t'', substi s x t t' -> substi s x t t'' -> t' = t''.
Proof.
  intros s x t. induction t; intros; inversion H0; inversion H; subst; eauto;
    try (exfalso; eauto; fail).
  - f_equal.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - f_equal; apply IHt; auto.
  - f_equal.
    + apply IHt1; auto.
    + apply IHt2; auto.
    + apply IHt3; auto.
Qed.

#[export] Instance Dec_substi (s : tm) (x : string) (t t' : tm) : Dec (substi s x t t').
Proof with try (right; intros c; inversion c; subst; eauto; fail).
  dec_eq.
  gen t'. gen x. gen s. induction t; intros; try (right; intros c; inversion c; fail).
  - destruct (dec_eq x0 s).
    + subst. destruct (dec_eq s0 t'); subst...
      left; constructor.
    + destruct (dec_eq (tm_var s) t'); subst...
      left; constructor; auto.
  - destruct (substi_exists s x0 t1), (substi_exists s x0 t2).
    destruct (dec_eq (tm_app x1 x2) t').
    + subst. auto.
    + right. intros c. assert (substi s x0 <{t1 t2}> <{x1 x2}>) by (econstructor; eauto).
      eapply substi_uniq in H; eauto.
  - destruct (dec_eq x0 s).
    + subst. destruct (dec_eq (<{ \ s : t, t0 }>) t'); subst...
      left; constructor.
    + destruct (substi_exists s0 x0 t0). destruct (dec_eq <{ \s : t, x1 }> t'); subst; auto.
      right. intros c.
      assert (substi s0 x0 <{\s : t, t0}> <{\s : t, x1}>) by (econstructor; eauto).
      eapply substi_uniq in H; eauto.
  - destruct (dec_eq tm_true t'); subst... left; auto.
  - destruct (dec_eq tm_false t'); subst... left; auto.
  - destruct (substi_exists s x0 t1), (substi_exists s x0 t2), (substi_exists s x0 t3).
    destruct (dec_eq (tm_if x1 x2 x3) t').
    + subst; auto.
    + right; intros c;
        assert (substi s x0 (tm_if t1 t2 t3) (tm_if x1 x2 x3)) by (econstructor; eauto).
      eapply substi_uniq in H; eauto.
Defined.

(* In the test suite we mainly care that this runs at all, so we lower Test.defNumTests to not waste 5 sec per test. *)
(* Even though most of the tests are discarded. *)
Extract Constant Test.defNumTests => "100".

Theorem substi_correct_l : forall s x (ts t' : tm),
  subst x s ts = t' -> substi s x ts t'.
Proof.
  quickchick. Admitted.

Theorem substi_correct_r : forall s x (ts t' : tm),
  substi s x ts t' -> substi s x ts ts -> subst x s ts = t'.
Proof.
  grab_dependencies. quickchick. Admitted.



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

Derive DecOpt for (step t t').

Reserved Notation "Gamma '|--' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).
(* Print Grammar constr. *)

Definition t_update (Gamma : string -> option ty) (x : string) (T : ty) (x' : string) : option ty :=
  if (x = x')? then Some T else Gamma x'.

Inductive has_type : (string -> option ty) -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      t_update Gamma x T2 |-- t1 \in T1 ->
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
Print tm.

Definition bindop {A B} (ma : option A) (f : A -> option B) : option B :=
  match ma with
  | None => None
  | Some a => f a
  end.
Print ty.
Fixpoint type_eqb (T T' : ty) : bool :=
  match T, T' with
  | Ty_Bool, Ty_Bool => true
  | Ty_Arrow l r, Ty_Arrow l' r' => (type_eqb l l') && (type_eqb r r')
  | _, _ => false
  end.

Theorem type_eq_eqb : forall T T',  type_eqb T T' = true <-> T = T'.
Proof.
  induction T; intros; destruct T'; simpl in *;
    split; intros; auto; try discriminate.
  - rewrite Bool.andb_true_iff in H. destruct H. apply IHT1 in H.
    apply IHT2 in H0. subst; auto.
  - injection H as H. subst; simpl; auto.
    assert (forall T, type_eqb T T = true).
    + induction T; simpl; auto. rewrite IHT3, IHT4; auto.
    + do 2 rewrite H. auto.
  Qed.

Fixpoint type_of (Gamma : string -> option ty) (t : tm) : option ty :=
  match t with
  | tm_var s => Gamma s
  | tm_abs x T e => bindop (type_of (t_update Gamma x T) e)
                      (fun T' => Some <{T -> T'}>)
  | tm_app f e =>
      bindop (type_of Gamma f) (fun T21 =>
       match T21 with
       | <{T2 -> T1}> =>
           bindop (type_of Gamma e) (fun T2' =>
               if type_eqb T2 T2' then Some T1 else None
             )
       | _ => None
       end
        )
  | tm_true | tm_false => Some Ty_Bool
  | tm_if b t f =>
      bindop (type_of Gamma b) (fun Tb =>
      bindop (type_of Gamma t) (fun Tt =>
      bindop (type_of Gamma f) (fun Tf =>
       if andb (type_eqb Tb Ty_Bool) (type_eqb Tt Tf) then
         Some Tt
       else
         None
      )))
  end.

Theorem type_of_correct : forall Gamma t T,
    type_of Gamma t = Some T -> has_type Gamma t T.
Proof.
  intros. gen Gamma; gen T. induction t; intros; simpl 1 in *.
  - constructor; auto.
  - destruct (type_of Gamma t1) eqn: E.
    + simpl in H. rewrite E in H. simpl in H.
      destruct t; try discriminate.
      destruct (type_of Gamma t2) eqn: E'; try discriminate.
      simpl in *.  destruct (type_eqb t3 t) eqn: E''; try discriminate.
      injection H as H. subst. apply type_eq_eqb in E''. subst.
      apply IHt2 in E'. apply IHt1 in E.
      econstructor; eauto.
    + simpl in H. rewrite E in *. discriminate.
  - simpl in *. unfold bindop in H.
    destruct (type_of (t_update Gamma s t) t0) eqn: E; try discriminate.
    injection H as H; subst. constructor.
    apply IHt. apply E.
  - injection H as H; subst. constructor.
  - injection H as H; subst; constructor.
  - simpl in H. destruct (type_of Gamma t1) eqn: E;
      destruct (type_of Gamma t2) eqn: E';
      destruct (type_of Gamma t3) eqn: E''; simpl in H; try discriminate.
    apply IHt1 in E. apply IHt2 in E'. apply IHt3 in E''.
    destruct (type_eqb t <{ Bool }> && type_eqb t0 t4)%bool eqn: E''';
      try discriminate.
    injection H as H; subst. apply Bool.andb_true_iff in E'''.
    destruct E'''. apply type_eq_eqb in H, H0. subst.
    constructor; auto.
Qed.

Definition decopt_has_type (Gamma : string -> option ty) (t : tm) (T : ty) (n : nat) : option bool := bindop (type_of Gamma t) (fun T' => Some ((T = T')?)).

#[export] Instance DecOpt_has_type (Gamma : string -> option ty) (t : tm) (T : ty) : DecOpt (has_type Gamma t T).
Proof.
  constructor. apply decopt_has_type; auto.
  Defined.

#[global] Hint Constructors has_type : core.

Definition empty_env : string -> option ty := fun _ => None.

Lemma canonical_forms_bool : forall term,
  empty_env |-- term \in Bool ->
  value term ->
  (term = <{true}>) \/ (term = <{false}>).
Proof. quickchick. Admitted.

(* Quantifying over the type string -> option for Gamma causes bug.
   Failure(id_of_name called with anonymous).
Lemma weakening_empty : forall Gamma e T,
     empty_env |-- e \in T  ->
     has_type Gamma e T.
Proof. quickchick. Admitted.
*)

(* Dep case not handled yet for exists
Theorem progress : forall e T,
  empty_env |-- e \in T ->
  value e \/ exists e', e --> e'.
Proof. quickchick. Admitted.
 *)

Theorem preservation : forall e e' T,
  empty_env |-- e \in T  ->
  e --> e'  ->
  empty_env |-- e' \in T.
Proof. quickchick. Admitted.
