Require Import List.
Require Import Omega.
Require Import Utils.
Require Import Labels.
Require Import Instructions.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Vectors.Vector.
Set Implicit Arguments.

(** This file defines the notion of rule, [AllowModify], and the
    associated manipulation, hypotheses...  Defining the simplest
    language you would need to express simple rules: we need to model

    - when the rule applies: [allow : rule_scond]

    - the label of the result value: [labRes : option rule_expr]

      Optional because not all ops return results.

    - the label of the result PC: [labResPC : rule_expr]

*)



Section Rules.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.


(** * Label expressions *)

(** Labels variables *)
Inductive LAB (n: nat) : Type :=
| lab1 : 1 <= n -> LAB n
| lab2 : 2 <= n -> LAB n
| lab3 : 3 <= n -> LAB n
| labpc : LAB n.

Fixpoint nlem (n:nat) (m:nat) : n<=(n+m).
refine
(match m with
| O => _ (le_n n)
| S m' => _ (le_S _ _ (nlem n m'))
end).
intros; omega.
intros; zify; omega.
Qed.

Inductive rule_expr (n: nat) : Type :=
| L_Bot: rule_expr n
| L_Var: LAB n -> rule_expr n
| L_Join: rule_expr n -> rule_expr n -> rule_expr n.

(** Side conditions for rules: the Allow part *)
Inductive rule_scond (n : nat) : Type :=
| A_True: @rule_scond n
| A_LE:  rule_expr n -> rule_expr n -> @rule_scond n
| A_And: @rule_scond n -> @rule_scond n -> @rule_scond n
| A_Or: @rule_scond n -> @rule_scond n -> @rule_scond n
.


(** * Rules *)
(** The allow-modify part of a rule *)
Record AllowModify (n:nat) := almod  {
   allow  : rule_scond n;
   labRes : option (rule_expr n); (* The label of the result value *)
   labResPC : rule_expr n       (* The label of the result PC *)
}.

(** * Rule evaluation *)

(** * Rules Evaluation *)

(*(* eval_var is a mapping from abstract label names to concrete label
values (a context).  The function [apply_rule] below uses this context
to evaluate the rule ([AllowModify]).  *)
Definition mk_eval_var (n:nat) (v1 v2 v3: option T) (pc: T) : LAB n -> T :=
  fun lv =>
    match lv with
        | lab1 => v1
        | lab2 => v2
        | lab3 => v3
        | labpc => Some pc
    end.
********)


Definition mk_eval_var {n:nat} (vs:Vector.t T n) (pc:T) : LAB n -> T :=
fun lv =>
    match lv with
     | lab1 p => nth_order vs p
     | lab2 p => nth_order vs p
     | lab3 p => nth_order vs p
     | labpc => pc
    end.

Fixpoint eval_expr {n:nat} (eval_var:LAB n -> T) (e: rule_expr n) : T :=
match e with
  | L_Bot => bot
  | L_Var labv => eval_var labv
  | L_Join e1 e2 => join (eval_expr eval_var e1) (eval_expr eval_var e2)
end.

(** eval_cond : evaluates a side_condition with given values for the argument *)
Fixpoint eval_cond {n:nat} (eval_var:LAB n -> T) (c: rule_scond n) : bool :=
match c with
  | A_True => true
  | A_And c1 c2 => andb (eval_cond eval_var c1) (eval_cond eval_var c2)
  | A_Or c1 c2 =>  orb (eval_cond eval_var c1) (eval_cond eval_var c2)
  | A_LE e1 e2 => flows (eval_expr eval_var e1) (eval_expr eval_var e2)
end.

(** apply_rule applies the allow-modify r to the given parameters.=
    Returns the (optional) result value label and result PC label,
    or nothing when the side condition fails. *)
Definition apply_rule {n:nat} (r: AllowModify n)
  (vlabs: Vector.t T n) (pclab:T) : option (option T * T) :=
let eval_var := mk_eval_var vlabs pclab in
  match eval_cond eval_var (allow r) with
    | false => None
    | true =>
      let rpc := eval_expr eval_var (labResPC r) in
      let rres :=
        match (labRes r) with
        | Some lres => Some (eval_expr eval_var lres)
        | None => None
        end in
      Some (rres, rpc)
   end.

End Rules.

(** * Cosmetic notations for writing and applying rules *)
Notation "'≪' c1 , e1 , lpc '≫'" := (almod c1 (Some e1) lpc) (at level 95, no associativity).
Notation "'≪' c1 , '__' , lpc '≫'" := (almod c1 None lpc) (at level 95, no associativity).
Notation "'LabPC'" := (L_Var (labpc _)).
Notation "'Lab1'" := (L_Var (lab1 (nlem _ _))).
Notation "'Lab2'" := (L_Var (lab2 (nlem _ _))).
Notation "'Lab3'" := (L_Var (lab3 (nlem _ _))).
Notation "'BOT'" := (L_Bot _).
Notation "'JOIN'" := L_Join.
Notation "'TRUE'" := (A_True _).
Notation "'AND'" := A_And.
Notation "'OR'" := A_Or.
Notation "'LE'" := A_LE.
Notation "<||>" := (Vector.nil _).
Notation " <| x ; .. ; y |> " := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).
