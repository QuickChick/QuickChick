From QuickChick Require Import QuickChick.
Require Import List.
Import ListNotations.

(* Reduced from examples/Sygus.v. Merge eval with itself, then merge that
   result with eval again. Keep the original evaluation rules and dependency
   relations so recursive scoring sees the same multi-premise constructors. *)

Inductive exp :=
| X
| Y
| Zero
| One
| P (e1 e2: exp)
| ite (e e1 e2 : exp)
| T
| F
| Not (e : exp)
| And (e1 e2 : exp)
| Or (e1 e2 : exp)
| Lt (e1 e2 : exp).

Inductive res :=
| N (n : nat)
| B (b : bool).

Inductive plus : nat -> nat -> nat -> Prop :=
| plus0 n : plus 0 n n
| plusS n m npm : plus n m npm -> plus (S n) m (S npm)
.

QuickChickDebug Debug On.

Theorem plus_is_positive : forall n m npm, plus n m npm -> npm <= m.
Proof.
  quickchick.
 (* QuickChick (sized theorem).
  Extract Constant defNumTests => "100000".*)
  Abort.

(*Derive Inductive Schedule plus 2 derive "Enum" opt "true".*)

Inductive notR : bool -> bool -> Prop :=
| notT : notR true false
| notF : notR false true.

Inductive andR : bool -> bool -> bool -> Prop :=
| andBoth : andR true true true
| andFL b : andR false b false
| andFR b : andR b false false
.

Inductive orR : bool -> bool -> bool -> Prop :=
| orTL b : orR true b true
| orTR b : orR b true true
| orNeither : orR false false false
.

Inductive eval : exp -> nat -> nat -> res -> Prop :=
| Eval_X : forall x y, eval X x y (N x)
| Eval_Y : forall x y, eval Y x y (N y)
| Eval_0 : forall x y, eval Zero x y (N 0)
| Eval_1 : forall x y, eval One x y (N 1)
| Eval_P : forall x y e1 e2 r1 r2 r1p2,
    eval e1 x y (N r1) ->
    eval e2 x y (N r2) ->
    plus r1 r2 r1p2 ->
    eval (P e1 e2) x y (N r1p2) (* Issue 1 *)
| Eval_ITE_T : forall x y e e1 e2 r,
    eval e x y (B true) ->
    eval e1 x y r ->
    eval (ite e e1 e2) x y r
| Eval_ITE_F : forall x y e e1 e2 r,
    eval e x y (B false) ->
    eval e2 x y r ->
    eval (ite e e1 e2) x y r
| Eval_T : forall x y, eval T x y (B true)
| Eval_F : forall x y, eval F x y (B false)
| Eval_Not : forall x y e b b',
   eval e x y (B b) ->
   notR b b' ->
   eval (Not e) x y (B b')
| Eval_Lt_T : forall x y e1 e2 n1 n2,
    le (S n1) n2 ->
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B true)
| Eval_Lt_F : forall x y e1 e2 n1 n2,
    le n2 n1 ->
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B false)
| Eval_And e1 e2 x y bl br ba :
    andR bl br ba ->
    eval e1 x y (B bl) ->
    eval e2 x y (B br) ->
    eval (And e1 e2) x y (B ba)
| Eval_Or e1 e2 x y bl br ba :
    orR bl br ba ->
    eval e1 x y (B bl) ->
    eval e2 x y (B br) ->
    eval (Or e1 e2) x y (B ba).



Merge (fun e => eval e x y r) With (fun e => eval e x' y' r') As EVAL.
Merge (fun e => EVAL x y r x' y' r' e) With (fun e => eval e x'' y'' r'') As EVAL'.
Derive Valid Schedules EVAL' 9 consnum 8 derive "Gen".
