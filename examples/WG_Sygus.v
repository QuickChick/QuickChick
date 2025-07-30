From QuickChick Require Import QuickChick.
Require Import List.
Import ListNotations.

Inductive exp :=
| X
| Y
| Zero
| One
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

Inductive eval : exp -> nat -> nat -> res -> Prop :=
| Eval_X : forall x y, eval X x y (N x)
| Eval_Y : forall x y, eval Y x y (N y)       
| Eval_0 : forall x y, eval Zero x y (N 0)
| Eval_1 : forall x y, eval One x y (N 1)
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
| Eval_Lt_T : forall x y e1 e2 n1 n2,
    le (S n1) n2 -> 
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B true)
| Eval_Lt_F : forall x y e1 e2 n1 n2,
    le n2 n1 ->     
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B false).

Derive Show for res.
Derive Show for exp.
#[export] Instance dec_res (r1 r2 : res) : Dec (r1 = r2).
Proof. dec_eq. Defined.
#[export] Instance dec_exp (e1 e2 : exp) : Dec (e1 = e2).
Proof. dec_eq. Defined.

Merge (fun e => eval e x1 y1 r1) With
                                 (fun e => eval e x2 y2 r2) As EVAL.

Theorem foo :
  forall e, eval e 4 2 (N 4) ->
            eval e 2 5 (N 5) ->
            eval e 1 1 (N 1) ->
            e = X.
Extract Constant defNumTests => "1".
quickchick.
Extract Constant defNumTests => "1000000".
QuickChick (theorem 2).



