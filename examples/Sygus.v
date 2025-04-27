From QuickChick Require Import QuickChick.
Require Import List.
Import ListNotations.

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

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS n : odd n -> even (S n)
with odd : nat -> Prop :=
| odd1 : odd 1
| oddS n : even n -> odd (S n)
.

Derive Inductive Schedule even 0 derive "Gen" opt "true".

Print GenSizedSuchThat_even_O.
Print sizedGen. Print run.

Theorem even_SS : forall n, even n -> even (S (S n)).
quickchick.
Print theorem.

Print DecOpt_even_I.
QuickChick (sized (fun n => theorem (S (S n)))).


Sample (sized (fun n => GenSizedSuchThat_even_O (4 * (n + 10)))).

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
 (* quickchick.
  QuickChick (sized theorem).*)
  Extract Constant defNumTests => "100000".
  Abort.

Print checker.

QuickChick checker.

(*Derive Inductive Schedule plus 2 derive "Enum" opt "true".*)


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
(* | Eval_Not : forall x y e b,
   eval e x y (B b) ->
   eval (Not e) x y (B (negb b)) *) 
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

QuickChickDebug Debug Off.

Derive Valid Schedules eval 0 consnum 6 derive "Gen".

Derive Inductive Schedule eval 0 derive "Gen" opt "true".

Derive Inductive Schedule eval 1 derive "Gen" opt "true".

Sample (sized (fun n => GenSizedSuchThat_le_IO n 100)).

Derive Show for exp.

Sample (sized (fun n => GenSizedSuchThat_eval_OIII n 1 3 (N 4))).


Print GenSizedSuchThat_le_IO.
(*Derive Generator for (fun y => le x y).
Derive Generator for (fun e => eval e x y r).*)

(*
QuickChickDebug Debug On.
Derive Enumerator for (fun r => eval e x y r).
Derive Checker for (eval e x y r).
 *)
Fixpoint evalc (e : exp) (x y : nat) : option res :=
  match e with
  | X => Some (N x)
  | Y => Some (N y)
  | Zero => Some (N 0)
  | One => Some (N 1)
  | ite e e1 e2 =>
      match evalc e x y with
      | Some (B true) => evalc e1 x y
      | Some (B false) => evalc e2 x y
      | _ => None
      end
  | T => Some (B true)
  | F => Some (B false)
  | Lt e1 e2 =>
      match evalc e1 x y, evalc e2 x y with
      | Some (N n1), Some (N n2) => Some (B (Nat.ltb n1 n2))
      | _, _ => None
      end
  | P e1 e2 =>
      match evalc e1 x y, evalc e2 x y with
      | Some (N n1), Some (N n2) => Some (N (n1 + n2))
      | _, _ => None
      end
  | _ => None
  end.


Instance DecEqRes : Dec_Eq res.
Proof. dec_eq. Defined.

Instance DecEqexp : Dec_Eq exp. dec_eq. Defined.

Check (fun ( e : exp) => e = e ?).
  

Fixpoint partial_eval (e : exp) : exp :=
  match e with
  | X => X
  | Y => Y
  | Zero => Zero
  | One => One
  | ite e e1 e2 =>
      match partial_eval e with
      | T => partial_eval e1
      | F => partial_eval e2
      | e' => ite e' (partial_eval e1) (partial_eval e2)
      end
  | T => T
  | F => F
  | Lt e1 e2 =>
      match partial_eval e1, partial_eval e2 with
      | Zero, Zero => F
      | Zero, One => T
      | One, Zero => F
      | One, One => F
      | P One x, P One y => Lt x y
      | P x One, P One y => Lt x y
      | P x One, P y One => Lt x y
      | P One x, P y One => Lt x y
    (*  | P One x, y => (if (x = y) ? then F else Lt (P One x) y)
      | P x One, y => (if (x = y) ? then F else Lt (P x One) y)
      | x, P One y => (if (x = y) ? then T else Lt x (P One y))
      | x, P y One => (if (x = y) ? then T else Lt x (P y One))
      | e1', e2' => (if (e1' = e2') ? then F else Lt e1' e2')*)
      | e1', e2' => Lt e1' e2'
      end
  | P e1 e2 =>
      match partial_eval e1, partial_eval e2 with
      | Zero, e2' => e2'
      | e1', Zero => e1'
      | e1', e2' => P e1' e2'
      end
  | _ => e
  end.

Print partial_eval.

Definition stuck (e : exp) : bool := (e = (partial_eval e)) ? . 

Compute (stuck (ite X X Y)).

Definition shrinker e := if stuck e then [] else [partial_eval e].

(*Definition g :=
  genSizedST (fun e => eval e 2 4 (N 4)).*)


Search shrink.

Definition forAllShrinkMaybe {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G (option A)) (shrinker : A -> list A) (pf : A -> prop) : Checker :=
  bindGen gen (fun mx =>
                 match mx with
                 | Some x => shrinking shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))
                 | None => checker tt
                 end
              ).

Derive Inductive Schedule eval derive "Check" opt "true".

Derive Show for exp. 
Definition prop (ts : list (nat * nat * res)) :=
  let genSize := 5 in
  let defElemIgnore := (0,0, N 0) in
  forAll (elems_ defElemIgnore ts) (fun '(x,y,r) =>
  forAllShrinkMaybe (GenSizedSuchThat_eval_OIII genSize x y r) shrinker (fun e => 
  negb (forallb (fun '(x,y,r) => 
  match DecOpt_eval_IIII 10 e x y r
                with
  | Some true => true
  | _ => false
  end) ts))).

Definition test_cases : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 5);(1,1,N 1) ].

Extract Constant defNumTests => "100000". 
QuickChick (prop test_cases).

Print DecOpt_eval_IIII.

Derive Inductive Schedule eval 0 3 derive "Gen" opt "true".
(*

Compute (DecOpteval_IIII 10 ( (Lt One Zero)) 4 2 (B false)).
Compute (DecOpteval_IIII 10 ( (T)) 4 2 (B false)).
Print andBind.*)

Merge (fun e => eval e x y r) With (fun e => eval e x' y' r') As EVAL.

Derive Inductive Schedule EVAL 6 derive "Gen" opt "true".

(*Inductive EVAL : res -> res -> exp -> Prop :=
  | Eval_Lt_FEval_Lt_F : forall  (e1' e2' : exp) (n1' n2' n1 n2 : nat),
                         n2' <= n1' ->
                         n2 <= n1 ->
                         EVAL (N n2) (N n2') e2' ->
                         EVAL (N n1) (N n1') e1' -> EVAL (B false) (B false) (Lt e1' e2')
  | Eval_Lt_FEval_Lt_T : forall  (e1' e2' : exp) (n1' n2' n1 n2 : nat),
                         S n1' <= n2' ->
                         n2 <= n1 ->
                         EVAL (N n2) (N n2') e2' ->
                         EVAL (N n1) (N n1') e1' -> EVAL (B false) (B true) (Lt e1' e2')
  | Eval_Lt_TEval_Lt_F : forall  (e1' e2' : exp) (n1' n2' n1 n2 : nat),
                         n2' <= n1' ->
                         S n1 <= n2 ->
                         EVAL (N n2)  (N n2') e2' ->
                         EVAL (N n1)  (N n1') e1' -> EVAL (B true) (B false) (Lt e1' e2')
  | Eval_Lt_TEval_Lt_T : forall (e1' e2' : exp) (n1' n2' n1 n2 : nat),
                         S n1' <= n2' ->
                         S n1 <= n2 ->
                         EVAL (N n2) (N n2') e2' ->
                         EVAL (N n1) (N n1') e1' -> EVAL (B true) (B true) (Lt e1' e2')
  | Eval_FEval_F : EVAL (B false) (B false) F
  | Eval_TEval_T : EVAL (B true)  (B true) T 
 (** | Eval_ITE_FEval_ITE_F : forall (e' e1' e2' : exp) (r' : res) (r : res),
                           EVAL r r' e2' -> EVAL (B false) (B false) e' -> EVAL r r' (ite e' e1' e2')
  | Eval_ITE_FEval_ITE_T : forall (e' e1' e2' : exp) (r' : res) (r : res),
                           eval e1' r' ->
                           eval e2' x y r -> EVAL x y (B false) x' y' (B true) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_ITE_TEval_ITE_F : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           eval e2' x' y' r' ->
                           eval e1' x y r -> EVAL x y (B true) x' y' (B false) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_ITE_TEval_ITE_T : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           EVAL x y r x' y' r' e1' -> EVAL x y (B true) x' y' (B true) e' -> EVAL x y r x' y' r' (ite e' e1' e2')**)
  | Eval_1Eval_1 :  EVAL (N 1) (N 1) One
| Eval_0Eval_0 :  EVAL  (N 0) (N 0) Zero .

Derive  Schedules EVAL 2 consnum 2 derive "Gen".

Derive Inductive Schedule le 0 1 derive "Gen" opt "true". Print GenSizedSuchThatle_OO.




Derive Inductive Schedule EVAL 2 derive "Gen" opt "true".*)



Inductive EVAL : nat -> nat -> res -> nat -> nat -> res -> exp -> Prop :=
  | Eval_Lt_FEval_Lt_F : forall (x' y' : nat) (e1' e2' : exp) (n1' n2' x y n1 n2 : nat),
                         n2' <= n1' ->
                         n2 <= n1 ->
                         EVAL x y (N n2) x' y' (N n2') e2' ->
                         EVAL x y (N n1) x' y' (N n1') e1' -> EVAL x y (B false) x' y' (B false) (Lt e1' e2')
  | Eval_Lt_FEval_Lt_T : forall (x' y' : nat) (e1' e2' : exp) (n1' n2' x y n1 n2 : nat),
                         S n1' <= n2' ->
                         n2 <= n1 ->
                         EVAL x y (N n2) x' y' (N n2') e2' ->
                         EVAL x y (N n1) x' y' (N n1') e1' -> EVAL x y (B false) x' y' (B true) (Lt e1' e2')
  | Eval_Lt_TEval_Lt_F : forall (x' y' : nat) (e1' e2' : exp) (n1' n2' x y n1 n2 : nat),
                         n2' <= n1' ->
                         S n1 <= n2 ->
                         EVAL x y (N n2) x' y' (N n2') e2' ->
                         EVAL x y (N n1) x' y' (N n1') e1' -> EVAL x y (B true) x' y' (B false) (Lt e1' e2')
  | Eval_Lt_TEval_Lt_T : forall (x' y' : nat) (e1' e2' : exp) (n1' n2' x y n1 n2 : nat),
                         S n1' <= n2' ->
                         S n1 <= n2 ->
                         EVAL x y (N n2) x' y' (N n2') e2' ->
                         EVAL x y (N n1) x' y' (N n1') e1' -> EVAL x y (B true) x' y' (B true) (Lt e1' e2') 
  | Eval_FEval_F : forall x' y' x y : nat, EVAL x y (B false) x' y' (B false) F
  | Eval_TEval_T : forall x' y' x y : nat, EVAL x y (B true) x' y' (B true) T 
  | Eval_ITE_FEval_ITE_F : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           EVAL x y r x' y' r' e2' -> EVAL x y (B false) x' y' (B false) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_ITE_FEval_ITE_T : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           eval e1' x' y' r' ->
                           eval e2' x y r -> EVAL x y (B false) x' y' (B true) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_ITE_TEval_ITE_F : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           eval e2' x' y' r' ->
                           eval e1' x y r -> EVAL x y (B true) x' y' (B false) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_ITE_TEval_ITE_T : forall (x' y' : nat) (e' e1' e2' : exp) (r' : res) (x y : nat) (r : res),
                           EVAL x y r x' y' r' e1' -> EVAL x y (B true) x' y' (B true) e' -> EVAL x y r x' y' r' (ite e' e1' e2')
  | Eval_1Eval_1 : forall x' y' x y : nat, EVAL x y (N 1) x' y' (N 1) One
  | Eval_0Eval_0 : forall x' y' x y : nat, EVAL x y (N 0) x' y' (N 0) Zero 
  | Eval_YEval_Y : forall x' y' x y : nat, EVAL x y (N y) x' y' (N y') Y
| Eval_XEval_X : forall x' y' x y : nat, EVAL x y (N x) x' y' (N x') X .

Merge (fun e => EVAL x y r x' y' r' e) With (fun e => eval e x'' y'' r'') As EVAL'.

Print EVAL'.

Time Derive Inductive Schedule EVAL 6  derive "Enum" opt "true".



Check EnumSizedSuchThatEVAL_IIIIIIO.

Compute (EnumSizedSuchThatEVAL_IIIIIIO 2 4 2 (N 4) 3 5 (N 5)).

Print EnumSizedSuchThatEVAL_IIIIIIO.

Time Derive Inductive Schedule EVAL 6  derive "Gen" opt "true".



Check GenSizedSuchThatEVAL_IIIIIIO.

Sample (GenSizedSuchThatEVAL_IIIIIIO 2 4 2 (N 4) 3 5 (N 5)).

Definition prop' (ts : list (nat * nat * res)) :=
  let genSize := 5 in
  let defElemIgnore := (0,0, N 0) in
  forAll (elems_ defElemIgnore ts) (fun '(x,y,r) =>
  forAll (elems_ defElemIgnore ts) (fun '(x',y',r') =>
                                                                          
  forAllShrinkMaybe (GenSizedSuchThatEVAL_IIIIIIO genSize x y r x' y' r') shrinker (fun e => 
  negb (forallb (fun '(x,y,r) => 
  match DecOpteval_IIII 10 e x y r
                with
  | Some true => true
  | _ => false
  end) ts)))).

Definition test_cases' : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 1);(1,1,N 1) ].

Extract Constant defNumTests => "100000". 
QuickChick (prop' test_cases').


Merge (fun e => eval e x1 y1 r1) With (fun e => eval e x2 y2 r2) As EVAL.

Print EVAL.


Compute (EnumSizedSuchThateval_IIIO 3 (LT One Zero)

Compute (DecOpteval_IIII 10 (ite (Lt One Zero) (Or One (ite T (Or F X) One)) (ite T Y X)) 4 2 (N 4)).
QuickChick (prop [(1,1,B true); (3,3,B true); (0,1,B false); (0,2,B false); (0,0,B true); (2,0,B false)]).

Derive Inductive Schedule eval 3 derive "Gen" opt "true".


Derive Valid Schedules eval 3 consnum 8.

Derive Density eval 0.

Compute (evalc (ite (Lt X Y) Y X) 1 1).
Definition eqe x y := ite (Lt x y) F (ite (Lt y x) F T).

Compute (evalc (eqe X Y) 1 1).

(* And, Or *)
