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
Derive (Arbitrary, Show) for exp.
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
(*quickchick.*)
(*Print theorem.

Print DecOpt_even_I.
QuickChick (sized (fun n => theorem (S (S n)))).


Sample (sized (fun n => GenSizedSuchThat_even_O (4 * (n + 10)))).
 *)
Abort.
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
       

Derive Show for res.

QuickChickDebug Debug Off.

Derive Valid Schedules eval 0 consnum 11 derive "Gen".
Derive Generator for (fun p => plus n m p).
Derive Checker for (plus n m p).
Derive Checker for (notR n m).
Derive Generator for (fun m => le n m).
Derive Generator for (fun n => le n m).
Derive Checker for (le n m).
Derive Checker for (andR a b c).
Derive Checker for (orR a b c).
Derive Checker for (eval a b c d).

Derive Inductive Schedule eval derive "Check" opt "true".

Derive Inductive Schedule eval 0 derive "Gen" opt "true".

Derive Inductive Schedule eval 1 derive "Gen" opt "true".

Derive Show for exp.



Sample ( GenSizedSuchThat_eval_OIII (3) 0 0 (N 4)).


Definition test_cases : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 5);(1,1,N 1) ].

Inductive Elem {A} : A -> list A -> Prop :=
| Elem_Now : forall x l, Elem x (cons x l)
| Elem_Lat : forall x y l, Elem x l -> Elem x (cons y l).
                                          


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
  | And e1 e2 =>
      match evalc e1 x y, evalc e2 x y with
      | Some (B n1), Some (B n2) => Some (B (andb n1 n2))
      | _, _ => None
      end
  | Or e1 e2 =>
      match evalc e1 x y, evalc e2 x y with
      | Some (B n1), Some (B n2) => Some (B (orb n1 n2))
      | _, _ => None
      end
  | Not e =>
      match evalc e x y with
      | Some (B b) => Some (B (negb b))
      | _ => None
      end
  end.

Instance DecEqRes : Dec_Eq res.
Proof. dec_eq. Defined.

Instance DecEqexp : Dec_Eq exp. dec_eq. Defined.

Check (fun ( e : exp) => e = e ?).

Definition exp_eq (e e' : exp)  : bool := e = e' ?.
  

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
      | _, Zero => F
      | Zero, One => T
      | One, One => F
      | P One x, P One y => Lt x y
      | P x One, P One y => Lt x y
      | P x One, P y One => Lt x y
      | P One x, P y One => Lt x y
      | P One x, y => (if exp_eq x y then F else Lt (P One x) y)
      | P x One, y => (if exp_eq x y then F else Lt (P x One) y)
      | x, P One y => (if exp_eq x y then T else Lt x (P One y))
      | x, P y One => (if exp_eq x y then T else Lt x (P y One))
      | e1', e2' => (if exp_eq e1' e2' then F else Lt e1' e2')
      (*| e1', e2' => Lt e1' e2'*)
      end
  | P e1 e2 =>
      match partial_eval e1, partial_eval e2 with
      | Zero, e2' => e2'
      | e1', Zero => e1'
      | e1', e2' => P e1' e2'
      end
  | Not e =>
      match partial_eval e with
      | T => F
      | F => T
      | e' => Not e'
      end
  | And l r =>
      match partial_eval l, partial_eval r with
      | T, r' => r'
      | l', T => l'
      | F, _ => F
      | _, F => F
      | l',r' => And l' r'
      end
  | Or l r =>
      match partial_eval l, partial_eval r with
      | F, r' => r'
      | l', F => l'
      | T, _ => T
      | _, T => T
      | l',r' => Or l' r'
      end
  end.

Theorem partial_eval_correct : forall e x y r, eval e x y r -> eval (partial_eval e) x y r.
quickchick.

Compute partial_eval ((Lt One (P One Y))).
Definition stuck (e : exp) : bool := (e = (partial_eval e)) ? . 

Compute (stuck (ite T X Y)).

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
   match DecOpt_eval_IIII 100000 e x y r
                with
  | Some true => true
  | Some false => false
  | None => false          
  end) ts))).

Definition test_cases' : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 5);(1,1,N 1); (3,6,N 3) ].

Definition max_examples := [(4,2, N 4); (2,5,N 5);(7,1,N 7)].

Extract Constant defNumTests => "100000". 
QuickChick (prop max_examples).

Print test_cases.

Compute partial_eval (ite (Lt (P (P X One) (P One X)) (P X (P (P X X) One))) X Y

  ).

Compute evalc (ite (Lt (P (P X One) (P One X)) (P X (P (P X X) One))) X Y) 6 7.


Print DecOpt_eval_IIII.

Derive Inductive Schedule eval 0 3 derive "Gen" opt "true".
(*

Compute (DecOpteval_IIII 10 ( (Lt One Zero)) 4 2 (B false)).
Compute (DecOpteval_IIII 10 ( (T)) 4 2 (B false)).
Print andBind.*)

Merge (fun e => eval e x y r) With (fun e => eval e x' y' r') As EVAL.

Derive Inductive Schedule EVAL 6 derive "Gen" opt "true".
Check shrinking.
Sample (GenSizedSuchThat_EVAL_IIIIIIO 3 1 0 (N 1) 1 2 (N 2)).

Derive Valid  Schedules EVAL 6 consnum 5 derive "Gen".
 

Merge (fun e => EVAL x y r x' y' r' e) With (fun e => eval e x'' y'' r'') As EVAL'.

Print EVAL'.

Derive EnumSized for exp.

Time Derive Inductive Schedule EVAL' 9  derive "Gen" opt "true".

Sample (GenSizedSuchThat_EVAL'_IIIIIIIIIO 3 4 2 (N 4) 2 5 (N 5) 1 1 (N 1)).

Derive Inductive Schedule eval derive "Check" opt "true".

Definition prop' (ts : list (nat * nat * res)) :=
  let genSize := 3 in
  let defElemIgnore := (0,0, N 0) in
  forAll (elems_ defElemIgnore ts) (fun '(x,y,r) =>
  forAll (elems_ defElemIgnore ts) (fun '(x',y',r') =>
  forAll (elems_ defElemIgnore ts) (fun '(x'',y'',r'') =>                                                                      
                                                                          
  forAllShrinkMaybe (GenSizedSuchThat_EVAL'_IIIIIIIIIO genSize x y r x' y' r' x'' y'' r'') shrinker (fun e => 
  negb (forallb (fun '(x,y,r) => 
  match DecOpt_eval_IIII 100 e x y r
                with
  | Some true => true
  | _ => false
  end) ts))))).

Definition test_cases'' : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 5);(1,1,N 1); (0,0,N 0) ].

Extract Constant defNumTests => "100000". 
QuickChick ( (prop' test_cases'')).


Time Compute (DecOpt_eval_IIII 10000 (ite (Lt One Zero) (Or One (ite T (Or F X) One)) (ite T Y X)) 4 2 (N 4)).
(*QuickChick (prop' [(1,1,B true); (3,3,B true); (0,1,B false); (0,2,B false); (0,0,B true); (2,0,B false)]).*)

Derive Inductive Schedule eval 1 2 3 derive "Gen" opt "true".


Derive Valid Schedules EVAL' 9 consnum 8 derive "Gen".

Derive Density EVAL 6 derive "Gen".

Compute (evalc (ite (Lt X Y) Y X) 1 1).
Definition eqe x y := ite (Lt x y) F (ite (Lt y x) F T).

Compute (evalc (eqe X Y) 1 1).

(* And, Or *)
