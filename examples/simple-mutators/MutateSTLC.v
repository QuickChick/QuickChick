From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

Inductive Typ :=
| TBool : Typ
| TFun  : Typ -> Typ -> Typ
.

Derive (Show, Sized) for Typ.

Inductive Expr :=
| Var   : nat -> Expr
| Bool  : bool -> Expr
| Abs   : Typ -> Expr -> Expr
| App   : Expr -> Expr -> Expr
.

Derive (Show, Sized) for Expr.

Definition Ctx := list Typ.

Fixpoint typ_eqb (t1 t2: Typ) : bool :=
    match t1, t2 with
    | TBool, TBool => true
    | TBool, TFun _ _ => false
    | TFun _ _, TBool => false
    | TFun t1' t1'', TFun t2' t2'' => (typ_eqb t1'  t2') && (typ_eqb t1'' t2'')
    end.
  
Notation "A == B" := (typ_eqb A B) (at level 100, right associativity).


Fixpoint getTyp (ctx: Ctx) (e: Expr) : option Typ :=
    match e with
    | (Var n) =>
        if (0 <=? n) && ((List.length ctx) <? n) then (List.nth_error ctx (n))
        else  None
    | (Bool _) => 
        Some TBool
    | (Abs t e) =>
        t' <- getTyp (t::ctx) e ;;
        Some (TFun t t')
    | (App e1 e2) => 
        t1' <- getTyp ctx e1 ;;
        match t1' with
        | TFun t11 t12 =>
            t2 <- getTyp ctx e2 ;;
            if t11 == t2 then Some t12 else None
        | _ => None
        end
    end
.

Definition typeCheck (ctx: Ctx) (e: Expr) (t: Typ) : bool :=
    match getTyp ctx e with
    | Some t' => t == t'
    | None => false
    end
.



Definition shift  (d: Z) (ex: Expr) : Expr :=
    let fix go (c: Z) (e: Expr):=
        match e with 
        | Var n =>
            (*! *)
            if n <? Z.to_nat c then Var n
            else Var (n + Z.to_nat d)
            (*!! shift_var_none *)
            (*!
            Var n
            *)
            (*!! shift_var_all *)
            (*!
            Var (n + d)
            *)
            (*!! shift_var_leq *)
            (*!
            if n <=? c then Var n
            else Var (n + d)
            *)
        | Bool b => 
            Bool b
        | Abs t e =>
            (*! *)
            Abs t (go (1 + c)%Z e)
            (*!! shift_abs_no_incr *)
            (*!
            Abs t (go c e)
            *)
        | (App e1 e2) => 
            App (go c e1) (go c e2)
        end in
    go 0%Z ex
.



Fixpoint subst  (n: nat) (s: Expr) (e: Expr) : Expr :=
    match n, s, e with 
    | n, s, (Var m) =>
        (*! *)
        if m =? n then s
        else Var m
        (*!! subst_var_all *)
        (*!
        s
        *)
        (*!! subst_var_none *)
        (*!
        Var m
        *)
    | _, _, (Bool b) => Bool b
    | n, s, (Abs t e) =>
        (*! *)
        Abs t (subst (n + 1) (shift 1 s) e)
        (*!! subst_abs_no_shift *)
        (*!
        Abs t (subst (n + 1) s e)
        *)
        (*!! subst_abs_no_incr *)
        (*!
        Abs t (subst n (shift 1 s) e)
        *)
    | n, s, (App e1 e2) => App (subst n s e1) (subst n s e2)
    end.



Definition substTop (s: Expr) (e: Expr) : Expr :=
    (*! *)
    shift (-1) (subst 0 (shift 1 s) e)
    (*!! substTop_no_shift *)
    (*!
    subst 0 s e
    *)
    (*!! substTop_no_shift_back *)
    (*!
    subst 0 (shift 1 s) e
    *)
.

Definition fromMaybe {A} (a: A) (a' : option A) : A :=
    match a' with
    | Some value => value
    | None => a
    end.

Fixpoint pstep  (e: Expr) : option Expr :=
    match e with
    | (Abs t e) => 
        e' <- (pstep e) ;;
        Some (Abs t e')
    | (App (Abs _ e1) e2) =>
        let e1' := fromMaybe e1 (pstep e1) in
        let e2' := fromMaybe e2 (pstep e2) in
            Some (substTop e2' e1')
    | (App e1 e2) =>
        match pstep e1, pstep e2 with
        | None, None => None
        | me1, me2 =>
            let e1' := fromMaybe e1 me1 in
            let e2' := fromMaybe e2 me2 in
                Some (App e1' e2')
        end
    | _ => None
    end.


Fixpoint multistep (f: nat) (step: (Expr -> option Expr))  (e: Expr) : option Expr :=
    match f with
    | O => None
    | S f' =>
        match step e with
        | None => Some e
        | Some e' => multistep f' step e'
        end
    end.


Fixpoint isNF  (e: Expr) : bool :=
    match e with 
    | Var _ => true
    | Bool _ => true
    | Abs _ e => isNF e
    | App (Abs _ _) _ => false
    | App e1 e2 => isNF e1 && isNF e2
    end.

Definition mt (e: Expr) : option Typ := 
    getTyp nil e
.

Definition isJust {A} (a: option A) : bool :=
    match a with
    | Some _ => true
    | None => false
    end
.


Definition mtypeCheck (e: option Expr) (t: Typ) : bool :=
    match e with
    | Some e' => typeCheck nil e' t
    | None => true
    end.

Definition prop_SinglePreserve (e: Expr) : option bool :=
  isJust (mt e) -=> 
    t' <- (mt e) ;;
    Some (mtypeCheck (pstep e) t')
.


Definition prop_MultiPreserve (e: Expr) : option bool :=
  isJust (mt e) -=> 
    t' <- mt e ;;
    Some (mtypeCheck (multistep 40 pstep e) t')
.




Fixpoint sizeSTLC (e: Expr) : nat :=
    match e with
    | (Abs _ e) => 1 + sizeSTLC e
    | (App e1 e2) => 1 + sizeSTLC e1 + sizeSTLC e2
    | _ => 1
    end
.

(* instances *)

(* bool *)
Derive (Arbitrary, Sized) for bool.
#[local] Instance MutateBool : Mutate bool :=
  {| mutate b := oneOf_ (returnGen b) [returnGen true; returnGen false] |}.
#[local] Instance FuzzyBool : Fuzzy bool :=
  {| fuzz b := oneOf_ (returnGen b) [returnGen true; returnGen false] |}.

(* nat *)

(* 0 = 50%, 1 = 25%, 2 = 17.5%, ... up to n *)
#[local] Program Instance GenSizedNat : GenSized nat :=
    {|
        arbitrarySized n :=
            let f := fix f n :=
                match n with
                | O => returnGen O
                | S n' =>
                    oneOfT_ (fun _ => returnGen n)
                        [ fun _ => returnGen O;  (* here *)
                          fun _ => fmap S (f n') (* there*) ]
                end
            in f n
        ;
    |}.

#[local] Instance GenNat : Gen nat :=
    (* {| arbitrary := choose (0, 1) |}. *)
    {| arbitrary := arbitrarySized 3 |}.

#[local] Instance MutateNat : Mutate nat :=
  {| mutate n := choose (n - 1, n + 1) |}.
#[local] Instance FuzzyNat : Fuzzy nat :=
  {| fuzz n := choose (n - 1, n + 1) |}.
Derive (Sized) for nat.

(* type *)
Derive (Arbitrary, Sized, Fuzzy, Mutate) for Typ.

(* expr *)
Derive (Arbitrary, Sized, Fuzzy, Mutate) for Expr.

(* Sample (fuzz (Abs TBool (Var 0))). *)
(* Sample (mutate (Abs TBool (Var 0))). *)

(* checkers to test *)

Definition test_prop_SinglePreserve :=
  forAll arbitrary (fun (e: Expr) =>
    prop_SinglePreserve e).

Definition test_prop_MultiPreserve :=
    forAll arbitrary (fun (e: Expr) =>
        prop_MultiPreserve e).

(* fuzzing *)

Print GenSized.
Sample (@arbitrarySized nat _ 100).
Check Nat.mul.

ManualExtract Typ.
ManualExtract Expr.
QuickChickDebug Debug On.

Definition make_fuzzer_fuzz {A} `{Gen A} `{Fuzzy A} `{Show A} prop (_ : unit) := 
    @fuzzLoop A arbitrary fuzz show prop.
Definition make_fuzzer_mutate {A} `{Gen A} `{Mutate A} `{Show A} prop (_ : unit) := 
    @fuzzLoop A arbitrary mutate show prop.

Definition prop_tmp (b : bool) := Some b.

(* fuzzing: prop_SinglePreserve *)

(* FuzzChick prop_SinglePreserve (make_fuzzer_fuzz prop_SinglePreserve tt). *)
(* ==> 1. Passed 10000 tests (11719 discards) *)
(* ==> 2. Passed 10000 tests (12769 discards) *)
(* ==> 3. Passed 10000 tests (11145 discards) *)

FuzzChick prop_SinglePreserve (make_fuzzer_mutate prop_SinglePreserve tt).
(* ==> 1. Passed 10000 tests (19549 discards) *)
(* ==> 2. Passed 10000 tests (19341 discards) *)
(* ==> 3. Passed only 9996 tests; Discarded: 20000 *)
(* ==> 3. Passed 10000 tests (19541 discards) *)
(* ==> 3.1 Passed 10000 tests (19525 discards) // weight_rec_ind = 2^size *)
(* ==> 3.2 Passed 10000 tests (18934 discards) // weight_rec_ind = 4^size *)
(* ==> 3.3 Passed 10000 tests (18840 discards) // weight_rec_ind = 8^size *)
(* ==> 3.4 Passed 10000 tests (18289 discards) // weight_rec_ind = 2^size; weight_rec_nonind = 16 *)


(* Definition fuzzer :=
    fun (_ : unit) => fuzzLoop arbitrary mutate show prop_MultiPreserve.

FuzzChick prop_MultiPreserve (make_fuzzer_mutate prop_MultiPreserve tt).
*)
