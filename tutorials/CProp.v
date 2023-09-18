From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Inductive Ctx :=
| EmptyCtx
| CtxBind : Type -> Ctx -> Ctx.

Fixpoint interpCtx (C : Ctx) : Type :=
  match C with
  | EmptyCtx => unit
  | CtxBind t C => t * interpCtx C
  end.

Inductive CProp : Ctx -> Type :=
  | ForAll : forall A C,
      (interpCtx C -> G A) ->
      (interpCtx C -> A -> G A) ->
      (interpCtx C -> A -> list A) ->
      (interpCtx C -> A -> string) ->
      CProp (CtxBind A C) -> CProp C
  | Predicate : forall C,
      (interpCtx C -> option bool) -> CProp C.

Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition test (x y : nat) : option bool :=
  Some (Nat.ltb y x).
  
Definition example :=
  @ForAll _ EmptyCtx (fun tt => arb) (fun tt n => arb) (fun tt n => nil) (fun tt n => show n) (
  @ForAll _ (CtxBind nat EmptyCtx) (fun '(x, tt) => gen x) (fun tt n => arb) (fun tt n => nil) (fun tt n => show n) (
  @Predicate (CtxBind nat (CtxBind nat EmptyCtx))
             (fun '(y, (x, tt)) => test x y))).

Fixpoint genAndTest (C: Ctx) (env : interpCtx C)
         (cprop: CProp C) : G (option bool).
  induction cprop.
  - refine (bindGen _ _).
    + exact (g env).
    + intro x.
      apply IHcprop.
      exact (x, env).
  - exact (returnGen (o env)).
Defined.

Fixpoint finalCtx (C : Ctx) 
         (cprop : CProp C) : Ctx.
  induction cprop.
  - exact (CtxBind A (finalCtx (CtxBind A C) cprop)).
  - exact EmptyCtx.
Defined.

Fixpoint genAndTestResult (C: Ctx) (env : interpCtx C)
         (cprop: CProp C) : G (interpCtx (finalCtx C cprop) * option bool).
  induction cprop; simpl in *.
  - refine (bindGen _ _).
    + exact (g env).
    + intro a.
      specialize (IHcprop (a, env)).
      refine (bindGen IHcprop _).
      intros [c b].
      refine (returnGen ((a,c), b)).
  - exact (returnGen (tt, o env)).
Defined.

Definition emptyEnv : interpCtx EmptyCtx := tt.

Compute (finalCtx EmptyCtx example).

Fixpoint print (C : Ctx) (cprop : CProp C)
         (cenv : interpCtx C)
         (fenv : interpCtx (finalCtx C cprop))
         {struct cprop}
  : list string.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply cons.
    + exact (s cenv a).
    + apply (print _ cprop (a, cenv) fenv'). 
  - exact nil.
Defined.

Compute (print EmptyCtx example tt (3,(4,tt))).

(* 

Runner Loop:

- Generate a test case
- Depending on some state, you may choose to mutate it
- Run the test case
- Update the state based on the test case
- If the test case fails
  + Shrink the case by repeatedly running it
  + If the case is minimal, return it
- If the test case passes
  + Check if you exhausted your fuel or you have too many discards
  + If so, return "not found"
  + Otherwise, go back to generating a new test case


Problems:
- I want shrinking and printing to be an after-thought. We should have a pipeline

  1. Run tests, collect metrics if applicable.
  2. Get result, shrink if applicable.
  3. Print result

  The problem is that I haven't found a good way of integrating the metric collection
  because data types are not present in the higher level interface. The first option
  is to use printing for serialization. 

 *)

Fixpoint runLoop (f: nat) () (cprop: CProp EmptyCtx) : G Result.
  induction f.
  - refine (returnGen _).
    refine (MkResult None false ""%string false nil nil None).
  - refine (bindGen _ _).
    + apply IHf.
    + intros. apply IHf.
Defined.

Print runLoop.





Definition result :list (option bool) := 
  sample (run EmptyCtx emptyEnv example).

QuickChick (runLoop 10 example).

QuickChick (run EmptyCtx emptyEnv example).
Sample (run EmptyCtx emptyEnv example).
