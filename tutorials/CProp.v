From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Inductive Ctx :=
| EmptyCtx
| CtxBind : Type -> Ctx -> Ctx.

Declare Scope prop_scope.
Notation "'∅'" := EmptyCtx : prop_scope.
Notation " A '·' C " :=
  (CtxBind A C) (at level 70) : prop_scope.

Local Open Scope prop_scope.

Fixpoint interpCtx (C : Ctx) : Type :=
  match C with
  | ∅ => unit
  | T·C => T * interpCtx C
  end.

Notation "'⟦' C '⟧'" := (interpCtx C) : prop_scope.

Inductive CProp : Ctx -> Type :=
| ForAll : forall A C,
    (* TODO: Name these? *)
      (⟦C⟧ -> G A) ->
      (⟦C⟧ -> A -> G A) ->
      (⟦C⟧ -> A -> list A) -> 
      (⟦C⟧ -> A -> string) ->
      CProp (A · C) -> CProp C
  | Predicate : forall C,
      (⟦C⟧ -> option bool) -> CProp C.

Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition test (x y : nat) : option bool :=
  Some (Nat.ltb y x).
  
Definition example :=
  @ForAll _ EmptyCtx (fun tt => arb) (fun tt n => arb) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (CtxBind nat EmptyCtx) (fun '(x, tt) => gen x) (fun tt n => arb) (fun tt n => shrink n) (fun tt n => show n) (
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

(* replace genAndTest with this *)
Fixpoint genAndRun {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> G (option bool) :=
  match cprop with
  | ForAll A C gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        genAndRun cprop' (a,env) 
  | Predicate C prop =>
      fun env => ret (prop env)
  end.

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

Fixpoint runAndTest (C:Ctx) (cprop : CProp C)
         (cenv : interpCtx C)
         (fenv : interpCtx (finalCtx C cprop))
         {struct cprop}
  : option bool.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - exact (o cenv).
Defined.

Compute (runAndTest EmptyCtx example tt (3,(4,tt))).
Compute (runAndTest EmptyCtx example tt (4,(3,tt))).

Fixpoint shrinkOnTheFly
  (C : Ctx) (cprop : CProp C)
  (cenv : interpCtx C)
  (fenv : interpCtx (finalCtx C cprop))
  {struct cprop}
  : option (interpCtx (finalCtx C cprop)).
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'].
    (* Recurse through the list of shrinks *)
    induction (l cenv a).
    (* No more shrinks - try the next element of the property *)
    + destruct (shrinkOnTheFly _ cprop (a,cenv) fenv') eqn:M.
      * exact (Some (a, i)).
      * exact None.
    (* More shrinks - run the property on the shrunk possibility. *)
    + destruct (runAndTest _ cprop (a0,cenv) fenv') eqn:T.
      * destruct b.
        (* Test succeeded - recurse down the list. *)
        -- apply IHl0.
        (* Test failed - end with current result. *)
        -- exact (Some (a0, fenv')).
      * (* Test discarded - recurse down the list. *)
        apply IHl0.
  - exact None.
Defined.

Fixpoint shrinkLoop (fuel : nat)
  (cprop: CProp EmptyCtx) (counterexample : interpCtx (finalCtx EmptyCtx cprop)) :
  interpCtx (finalCtx EmptyCtx cprop) :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrinkOnTheFly EmptyCtx cprop tt counterexample with
      | Some c' => shrinkLoop fuel' cprop c'
      | None => counterexample
      end
  end.

Fixpoint shrinkLoopLog (fuel : nat)
  (cprop: CProp EmptyCtx) (counterexample : interpCtx (finalCtx EmptyCtx cprop)) :
  list (interpCtx (finalCtx EmptyCtx cprop)) :=
  match fuel with
  | O => [counterexample]
  | S fuel' =>
      match shrinkOnTheFly EmptyCtx cprop tt counterexample with
      | Some c' => (counterexample :: shrinkLoopLog fuel' cprop c')
      | None => [counterexample]
      end
  end.

Compute (shrinkLoopLog 10  example (3,(4,tt))).

Fixpoint runLoop1 (fuel: nat)
         (cprop: CProp EmptyCtx) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult EmptyCtx emptyEnv cprop)
              (fun res =>
                  returnGen (print EmptyCtx cprop tt (fst res)))
               
  end.

Fixpoint runLoop2 (fuel: nat)
         (cprop: CProp EmptyCtx) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult EmptyCtx emptyEnv cprop)
              (fun res =>
                 match res with
                 | (variables, result) =>
                     match result with
                     | Some false =>
                                let shrinked := shrinkLoop 10 cprop (fst res) in
                                 returnGen (print EmptyCtx cprop tt shrinked)
                     | None | Some true => runLoop2 fuel' cprop
                     end
                 end
                   
                 
                  )
               
  end.

Fixpoint genAndTestLoop (fuel: nat)
         (cprop: CProp EmptyCtx) : G (option (interpCtx (finalCtx EmptyCtx cprop))) :=
  match fuel with
  | 0 => returnGen None
  | S fuel' =>
      bindGen (genAndTestResult EmptyCtx emptyEnv cprop)
              (fun res =>
                 match res with
                 | (variables, result) =>
                     match result with
                     | Some false => returnGen (Some variables)
                     | None | Some true => genAndTestLoop fuel' cprop
                     end
                 end)
               
  end.

Fixpoint runLoop3 (fuel: nat)
         (cprop: CProp EmptyCtx) : G (list string) :=
  generationResult <- genAndTestLoop fuel cprop ;;
  match generationResult with
  | None => returnGen []
  | Some variables =>
      let shrinkingResult := shrinkLoop 10 cprop variables in
      let printingResult := print EmptyCtx cprop tt shrinkingResult in
      returnGen printingResult
  end
.



Sample (runLoop3 10 example).

Print runLoop.





Definition result :list (option bool) := 
  sample (run EmptyCtx emptyEnv example).

QuickChick (runLoop 10 example).

QuickChick (run EmptyCtx emptyEnv example).
Sample (run EmptyCtx emptyEnv example).
