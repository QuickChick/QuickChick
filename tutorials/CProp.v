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

Inductive CProp : Ctx -> Type -> Type :=
| ForAll : forall A C F
      (name: string)
      (generator : ⟦C⟧ -> G A)
      (mutator   : ⟦C⟧ -> A -> G A)
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) F -> CProp C F
  | Predicate : forall C F,
      (⟦C⟧ -> option bool * option F) -> CProp C F.

Fixpoint inputTypes {C : Ctx} {F : Type}
         (cprop : CProp C F) : Ctx :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | Predicate _ _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@inputTypes _ _ c).

Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition test (x y : nat) : option bool :=
  Some (Nat.ltb y x).

Local Open Scope string.

Definition example :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => arb) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => arb) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) unit
             (fun '(y, (x, tt)) => (test x y, None)))).

Compute ⦗example⦘. 

Fixpoint genAndRun {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (⟦⦗cprop⦘⟧ * (option bool * option F)) :=
  match cprop with
  | ForAll A C F _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        res <- genAndRun cprop' (a,env);;
        let '(env', (truth, instr)) := res in
        ret ((a,env'), (truth, instr))
  | Predicate C F prop =>
      fun env => returnGen (tt, prop env)
  end.

Fixpoint print {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string) :=
  match cprop with
  | ForAll A C F name gen mut shr pr cprop' =>
      fun env '(a,inps') =>
        (name, pr env a) :: (print cprop' (a, env) inps')
  | Predicate C F prop =>
      fun _ _ => nil
  end.

Fixpoint generalizedTargeting (fuel : nat) {C} {F}
         (cprop: CProp C F)
    (* TODO : better data structure for seed pool *)
         (seed_pool : data structure ⟦⦗C⦘⟧)
         {Agg : Type}
         (agg : Agg)
         (update_agg : Agg -> F -> ⟦⦗C⦘⟧ -> Agg)
         (is_waypoint: Agg -> F -> bool)
         (priority : Agg -> F -> nat)
         :=
  match fuel with 
  | O => _
  | S fuel' =>
      (* Zero: Decide how to generate based on seed_pool *)
      (* This is just random *)
      res <- genAndRun cprop ∅;;
      let '(inputs, (truth, feedback)) := res in
      (* First: Check truth.. *)
      ....
      (* Second: Check feedback *)
      if is_waypoint agg feedback then
        let agg' := update_agg agg feedback inputs in
        let seed_pool := ... in
        generalizedTargeting ....                            else
        generalizedTargeting ....     
                         end. 

Fixpoint runAndTest (C:Ctx) (cprop : CProp C)
         (cenv : ⟦C⟧)
         (fenv :  ⟦finalCtx C cprop⟧)
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

Compute (runAndTest ∅ example tt (3,(4,tt))).
Compute (runAndTest ∅ example tt (4,(3,tt))).

Fixpoint shrinkOnTheFly
  (C : Ctx) (cprop : CProp C)
  (cenv :  ⟦C⟧)
  (fenv :  ⟦finalCtx C cprop⟧)
  {struct cprop}
  : option ⟦finalCtx C cprop⟧.
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
  (cprop: CProp ∅) (counterexample : ⟦finalCtx ∅ cprop⟧) :
  ⟦finalCtx ∅ cprop⟧ :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrinkOnTheFly ∅ cprop tt counterexample with
      | Some c' => shrinkLoop fuel' cprop c'
      | None => counterexample
      end
  end.

Fixpoint shrinkLoopLog (fuel : nat)
  (cprop: CProp ∅) (counterexample : ⟦finalCtx ∅ cprop⟧) :
  list  ⟦finalCtx ∅ cprop⟧ :=
  match fuel with
  | O => [counterexample]
  | S fuel' =>
      match shrinkOnTheFly ∅ cprop tt counterexample with
      | Some c' => (counterexample :: shrinkLoopLog fuel' cprop c')
      | None => [counterexample]
      end
  end.

Compute (shrinkLoopLog 10  example (3,(4,tt))).

Fixpoint runLoop1 (fuel: nat)
         (cprop: CProp ∅) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
              (fun res =>
                  returnGen (print ∅ cprop tt (fst res)))
               
  end.

Fixpoint runLoop2 (fuel: nat)
         (cprop: CProp ∅) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
              (fun res =>
                 match res with
                 | (variables, result) =>
                     match result with
                     | Some false =>
                                let shrinked := shrinkLoop 10 cprop (fst res) in
                                 returnGen (print ∅ cprop tt shrinked)
                     | None | Some true => runLoop2 fuel' cprop
                     end
                 end)
               
  end.

Fixpoint genAndTestLoop (fuel: nat)
         (cprop: CProp ∅) : G (option ⟦finalCtx ∅ cprop⟧) :=
  match fuel with
  | 0 => returnGen None
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
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
         (cprop: CProp ∅) : G (list string) :=
  generationResult <- genAndTestLoop fuel cprop ;;
  match generationResult with
  | None => returnGen []
  | Some variables =>
      let shrinkingResult := shrinkLoop 10 cprop variables in
      let printingResult := print ∅ cprop tt shrinkingResult in
      returnGen printingResult
  end
.


Sample (runLoop3 10 example).
