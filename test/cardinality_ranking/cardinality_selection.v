From QuickChick Require Import QuickChick.
Require Import List.
Import ListNotations.

(* [defd ets ns] determines ns from ets; [wf ns a] accepts any ns and a.
   Producing ns from wf and then checking defd ets ns is a filter that admits
   one list out of exponentially many, so cardinality ranking produces ns
   from defd. The inequality a <> b almost always passes. As in Cedar, ets is
   taken apart from an equality on the input V; BudgetAware then ties the two
   schedules (its density field is already Checking because of the
   inequality) and its lower candidate identifier checks defd. *)
Inductive defd : list nat -> list nat -> Prop :=
| DefdNil : defd [] []
| DefdCons : forall n ets ns, defd ets ns -> defd (n :: ets) (n :: ns).

Inductive wf : list nat -> nat -> Prop :=
| WfAny : forall ns a, wf ns a.

Inductive envt : Type := Env : list nat -> envt.

Inductive pick : envt -> nat -> nat -> Prop :=
| Pick : forall V ets ns a b,
    V = Env ets -> wf ns a -> wf ns b -> defd ets ns -> a <> b -> pick V a b.

QuickChick Derive Generator for (fun a b => pick V a b).

Goal True.
  lazymatch (eval unfold GenSizedSuchThatpick in GenSizedSuchThatpick) with
  | context [@decOpt (defd _ _)] => fail "cardinality ranking checked defd after inventing ns"
  | _ => exact I
  end.
Qed.
