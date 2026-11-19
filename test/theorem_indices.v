(* quickchick n i runs the i-th best theorem schedule, in the order
   quickchick_schedules lists them, under the active scorer. *)
From QuickChick Require Import QuickChick SchedulingPolicy.
Require Import List.
Extract Constant defNumTests => "5".

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive plus' : nat -> nat -> nat -> Prop :=
| plus_O n : plus' 0 n n
| plus_S n m p : plus' n m p -> plus' (S n) m (S p).

(* Ten candidates under density. *)
Goal forall a b c d s, le' a b -> le' b c -> plus' a c s -> le' c d -> le' a d.
  quickchick_schedules.
  quickchick 3 0.
  quickchick 3 4.
  quickchick 3 9.
  Fail quickchick 3 10.
  quickchick_idx 2.
  Fail quickchick_idx 10.
Abort.

QC Scorer budget_aware.
Goal forall a b c d s, le' a b -> le' b c -> plus' a c s -> le' c d -> le' a d.
  quickchick_schedules.
  quickchick 3 1.
Abort.

(* Compiled policies rank theorem schedules too. *)
Definition count_checks (direction : bool) : scorer nat := {|
  score_step := fun _ step _ => match step with
    | CheckStep _ _ => if direction then 1 else 0
    | _ => if direction then 0 else 1 end;
  score_schedule := fun _ _ xs => fold_left Nat.add xs 0;
  score_leaf := fun _ _ xs => fold_left Nat.add (map snd xs) 0;
  score_inductive := fun _ _ xs => fold_left Nat.add (map snd xs) 0;
  compare_scores := Nat.compare |}.
Definition fewest_checks : policy := {| score_type := nat; policy_scorer := count_checks true; lower_bound := fun _ _ => 0; policy_grouping := None; policy_bound_sound := None |}.
Definition most_checks : policy := {| score_type := nat; policy_scorer := count_checks false; lower_bound := fun _ _ => 0; policy_grouping := None; policy_bound_sound := None |}.

Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive pinned : nat -> nat -> Prop :=
| PinZero : forall y, pinned 0 y
| PinOne : forall y, pinned 1 y.

QC Scorer fewest_checks.
Goal forall x y, loose x -> pinned x y -> x <= 1.
  quickchick 2.
  lazymatch (eval unfold theorem in theorem) with
  | context [@decOpt (loose _)] => fail "fewest_checks checked loose x"
  | _ => idtac
  end.
Abort.

QC Scorer most_checks.
Goal forall x y, loose x -> pinned x y -> x <= 1.
  quickchick 2.
  lazymatch (eval unfold theorem in theorem) with
  | context [@decOpt (loose _)] => idtac
  | _ => fail "most_checks did not check loose x"
  end.
Abort.
