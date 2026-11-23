(* A Rocq scoring policy, compiled and loaded by QC Scorer, chooses
   constructor schedules. Two policies that disagree about checks choose
   different schedules for the same relation. *)
From QuickChick Require Import QuickChick SchedulingPolicy.
Require Import List.

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
Inductive root1 : nat -> nat -> Prop := Root1 : forall x y, loose x -> pinned x y -> root1 x y.
QuickChick Derive Generator for (fun x y => root1 x y).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot1 in GenSizedSuchThatroot1) with
  | context [@decOpt (loose _)] => fail "fewest_checks checked loose x"
  | _ => exact I
  end.
Qed.

QC Scorer most_checks.
Inductive root2 : nat -> nat -> Prop := Root2 : forall x y, loose x -> pinned x y -> root2 x y.
QuickChick Derive Generator for (fun x y => root2 x y).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot2 in GenSizedSuchThatroot2) with
  | context [@decOpt (loose _)] => exact I
  | _ => fail "most_checks did not check loose x"
  end.
Qed.

(* A constant that is not a policy, and an unknown name, are rejected. *)
Fail QC Scorer count_checks.
Fail QC Scorer no_such_policy.

(* A bound proved with an admitted lemma still enables pruning; selecting the
   policy warns that pruning trusts it. *)
Lemma trusted_bound : bound_admissible (count_checks true) (fun _ _ => 0).
Admitted.
Definition trusted_policy : policy := {| score_type := nat;
  policy_scorer := count_checks true; lower_bound := fun _ _ => 0;
  policy_grouping := None; policy_bound_sound := Some trusted_bound |}.
QC Scorer trusted_policy.
Inductive root3 : nat -> nat -> Prop := Root3 : forall x y, loose x -> pinned x y -> root3 x y.
QuickChick Derive Generator for (fun x y => root3 x y).
