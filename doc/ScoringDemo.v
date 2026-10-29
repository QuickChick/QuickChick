From Coq Require Import List Arith Lia.
From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Import ListNotations.

(* A schedule scorer written in Rocq. It counts a schedule's positive
   checks: fewer is better. Built with fold_policy, it comes with a proved
   pruning bound and a grouping, so QC Scorer compiles it and the plugin
   searches with pruning and by independent hypothesis groups. *)

Definition checks_score : step_scorer nat nat_sum :=
  spec_step_scorer nat_sum (fun _ _ step _ => if is_check step then 1 else 0)
    (fun _ _ _ _ => ltac:(nat_order)).

(* A remaining hypothesis whose arguments are all bound must become a
   positive check, so each one counts in the bound. *)
Definition forced_checks_cost : check_floor nat nat_sum checks_score.
Proof.
  refine {| floor_score := fun _ => 1 |}.
  intros. cbn. nat_order.
Defined.

Definition fewest_checks : policy :=
  fold_policy nat_sum checks_score (Some forced_checks_cost) Additive.

Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive pinned : nat -> nat -> Prop :=
| PinZero : forall y, pinned 0 y
| PinOne : forall y, pinned 1 y.
Inductive root : nat -> nat -> Prop :=
| Root : forall x y, loose x -> pinned x y -> root x y.

(* QC Scorer compiles the policy once; later derivations in this file rank
   their schedules with it. *)
QC Scorer fewest_checks.
QuickChick Derive Generator for (fun x y => root x y).

(* The selected schedule generates x from loose instead of checking it. *)
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot in GenSizedSuchThatroot) with
  | context [@decOpt (loose _)] => fail "fewest_checks checked loose x"
  | _ => exact I
  end.
Qed.

(* Back to the default scorer. *)
QC Scorer density.
