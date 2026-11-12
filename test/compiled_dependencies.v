From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Require Import List Arith Bool String. Import ListNotations.

(* A compiled policy sees the completed scores of the relations a schedule
   depends on. Two policies that read a producer's dependency score in
   opposite directions choose different producers; without the scores they
   would tie and choose the same one. Both prove their bound, so they also
   search with pruning. *)

(* Every step costs 1, a producer also [cost] of its dependency's completed
   score, and a check nothing. An unknown dependency costs nothing, the least
   it could cost, so the bound proved by fold_policy holds. *)
Definition dependency_cost (cost : nat -> nat) : step_scorer nat nat_sum.
Proof.
  refine (dependency_step_scorer nat_sum (fun _ _ step _ dep =>
    match step with
    | SuchThat _ _ _ => 1 + match dep with Some s => cost s | None => 0 end
    | CheckStep _ _ => 0
    | _ => 1
    end) _ _); intros; [nat_order | destruct step; nat_order].
Defined.

Definition cheap_dependencies : policy :=
  fold_policy nat_sum (dependency_cost (fun s => s)) None Additive.
Definition costly_dependencies : policy :=
  fold_policy nat_sum (dependency_cost (fun s => 10 - s)) None Additive.

Inductive good : nat -> Prop := Good : forall x, good x.
Inductive bad : nat -> Prop := Bad : forall x, good x -> bad x.

QC Scorer cheap_dependencies.
Inductive root1 : nat -> Prop := Root1 : forall x, good x -> bad x -> root1 x.
QuickChick Derive Generator for (fun x => root1 x).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot1 in GenSizedSuchThatroot1) with
  | context [@decOpt (bad _)] => exact I
  | _ => fail "cheap_dependencies did not generate x from good"
  end.
Qed.

QC Scorer costly_dependencies.
Inductive root2 : nat -> Prop := Root2 : forall x, good x -> bad x -> root2 x.
QuickChick Derive Generator for (fun x => root2 x).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot2 in GenSizedSuchThatroot2) with
  | context [@decOpt (good _)] => exact I
  | _ => fail "costly_dependencies did not generate x from bad"
  end.
Qed.
