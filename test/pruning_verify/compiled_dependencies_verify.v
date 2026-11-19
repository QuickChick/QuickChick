From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Require Import List Arith Lia. Import ListNotations.

(* A policy that reads dependency scores, in verification mode: its bound,
   proved for contexts that gain completed dependencies, is checked against
   every completed descendant. *)
Definition dependency_cost : step_scorer nat nat_sum.
Proof.
  refine (dependency_step_scorer nat_sum (fun _ _ step _ dep =>
    match step with
    | SuchThat _ _ _ => 1 + match dep with Some s => s | None => 0 end
    | CheckStep _ _ => 0
    | _ => 1
    end) _ _); intros; [nat_order | destruct step; nat_order].
Defined.

Definition dependency_policy : policy := fold_policy nat_sum dependency_cost None Additive.
QC Scorer dependency_policy.

Inductive good : nat -> Prop := Good : forall x, good x.
Inductive bad : nat -> Prop := Bad : forall x, good x -> bad x.
Inductive chain : nat -> nat -> Prop :=
| Chain : forall x y, good x -> bad y -> good y -> bad x -> chain x y.
QuickChick Derive Generator for (fun x y => chain x y).
