From QuickChick Require Import QuickChick SchedulingPolicy SchedulingPolicyLaws.
Require Import List Arith Lia. Import ListNotations.

(* A policy whose score depends on local ids themselves. Its fold bound is
   proved admissible on the assumption that a committed step keeps its view
   below a search node, so verification mode fails if the plugin numbered a
   variable differently at a node and in a schedule below it. *)
Definition output_ids (step : step_view) : nat :=
  match step with
  | Unconstrained l _ _ => local_id l
  | SuchThat ls _ _ => fold_left Nat.add (map local_id ls) 0
  | _ => 0
  end.

Definition ids_score : step_scorer nat nat_sum :=
  spec_step_scorer nat_sum (fun _ _ step _ => output_ids step) (fun _ _ _ _ => ltac:(nat_order)).

Definition ids_policy : policy := fold_policy nat_sum ids_score None Additive.

QC Scorer ids_policy.

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive chain : nat -> nat -> nat -> nat -> Prop :=
| Chain : forall a b c d, le' a b -> le' b c -> le' c d -> chain a b c d.

QuickChick Derive Generator for (fun b c d => chain a b c d).
QuickChick Derive Generator for (fun a b c d => chain a b c d).
