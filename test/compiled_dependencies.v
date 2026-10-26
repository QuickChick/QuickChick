From QuickChick Require Import QuickChick SchedulingPolicy.
Require Import List Arith Bool String. Import ListNotations.

(* A compiled policy sees the completed scores of the relations a schedule
   depends on. Two policies that read a producer's dependency score in
   opposite directions choose different producers; without the scores they
   would tie and choose the same one. *)

Fixpoint term_eqb (a b : term_view) : bool :=
  match a, b with
  | TLocal i, TLocal j => Nat.eqb i j
  | TGlobal x, TGlobal y | TGenerated x, TGenerated y | TSort x, TSort y => String.eqb x y
  | TApply f xs, TApply g ys =>
    term_eqb f g &&
    (fix args_eqb xs ys := match xs, ys with
     | [], [] => true
     | x :: xs, y :: ys => term_eqb x y && args_eqb xs ys
     | _, _ => false
     end) xs ys
  | _, _ => false
  end.

Definition dependency_score (ctx : score_context nat) (source : source_view) : option nat :=
  match find (fun '(spec, _) => term_eqb (spec_application spec) (source_application source))
              (dependencies ctx) with
  | Some (_, Completed s) => Some s
  | _ => None
  end.

(* Every step costs 1; a producer also costs [cost] of its dependency's
   score, and an unknown dependency nothing. *)
Definition dependency_scorer (cost : nat -> nat) : scorer nat := {|
  score_step := fun _ _ _ => 0;
  score_schedule := fun ctx schedule _ =>
    fold_left Nat.add (map (fun '(step, _) => match step with
      | SuchThat _ source _ =>
        1 + match dependency_score ctx source with Some s => cost s | None => 0 end
      | CheckStep _ _ => 0
      | _ => 1
      end) (schedule_steps schedule)) 0;
  score_leaf := fun _ _ covering => fold_left Nat.min (map snd covering) 100;
  score_inductive := fun _ _ leaves => fold_left Nat.max (map snd leaves) 0;
  compare_scores := Nat.compare
|}.

Definition cheap_dependencies : policy := {| score_type := nat;
  policy_scorer := dependency_scorer (fun s => s); lower_bound := fun _ _ => 0;
  policy_grouping := None; policy_bound_sound := None |}.
Definition costly_dependencies : policy := {| score_type := nat;
  policy_scorer := dependency_scorer (fun s => 10 - s); lower_bound := fun _ _ => 0;
  policy_grouping := None; policy_bound_sound := None |}.

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
