From Coq Require Import List String Arith.
From QuickChick Require Import QuickChick SchedulingPolicy.
Import ListNotations.
Open Scope string_scope.

(* Experimental diagnostic: Rocq scores real schedule candidates, but the
   public derivation still selects with its existing ranking policy. *)
Record demo_cost := { source_priority : nat; schedule_work : nat }.

Definition ends_in (name suffix : string) : bool :=
  String.eqb (String.substring (String.length name - String.length suffix)
               (String.length suffix) name) suffix.

Definition demo_score (schedule : schedule_view) : demo_cost :=
  let first_source := match schedule_steps schedule with
    | (SuchThat _ source _, _) :: _ => Some (source_application source)
    | (Unconstrained _ source _, _) :: _ => Some (source_application source)
    | (CheckStep source _, _) :: _ => Some (source_application source)
    | _ => None end in
  let priority := match first_source with
    | Some (TApply (TGlobal name) _) =>
        if ends_in name "demo_c" then 0
        else if ends_in name "demo_b" then 1 else 2
    | _ => 3 end in
  {| source_priority := priority;
     schedule_work := List.length (schedule_steps schedule) |}.

Definition demo_compare (left right : demo_cost) : comparison :=
  match Nat.compare (source_priority left) (source_priority right) with
  | Eq => Nat.compare (schedule_work left) (schedule_work right)
  | order => order end.

Inductive demo_a : nat -> Prop := DemoA : forall x, demo_a x.
Inductive demo_b : nat -> nat -> Prop := DemoB : forall x y, demo_b x y.
Inductive demo_c : nat -> nat -> Prop := DemoC : forall y z, demo_c y z.
Inductive demo_root : nat -> nat -> nat -> Prop :=
| DemoRoot : forall x y z,
    demo_a x -> demo_b x y -> demo_c y z -> demo_root x y z.

(* With the probe enabled, candidate 3 wins under demo_score. The current
   built-in ranker still selects candidate 0. *)
QuickChick Derive Generator for (fun x y z => demo_root x y z).
