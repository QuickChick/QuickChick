From QuickChick Require Import QuickChick SchedulingPolicy.
Require Import List Arith. Import ListNotations.

(* The built-in density_then_vars ranking written as a Rocq policy. Compiled
   by QC Scorer, it must choose the same schedules as the built-in. *)

Definition grade_rank (d : density) : nat :=
  match d with
  | Checking => 0 | Backtracking => 1 | Neutral => 2 | Partial => 3 | Total => 4
  end.

Definition prefers_dense (m : derive_mode) : bool :=
  match m with Generate | TestTheorem => true | Enumerate | Check => false end.

(* A producer is as dense as its sparsest step; a checker or enumerator as
   sparse as its densest. Lower scores are better, so a producer's rank is
   flipped. *)
Definition representative (dense : bool) (grades : list nat) : nat :=
  match grades with
  | [] => 0
  | g :: gs =>
    if dense then 4 - fold_left Nat.min gs g else fold_left Nat.max gs g
  end.

(* Variables occurring as relation or constructor arguments, as the engine
   collects them: not under binders, arrows or negations. *)
Fixpoint argument_locals (t : term_view) : list nat :=
  match t with
  | TLocal i => [i]
  | TApply _ args => flat_map argument_locals args
  | _ => []
  end.

Definition distinct (ids : list nat) : list nat := nodup Nat.eq_dec ids.

(* The engine counts a nonrecursive source's distinct variables, and a
   generated call's distinct variables per argument. *)
Definition source_locals (s : source_view) : list nat :=
  match source_category s, source_application s with
  | External, t => distinct (argument_locals t)
  | _, TApply _ args => flat_map (fun a => distinct (argument_locals a)) args
  | _, t => distinct (argument_locals t)
  end.

Fixpoint pattern_locals (p : pattern_view) : list nat :=
  match p with
  | PLocal i => [i]
  | PConstructor _ args => flat_map pattern_locals args
  | _ => []
  end.

Definition step_uses (bound : list nat) (step : step_view) : nat :=
  let count ids := length (filter (fun i => existsb (Nat.eqb i) bound) ids) in
  match step with
  | Unconstrained _ s _ | SuchThat _ s _ | CheckStep s _ => count (source_locals s)
  | LetStep _ value => count (distinct (argument_locals value))
  | MatchStep _ _ => 0
  end.

Definition step_binds (step : step_view) : list nat :=
  match step with
  | Unconstrained l _ _ => [local_id l]
  | SuchThat ls _ _ => map local_id ls
  | MatchStep _ p => pattern_locals p
  | LetStep l _ => [local_id l]
  | CheckStep _ _ => []
  end.

(* Uses of variables bound by earlier steps; the root's inputs do not count. *)
Fixpoint variable_uses (bound : list nat) (steps : list step_view) : nat :=
  match steps with
  | [] => 0
  | step :: rest => step_uses bound step + variable_uses (step_binds step ++ bound) rest
  end.

Definition density_scorer : scorer (nat * nat) := {|
  score_step := fun _ _ _ => (0, 0);
  score_schedule := fun ctx schedule _ =>
    let steps := schedule_steps schedule in
    (representative (prefers_dense (spec_mode (current_spec ctx)))
       (map (fun '(_, g) => grade_rank g) steps),
     variable_uses [] (map fst steps));
  score_leaf := fun _ _ _ => (0, 0);
  score_inductive := fun _ _ _ => (0, 0);
  compare_scores := fun '(d, u) '(d', u') =>
    match Nat.compare d d' with Eq => Nat.compare u u' | c => c end
|}.

Definition density_policy : policy :=
  {| score_type := nat * nat; policy_scorer := density_scorer;
     lower_bound := fun _ _ => (0, 0) |}.

(* The built-in and the compiled policy choose the same schedule. Each
   relation is derived under both; the generated instances must be equal. *)
Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive pinned : nat -> nat -> Prop :=
| PinZero : forall y, pinned 0 y
| PinOne : forall y, pinned 1 y.
Inductive root : nat -> nat -> Prop :=
| Root : forall x y, loose x -> pinned x y -> root x y.

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive between : nat -> nat -> nat -> Prop :=
| Between : forall a b c, le' a b -> le' b c -> between a b c.

QuickChick Derive Generator for (fun x y => root x y).
QuickChick Derive Generator for (fun b c => between a b c).
QuickChick Derive Checker for (between a b c).
QC Scorer density_policy.
QuickChick Derive Generator for (fun x y => root x y).
QuickChick Derive Generator for (fun b c => between a b c).
QuickChick Derive Checker for (between a b c).

Ltac same_instance i j :=
  let a := eval unfold i in i in
  let b := eval unfold j in j in
  first [constr_eq a b | fail "the compiled density policy chose another schedule"].

Goal True.
  same_instance GenSizedSuchThatroot GenSizedSuchThatroot0.
  same_instance GenSizedSuchThatbetween GenSizedSuchThatbetween0.
  same_instance DecOptbetween DecOptbetween0.
  exact I.
Qed.
