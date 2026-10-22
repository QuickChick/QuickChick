From QuickChick Require Import SchedulingPolicy QuickChick.

Inductive policy_quote_probe : nat -> Prop :=
| QuoteZero : policy_quote_probe 0
| QuoteSucc : forall n, policy_quote_probe n -> policy_quote_probe (S n).

Definition policy_quote_probe_score (view : term_view) : nat :=
  match view with
  | TProduct _ _ _ => 7
  | _ => 0
  end.

Record quote_cost := { quote_depth : nat; quote_weight : nat }.

Definition policy_quote_record_score (view : term_view) : quote_cost :=
  match view with
  | TProduct _ _ _ => {| quote_depth := 2; quote_weight := 3 |}
  | _ => {| quote_depth := 0; quote_weight := 1 |}
  end.

Definition policy_quote_step_score (step : step_view) : nat :=
  match step with
  | CheckStep _ _ => 1
  | SuchThat _ _ _ => 2
  | Unconstrained _ _ _ => 3
  | MatchStep _ _ => 4
  | LetStep _ _ => 5
  end.

Definition policy_quote_step_fields (step : step_view) : nat * nat * nat :=
  match step with
  | SuchThat outputs source _ =>
      (List.length outputs, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | Unconstrained _ source _ =>
      (1, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | CheckStep source _ =>
      (0, List.length (source_inputs source),
       List.length (source_finite_pins source))
  | _ => (0, 0, 0)
  end.

Derive Inductive Schedule policy_quote_probe derive "Check" opt "true".

Inductive policy_quote_param (A : Type) : list A -> Prop :=
| QuoteNil : policy_quote_param A nil
| QuoteCons : forall x xs, policy_quote_param A xs -> policy_quote_param A (x :: xs).

Derive Inductive Schedule policy_quote_param derive "Check" opt "true".

Inductive policy_quote_generated : nat -> Prop :=
| QuoteGenerated : forall n, policy_quote_generated n.

Derive Inductive Schedule policy_quote_generated 0 derive "Gen" opt "true".

Inductive policy_quote_premise : nat -> Prop :=
| QuoteFromPremise : forall n, policy_quote_probe n -> policy_quote_premise n.

Derive Inductive Schedule policy_quote_premise 0 derive "Gen" opt "true".

Inductive policy_quote_zero : nat -> Prop :=
| QuoteOnlyZero : policy_quote_zero 0.

Inductive policy_quote_pinned : nat -> Prop :=
| QuotePinned : forall n, policy_quote_zero n -> policy_quote_pinned n.

Derive Inductive Schedule policy_quote_pinned 0 derive "Gen" opt "true".

Inductive policy_quote_indexed : nat -> nat -> Prop :=
| QuoteIndexed : forall n, policy_quote_indexed n (S n).

Inductive policy_quote_with_input : nat -> nat -> Prop :=
| QuoteWithInput : forall x y,
    policy_quote_indexed x y -> policy_quote_with_input x y.

Derive Inductive Schedule policy_quote_with_input 1 derive "Gen" opt "true".
