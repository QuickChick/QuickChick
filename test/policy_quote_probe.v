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

Derive Inductive Schedule policy_quote_probe derive "Check" opt "true".

Inductive policy_quote_param (A : Type) : list A -> Prop :=
| QuoteNil : policy_quote_param A nil
| QuoteCons : forall x xs, policy_quote_param A xs -> policy_quote_param A (x :: xs).

Derive Inductive Schedule policy_quote_param derive "Check" opt "true".
