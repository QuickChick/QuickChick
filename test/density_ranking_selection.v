From QuickChick Require Import QuickChick.

(* The density ranking prefers a schedule without checks: x from loose, then
   y from pinned with x as an input at its finitely pinned position.
   BudgetAware charges that loose production of a pinned variable
   (selectivity 1) and prefers producing both from pinned, then checking
   loose x (selectivity 0). *)
Inductive loose : nat -> Prop := Loose : forall x, loose x.
Inductive pinned : nat -> nat -> Prop :=
| PinZero : forall y, pinned 0 y
| PinOne : forall y, pinned 1 y.
Inductive root : nat -> nat -> Prop :=
| Root : forall x y, loose x -> pinned x y -> root x y.
QuickChick Derive Generator for (fun x y => root x y).

(* Under the default density ranking, loose is a producer, not a check. *)
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot in GenSizedSuchThatroot) with
  | context [@decOpt (loose _)] => fail "density ranking unexpectedly checked loose x"
  | _ => exact I
  end.
Qed.

(* QC Scorer applies to later derivations in the same file, without reusing
   results scored by the previous scorer. *)
QC Scorer budget_aware.
Inductive root2 : nat -> nat -> Prop :=
| Root2 : forall x y, loose x -> pinned x y -> root2 x y.
QuickChick Derive Generator for (fun x y => root2 x y).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot2 in GenSizedSuchThatroot2) with
  | context [@decOpt (loose _)] => exact I
  | _ => fail "BudgetAware scorer did not check loose x"
  end.
Qed.

QuickChick Scorer density.
Inductive root3 : nat -> nat -> Prop :=
| Root3 : forall x y, loose x -> pinned x y -> root3 x y.
QuickChick Derive Generator for (fun x y => root3 x y).
Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot3 in GenSizedSuchThatroot3) with
  | context [@decOpt (loose _)] => fail "density scorer unexpectedly checked loose x"
  | _ => exact I
  end.
Qed.

Fail QC Scorer no_such_scorer.
