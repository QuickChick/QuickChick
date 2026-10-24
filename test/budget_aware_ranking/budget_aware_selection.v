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
QCDerive Generator for (fun x y => root x y).

Goal True.
  lazymatch (eval unfold GenSizedSuchThatroot in GenSizedSuchThatroot) with
  | context [@decOpt (loose _)] => exact I
  | _ => fail "BudgetAware ranking did not check loose x"
  end.
Qed.
