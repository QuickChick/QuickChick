From QuickChick Require Import QuickChick.
Require Import Nat.

Inductive square_of_equiv : nat -> nat -> Prop :=
| sq' : forall n m,
    mult n n = m -> square_of_equiv n m.

Derive EnumSizedSuchThat for (fun n => square_of_equiv n m).
Derive DecOpt for (square_of_equiv n m).

Example equiv_1 :
  @decOpt (square_of_equiv 2 4) _ 42 = Some true.
Proof. reflexivity. Qed.
Example equiv_2 :
  @decOpt (square_of_equiv 2 5) _ 42 = Some false.
Proof. reflexivity. Qed.

Inductive square_of : nat -> nat -> Prop :=
| sq : forall n, square_of n (n * n).

Derive EnumSizedSuchThat for (fun n => square_of n m).
Derive DecOpt for (square_of n m).

Example sq_1 :
  @decOpt (square_of 2 4) _ 42 = Some true.
Proof. reflexivity. Qed.
Example sq_2 :
  @decOpt (square_of 2 5) _ 42 = Some false.
Proof. reflexivity. Qed.

