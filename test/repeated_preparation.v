From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* Preparing a second test in the same proof declares helpers whose universe
   context includes levels the first preparation added to the proof. Merging
   that context again must not redeclare levels already in the environment
   ("AcyclicGraph...AlreadyDeclared" before the fix). *)

Inductive In' {A : Type} : A -> list A -> Prop :=
| In_here x l : In' x (x :: l)
| In_later x y l : In' x l -> In' x (y :: l).

Inductive sorted : list nat -> Prop :=
| s_nil : sorted []
| s_one n : sorted [n]
| s_cons n m l : n <= m -> sorted (m :: l) -> sorted (n :: m :: l).

Theorem repeated : forall (l : list nat) x, sorted l -> In' x l -> x <= 5.
Proof.
  quickchick 3.
  quickchick 3.
  Check theorem.
Abort.
