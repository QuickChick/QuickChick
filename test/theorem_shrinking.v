From QuickChick Require Import QuickChick.
Require Import String List. Import ListNotations.

(* A theorem test shrinks a failing unconstrained variable with its Shrink
   instance. A shrunk value that breaks a later hypothesis check is
   discarded, so it never becomes the reported counterexample. *)

Theorem short_lists : forall (l : list nat), length l < 2.
Proof.
  quickchick 3.
  match goal with
  | h := ?body |- _ => lazymatch body with context [forAllShrink] => idtac end
  | _ => fail "the theorem test does not shrink its variable"
  end.
Abort.

Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).

Theorem checked_variable : forall n m : nat, le' n m -> n + m < 4.
Proof. quickchick 3. Abort.

(* A type without a Shrink instance is generated but not shrunk. *)
Inductive opaque := A | B.

#[local] Instance show_opaque : Show opaque :=
  {| show x := match x with A => "A"%string | B => "B"%string end |}.
#[local] Instance gen_opaque : Gen opaque := {| arbitrary := elems_ A [A; B] |}.

Theorem no_shrink_instance : forall (x : opaque) (n : nat), n < 2.
Proof. quickchick 3. Abort.
