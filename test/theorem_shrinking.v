From QuickChick Require Import QuickChick.
Require Import String List. Import ListNotations.

(* A theorem test shrinks a failing unconstrained variable with its Shrink
   instance. A shrunk value that breaks a later hypothesis check is
   discarded, so it never becomes the reported counterexample. Outputs of a
   producing hypothesis are shrunk to values that an existing checker
   confirms still satisfy it. *)

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

Inductive sorted : list nat -> Prop :=
| SNil : sorted []
| SOne x : sorted [x]
| SCons x y l : x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

QCDerive Checker for (sorted l).

Theorem short_sorted : forall l, sorted l -> length l < 3.
Proof.
  quickchick 3.
  match goal with
  | h := ?body |- _ => lazymatch body with context [theoremForAllST] => idtac end
  | _ => fail "the theorem test does not shrink the hypothesis's output"
  end.
Abort.

(* Shrinks of (n, m) are kept only when le' n m holds. *)
QCDerive Checker for (le' n m).

Example kept_shrinks :
  List.filter (fun '(n, m) => match theoremHypCheck (P := le' n m) 100 with
                              | Some true => true
                              | _ => false
                              end) (shrink (3, 3))
  = [(1, 3); (0, 3)].
Proof. vm_compute. reflexivity. Qed.

(* A type without a Shrink instance is generated but not shrunk. *)
Inductive opaque := A | B.

#[local] Instance show_opaque : Show opaque :=
  {| show x := match x with A => "A"%string | B => "B"%string end |}.
#[local] Instance gen_opaque : Gen opaque := {| arbitrary := elems_ A [A; B] |}.

Theorem no_shrink_instance : forall (x : opaque) (n : nat), n < 2.
Proof. quickchick 3. Abort.
