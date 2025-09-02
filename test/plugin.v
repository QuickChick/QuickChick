From QuickChick Require Import QuickChick.
From Coq Require Import Derive.

(* Check that this [Derive] still works *)
Derive X SuchThat (X = 1) As eqX.
Abort.

Inductive foo {A : Type} :=
| bar : A -> foo -> foo
| baz : foo
.

Derive Instance (Arbitrary, Show) for foo.
Sample (arbitrary : G foo).

Section Sanity.

  Inductive qux : Type :=
  | Qux: forall {A: Type}, A -> qux.

  Definition quux: qux -> bool :=
    fun a => match a with | Qux a => true end.

End Sanity.

Section Failures.

  Set Asymmetric Patterns.

  Fail Definition quux': qux -> bool :=
    fun a => match a with | Qux a => true end.

End Failures.

Import MonadNotation.

Definition a : G nat :=
  ret 1.
Definition b : G nat :=
  v <- a ;;
  ret v.

Import BindOptNotation.

Definition c : G (option nat) :=
  ret (Some 42).
Definition d : G (option nat) :=
  v <-- c;;
  ret (Some v).

Sample a.
Sample b.
Sample (liftM Some a).
Sample c.
Sample d.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrnat div.

QuickChick
   (fun (s : nat) (t : nat) =>
      eqn
        (gcdn s t)
        (gcdn t s)).

(* Test extraction hack (substitute type int = int) *)
Definition int := nat.
Definition teh := fun x : int => Nat.eqb x x.
QuickChick teh.
