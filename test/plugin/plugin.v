From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* TODO: better naming *)

Inductive foo {A : Type} :=
| bar : A -> foo -> foo
| baz : foo
.

Derive (Arbitrary, Show) for foo.
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
  returnGen 1.
Definition b : G nat :=
  v <- a ;;
  returnGen v.

Sample a.
Sample b.
Sample (liftM Some a).

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
