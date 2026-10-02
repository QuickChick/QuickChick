From QuickChick Require Import QuickChick.

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

Section ScheduledCheckerResults.

  Inductive checker_accepts : bool -> Prop :=
  | CheckerAcceptsTrue : checker_accepts true.

  Derive Inductive Schedule checker_accepts derive "Check" opt "true".

  Example checker_accepts_true :
    DecOpt_checker_accepts_I 5 true = Some true.
  Proof. reflexivity. Qed.

  Example checker_accepts_false :
    DecOpt_checker_accepts_I 5 false = Some false.
  Proof. reflexivity. Qed.

  Inductive checker_has_witness : unit -> Prop :=
  | CheckerHasWitness : forall b : bool, checker_has_witness tt.

  Derive Inductive Schedule checker_has_witness derive "Check" opt "true".

  Example checker_witness_found :
    DecOpt_checker_has_witness_I 5 tt = Some true.
  Proof. reflexivity. Qed.

  Definition checker_bool_enum_with_none : E (option bool) :=
    enumerate
      (returnEnum None ::
       bindEnum (enumSized 5) (fun b => returnEnum (Some b)) :: nil).

  Example checker_search_inconclusive :
    enumeratingOpt checker_bool_enum_with_none (fun _ => Some false) 5 = None.
  Proof. reflexivity. Qed.

End ScheduledCheckerResults.
