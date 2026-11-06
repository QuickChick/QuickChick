From QuickChick Require Import QuickChick LazyList Enumerators.
From Coq Require Import List.
Import ListNotations.

(* Constructor conclusions that apply a function, such as [dbl n (double n)]
   or [ev (n + 2)]. The scheduler reads each application as a fresh variable
   with an equality premise, so every mode can be derived. These once failed
   with "expected a constructor pattern". *)

Fixpoint double (n : nat) : nat :=
  match n with 0 => 0 | S m => S (S (double m)) end.

Inductive dbl : nat -> nat -> Prop :=
| Dbl : forall n, dbl n (double n).

QC Derive Checker for (dbl n m).
QC Derive Generator for (fun m => dbl n m).
QC Derive Generator for (fun n => dbl n m).
QC Derive Enumerator for (fun m => dbl n m).
QC Derive Enumerator for (fun n => dbl n m).

Example dbl_accepts : decOpt (P := dbl 3 6) 10 = Some true.
Proof. vm_compute. reflexivity. Qed.
Example dbl_rejects : decOpt (P := dbl 3 5) 10 = Some false.
Proof. vm_compute. reflexivity. Qed.

Example dbl_computes_output :
  LazyList_to_list (run (@enumSizeST _ (fun m => dbl 4 m) _ 3) 3) = [Some 8].
Proof. vm_compute. reflexivity. Qed.
Example dbl_inverts_output :
  LazyList_to_list (run (@enumSizeST _ (fun n => dbl n 6) _ 3) 3) = [Some 3].
Proof. vm_compute. reflexivity. Qed.

Inductive ev : nat -> Prop :=
| Ev0 : ev 0
| EvSS : forall n, ev n -> ev (n + 2).

QC Derive Generator for (fun n => ev n).
QC Derive Checker for (ev n).

(* The checker enumerates the n with ev n; lazy evaluation keeps the fuel's
   unused branches unevaluated. *)
Example ev_checker_accepts : decOpt (P := ev 2) 1 = Some true.
Proof. lazy. reflexivity. Qed.

Theorem ev_even : forall n, ev n -> Nat.even n = true.
Proof. quickchick 5. Abort.
