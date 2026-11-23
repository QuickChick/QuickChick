(* Under BudgetAware, counts can grow around a cycle of modes. The fixed
   point widens a growing count to unbounded, then narrows: later rounds
   recompute it, and it settles at its exact value. Reaching the round limit
   is made an error here, so both cycles must settle. *)
From QuickChick Require Import QuickChick.
Set Warnings "+quickchick-fixed-point-unsettled".
QC Scorer budget_aware.

(* No schedule avoids the cycle: P's enumerator produces k only through Q's
   and Q's only through P's, and each also enumerates x. The fabrication
   counts satisfy P = Q + 1 and Q = P + 1, so they are unbounded. *)
Inductive fn_box := FnBox : (nat -> nat) -> fn_box.
Definition box_s := FnBox S.
Definition box_p := FnBox pred.
Inductive P : nat -> fn_box -> Prop :=
| P0 : P 0 box_s
| PS : forall n k x, Q n k -> Nat.even x = true -> P (S n) k
with Q : nat -> fn_box -> Prop :=
| Q0 : Q 0 box_p
| QS : forall n k x, P n k -> Nat.even x = true -> Q (S n) k.
QuickChick Derive Enumerator for (fun k => P n k).

(* Here k can also come from R, at a fixed cost of three. The counts first
   grow, are widened, and then settle at min(3, other) + 1 = 4. *)
Parameter T : Type.
Parameter t0 t1 : T.
Axiom T_dec_eq : Dec_Eq T.
#[global] Existing Instance T_dec_eq.
Inductive R : T -> Prop :=
| R1 : forall x y z, Nat.even x = true -> Nat.even y = true -> Nat.even z = true -> R t0.
Inductive P' : nat -> T -> Prop :=
| P'0 : P' 0 t0
| P'S : forall n k x, Q' n k -> R k -> Nat.even x = true -> P' (S n) k
with Q' : nat -> T -> Prop :=
| Q'0 : Q' 0 t1
| Q'S : forall n k x, P' n k -> R k -> Nat.even x = true -> Q' (S n) k.
QuickChick Derive Enumerator for (fun k => P' n k).
