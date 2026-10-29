From QuickChick Require Import QuickChick.
Require Import ZArith.

Inductive limit : nat -> Prop := Limit : limit 2.

Inductive bounded : Z -> Z -> nat -> Prop :=
| Bounded : forall x y n,
    (x < y)%Z -> (y < Z.of_nat n)%Z -> bounded x y n.

#[local] Instance bounded_with_limit n :
  GenSizedSuchThat Z (fun y => bounded 0 y n) :=
  {| arbitrarySizeST := fun _ => returnGen (Some 1%Z) |}.

Inductive target : Z -> Prop :=
| Target : forall n y, limit n -> bounded 0 y n -> target y.

(* The two-output bounded mode needs an unavailable generator for Z.lt.
   Search must continue to limit first, then use bounded_with_limit. *)
QuickChick Derive ArbitrarySizedSuchThat for (fun y => target y).
Definition target_generator : GenSizedSuchThat Z (fun y => target y) :=
  ltac:(typeclasses eauto).

Goal True.
  lazymatch (eval unfold GenSizedSuchThattarget in GenSizedSuchThattarget) with
  | context [bounded_with_limit _] => exact I
  | _ => fail "the scheduled generator did not reuse bounded_with_limit"
  end.
Qed.
