From QuickChick Require Import QuickChick.

(* A constructor whose conclusion applies a class method to a variable,
   translated from Specimen's HashesTo (SpecimenTest/PolymorphicDepConstraints
   at 121cf234). Scheduling it once failed with "Failed to construct state". *)

Class MyHashable (A : Type) := { myHash : A -> nat }.

Inductive HashesTo (A : Type) `{MyHashable A} : A -> nat -> Prop :=
| MkHashesTo : forall x, HashesTo A x (myHash x).

#[local] Instance nat_hash : MyHashable nat := {| myHash n := n + 1 |}.

QCDerive Generator for (fun h => HashesTo nat x h).

Theorem hash_of_three : forall h, HashesTo nat 3 h -> h = 4.
Proof. quickchick 3. Abort.
