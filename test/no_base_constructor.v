From QuickChick Require Import QuickChick.

(* An unconstrained generator for a type whose constructors all take a
   recursive argument has nothing to produce when its fuel runs out. The
   derivation reports the type instead of failing to elaborate. [Fail]
   does not catch anomalies. *)

Inductive endless := More : endless -> endless.

Fail QCDerive GenSized for endless.

(* The same holds for one member of a mutual group, even when the other
   member has a base constructor. *)
Inductive no_base_left (A : Type) :=
| NLeaf : A -> no_base_left A
| NLeft : no_base_right A -> no_base_left A
with no_base_right (A : Type) :=
| NRight : no_base_left A -> no_base_right A.

Fail QCDerive GenSized for no_base_left.
