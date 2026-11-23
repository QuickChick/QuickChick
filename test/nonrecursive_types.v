From QuickChick Require Import QuickChick.
From Coq Require Import List String.
Import ListNotations.

(* Records and Variants are not recursive types, so the simple derivers
   inline their functions into the instance instead of declaring a fixpoint
   over them, which Coq rejects. Issues #155 and #285. *)

Record point := { px : nat; py : nat }.
QC Derive (Show, Shrink, Arbitrary) for point.

Example show_point : show {| px := 1; py := 2 |} = "Build_point 1 2"%string.
Proof. reflexivity. Qed.

Variant color := Red | Green.
QC Derive (Show, Shrink, Arbitrary) for color.

Example show_color : show Green = "Green"%string.
Proof. reflexivity. Qed.
Example shrink_color : shrink Green = [].
Proof. reflexivity. Qed.

(* A parameter's instances are those of the enclosing instance. *)
Variant boxed (A : Type) := Boxed : A -> boxed A.
Arguments Boxed {A}.
QC Derive (Show, Shrink) for boxed.

Example show_boxed : show (Boxed 3) = "Boxed 3"%string.
Proof. reflexivity. Qed.
Example shrink_boxed : shrink (Boxed 2) = [Boxed 1; Boxed 0].
Proof. reflexivity. Qed.
