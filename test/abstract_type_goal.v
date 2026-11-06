From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* A goal over an abstract type has no type to generate values of: quickchick
   reports it as a user error instead of failing during parsing. *)

Theorem rev_rev_any : forall (A : Type) `{Gen A} `{Dec_Eq A} (l : list A),
  rev (rev l) = l.
Proof. Fail quickchick 3. Abort.

Section Abstract.
  Variable A : Type.
  Context `{Gen A} `{Dec_Eq A}.
  Theorem rev_rev_section : forall (l : list A), rev (rev l) = l.
  Proof. Fail quickchick 3. Abort.
End Abstract.

Theorem rev_rev_nat : forall (l : list nat), rev (rev l) = l.
Proof. quickchick 3. Abort.
