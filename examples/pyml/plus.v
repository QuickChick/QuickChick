From QuickChick Require Import QuickChick.

QCInclude ".".

Parameter plus' : nat -> nat -> nat.

Extract Constant plus' => "Extract.plus".

Definition plus_prop x y :=
  plus' x y = x + y?.

(*! QuickChick plus_prop. *)
