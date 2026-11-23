From QuickChick Require Import QuickChick.

(* Relations with the same base name in different modules stay distinct
   (issue #311): a premise that mentions M1.Test is not a recursive call of
   the Test being derived. *)
Module M1.
  Inductive Test : bool -> Prop := T : Test true.
End M1.

Module M2.
  Inductive Test : nat -> Prop := T : M1.Test true -> Test 1.
  QC Derive Checker for (Test n).
  (* M1's relation, derived where Test means M2.Test. *)
  QC Derive Checker for (M1.Test b).
End M2.

Module M3.
  Inductive Test (b : bool) : Prop := T : M1.Test b -> Test b.
  QC Derive Checker for (Test b).
  QC Derive Generator for (fun b => Test b).
End M3.

Example checks :
  (decOpt (P := M2.Test 1) 5, decOpt (P := M2.Test 0) 5,
   decOpt (P := M1.Test true) 5, decOpt (P := M1.Test false) 5,
   decOpt (P := M3.Test true) 5, decOpt (P := M3.Test false) 5)
  = (Some true, Some false, Some true, Some false, Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

Sample (@arbitrarySizeST _ (fun b => M3.Test b) _ 3).
