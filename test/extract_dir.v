From QuickChick Require Import QuickChick.

(* Tests extract into the directory set by QuickChick Extract Dir (or QC
   Extract Dir, or the older QCExtractDir). [Dir] is not a keyword. *)
Definition Dir := 1.

QuickChick Extract Dir "extract_dir_tests".
QuickChick (Nat.eqb Dir 1).

QC Extract Dir "extract_dir_tests_qc".
QuickChick (Nat.eqb Dir 1).

QCExtractDir "extract_dir_tests_old".
QuickChick (Nat.eqb Dir 1).

Fail QC Extract Directory "extract_dir_tests".
