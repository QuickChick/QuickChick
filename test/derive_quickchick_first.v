From QuickChick Require Import QuickChick.
From Coq Require Import derive.Derive.

Derive stdlib_value SuchThat (stdlib_value = 3) As stdlib_value_correct.
Proof. subst stdlib_value. reflexivity. Qed.
Example stdlib_value_reduces : stdlib_value = 3.
Proof. reflexivity. Qed.

Inductive qc_tree := QCLeaf | QCNode : qc_tree -> qc_tree.
QuickChick Derive (Arbitrary, Show, Sized) for qc_tree.
Definition qc_generator : GenSized qc_tree := ltac:(typeclasses eauto).

Inductive parser_accepts : bool -> Prop := ParserAccepts : parser_accepts true.
QuickChick Derive Checker for (parser_accepts b).
Example parser_checker : decOpt (P := parser_accepts false) 3 = Some false.
Proof. reflexivity. Qed.

Inductive qc_short := QCShort | QCShortNode : qc_short -> qc_short.
QC Derive (Arbitrary, Show) for qc_short.
Definition qc_short_generator : GenSized qc_short := ltac:(typeclasses eauto).
