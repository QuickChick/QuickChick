From Coq Require Import derive.Derive.
From QuickChick Require Import QuickChick.

Derive stdlib_value SuchThat (stdlib_value = 3) As stdlib_value_correct.
Proof. subst stdlib_value. reflexivity. Qed.
Example stdlib_value_reduces : stdlib_value = 3.
Proof. reflexivity. Qed.

Inductive qc_tree := QCLeaf | QCNode : qc_tree -> qc_tree.
QuickChick Derive (Arbitrary, Show, Sized) for qc_tree.
Definition qc_generator : GenSized qc_tree := ltac:(typeclasses eauto).

Inductive parser_accepts : bool -> Prop := ParserAccepts : parser_accepts true.
Derive Inductive Schedule parser_accepts derive "Check" opt "true".
Example parser_checker : DecOpt_parser_accepts_I 3 false = Some false.
Proof. reflexivity. Qed.

Inductive qc_short := QCShort | QCShortNode : qc_short -> qc_short.
QC Derive (Arbitrary, Show) for qc_short.
Definition qc_short_generator : GenSized qc_short := ltac:(typeclasses eauto).
