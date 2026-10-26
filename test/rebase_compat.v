From QuickChick Require Import LegacyDerive.

Inductive legacy_tree :=
| LegacyLeaf
| LegacyNode : legacy_tree -> legacy_tree -> legacy_tree.

Derive (Arbitrary, Show, Sized) for legacy_tree.

Definition legacy_generator : GenSized legacy_tree := ltac:(typeclasses eauto).
Definition legacy_shrinker : Shrink legacy_tree := ltac:(typeclasses eauto).

Inductive canonical_tree :=
| CanonicalLeaf
| CanonicalNode : canonical_tree -> canonical_tree -> canonical_tree.

QuickChick Derive (Arbitrary, Show, Sized) for canonical_tree.

Definition canonical_generator : GenSized canonical_tree := ltac:(typeclasses eauto).

Inductive accepts : bool -> Prop := AcceptsTrue : accepts true.
QuickChick Derive DecOpt for (accepts b).
Definition old_checker : DecOpt (accepts false) := ltac:(typeclasses eauto).
Example old_checker_accepts : decOpt (P := accepts true) 3 = Some true.
Proof. reflexivity. Qed.
Example old_checker_rejects : decOpt (P := accepts false) 3 = Some false.
Proof. reflexivity. Qed.

Inductive scheduled_accepts : bool -> Prop :=
| ScheduledAcceptsTrue : scheduled_accepts true.
Derive Inductive Schedule scheduled_accepts derive "Check" opt "true".
Example scheduled_checker_accepts :
  DecOpt_scheduled_accepts_I 3 true = Some true.
Proof. reflexivity. Qed.
Example scheduled_checker_rejects :
  DecOpt_scheduled_accepts_I 3 false = Some false.
Proof. reflexivity. Qed.

(* Master derives instances for both members of a mutual block. *)
Inductive left_tree := LeftLeaf | LeftNode : right_tree -> left_tree
with right_tree := RightLeaf | RightNode : left_tree -> right_tree.
QuickChick Derive (Arbitrary, EnumSized, Show, Sized) for left_tree.
Definition right_generator : GenSized right_tree := ltac:(typeclasses eauto).
Definition right_shrinker : Shrink right_tree := ltac:(typeclasses eauto).
Definition right_enumerator : EnumSized right_tree := ltac:(typeclasses eauto).
Definition right_printer : Show right_tree := ltac:(typeclasses eauto).
Definition right_size : Sized right_tree := ltac:(typeclasses eauto).

(* Keep the single-class and using forms available through the legacy import. *)
Inductive legacy_named_tree := LegacyNamedLeaf | LegacyNamedNode : legacy_named_tree -> legacy_named_tree.
Derive Show for legacy_named_tree using legacy_hint.
Derive Sized for legacy_named_tree using legacy_hint and legacy_other_hint.
Definition legacy_printer : Show legacy_named_tree := ltac:(typeclasses eauto).
Definition legacy_size : Sized legacy_named_tree := ltac:(typeclasses eauto).

Inductive legacy_accepts : bool -> Prop := LegacyAccepts : legacy_accepts true.
Derive DecOpt for (legacy_accepts b).
Definition legacy_checker : DecOpt (legacy_accepts false) := ltac:(typeclasses eauto).
Example legacy_checker_rejects : decOpt (P := legacy_accepts false) 3 = Some false.
Proof. reflexivity. Qed.
