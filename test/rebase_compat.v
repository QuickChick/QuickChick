From QuickChick Require Import QuickChick.

Inductive legacy_tree :=
| LegacyLeaf
| LegacyNode : legacy_tree -> legacy_tree -> legacy_tree.

Derive (Arbitrary, Show, Sized) for legacy_tree.

Definition legacy_generator : GenSized legacy_tree := ltac:(typeclasses eauto).
Definition legacy_shrinker : Shrink legacy_tree := ltac:(typeclasses eauto).

Inductive canonical_tree :=
| CanonicalLeaf
| CanonicalNode : canonical_tree -> canonical_tree -> canonical_tree.

QCDerive (Arbitrary, Show, Sized) for canonical_tree.

Definition canonical_generator : GenSized canonical_tree := ltac:(typeclasses eauto).

Inductive accepts : bool -> Prop := AcceptsTrue : accepts true.
QCDerive DecOpt for (accepts b).
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
QCDerive (Arbitrary, EnumSized, Show, Sized) for left_tree.
Definition right_generator : GenSized right_tree := ltac:(typeclasses eauto).
Definition right_shrinker : Shrink right_tree := ltac:(typeclasses eauto).
Definition right_enumerator : EnumSized right_tree := ltac:(typeclasses eauto).
Definition right_printer : Show right_tree := ltac:(typeclasses eauto).
Definition right_size : Sized right_tree := ltac:(typeclasses eauto).
