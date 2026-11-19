From QuickChick Require Import QuickChick.
(* Derived checkers, generators and enumerators are typeclass instances. *)
Inductive registered : bool -> Prop := Reg : registered true.
QuickChick Derive Checker for (registered b).
Definition resolved_checker : DecOpt (registered true) := ltac:(typeclasses eauto).
Example accepts : decOpt (P := registered true) 3 = Some true.
Proof. reflexivity. Qed.
Example rejects : decOpt (P := registered false) 3 = Some false.
Proof. reflexivity. Qed.
Inductive tiny := L | N : tiny -> tiny.
QuickChick Derive GenSized for tiny.
Definition resolved_gen : GenSized tiny := ltac:(typeclasses eauto).
QuickChick Derive EnumSized for tiny.
Definition resolved_enum : EnumSized tiny := ltac:(typeclasses eauto).
Inductive only_true : bool -> Prop := OnlyTrue : only_true true.
QuickChick Derive Generator for (fun b => only_true b).
Definition constrained_gen : GenSizedSuchThat bool only_true := ltac:(typeclasses eauto).
QuickChick Derive Enumerator for (fun b => only_true b).
Definition constrained_enum : EnumSizedSuchThat bool only_true := ltac:(typeclasses eauto).

Inductive two_outputs : bool -> bool -> Prop := TwoOutputs : two_outputs true false.
QuickChick Derive Generator for (fun '(x, y) => two_outputs x y).
Definition pair_generator : GenSizedSuchThat (bool * bool) (fun '(x, y) => two_outputs x y) :=
  ltac:(typeclasses eauto).

Inductive even_rel : nat -> Prop :=
| EvenZero : even_rel 0
| EvenNext : forall n, odd_rel n -> even_rel (S n)
with odd_rel : nat -> Prop :=
| OddNext : forall n, even_rel n -> odd_rel (S n).
QuickChick Derive Checker for (odd_rel n).
Definition mutual_checker : DecOpt (odd_rel 1) := ltac:(typeclasses eauto).
Example mutual_accepts : decOpt (P := odd_rel 1) 5 = Some true.
Proof. reflexivity. Qed.
Example mutual_rejects : decOpt (P := odd_rel 0) 5 = Some false.
Proof. reflexivity. Qed.

Example generator_uses_helper : arbitrarySized (A := tiny) 3 = arbitrarySized_impl_tiny 3.
Proof. reflexivity. Qed.
Example enumerator_uses_helper : enumSized (A := tiny) 3 = enumSized_impl_tiny 3.
Proof. reflexivity. Qed.

Inductive parameterized (A : Type) : A -> Prop := Parameterized : forall a, parameterized A a.
QuickChick Derive Checker for (@parameterized A a).
Definition parameterized_bool : DecOpt (parameterized bool true) := ltac:(typeclasses eauto).
Example parameterized_accepts : decOpt (P := parameterized bool true) 3 = Some true.
Proof. reflexivity. Qed.

Inductive child_relation : bool -> Prop := ChildTrue : child_relation true.
Inductive parent_relation : bool -> Prop :=
| Parent : forall b, child_relation b -> parent_relation b.
QuickChick Derive Checker for (parent_relation b).
Example parent_accepts : decOpt (P := parent_relation true) 5 = Some true.
Proof. reflexivity. Qed.
Example parent_rejects : decOpt (P := parent_relation false) 5 = Some false.
Proof. reflexivity. Qed.
Goal True.
  let body := eval unfold DecOptparent_relation in DecOptparent_relation in
  lazymatch body with
  | context [@decOpt (child_relation _) _ _] => exact I
  | _ => fail "Expected a class-method call across SCCs"
  end.
Qed.
