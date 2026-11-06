From QuickChick Require Import QuickChick.
Inductive registered : bool -> Prop := Reg : registered true.
Derive Inductive Schedule registered derive "Check" opt "true".
Definition resolved_checker : DecOpt (registered true) := ltac:(typeclasses eauto).
Example accepts : decOpt (P := registered true) 3 = Some true.
Proof. reflexivity. Qed.
Example rejects : decOpt (P := registered false) 3 = Some false.
Proof. reflexivity. Qed.
Inductive tiny := L | N : tiny -> tiny.
Derive Inductive Schedule tiny derive "Gen" opt "false".
Definition resolved_gen : GenSized tiny := ltac:(typeclasses eauto).
Derive Inductive Schedule tiny derive "Enum" opt "false".
Definition resolved_enum : EnumSized tiny := ltac:(typeclasses eauto).
Inductive only_true : bool -> Prop := OnlyTrue : only_true true.
Derive Inductive Schedule only_true 0 derive "Gen" opt "true".
Definition constrained_gen : GenSizedSuchThat bool only_true := ltac:(typeclasses eauto).
Derive Inductive Schedule only_true 0 derive "Enum" opt "true".
Definition constrained_enum : EnumSizedSuchThat bool only_true := ltac:(typeclasses eauto).

Inductive two_outputs : bool -> bool -> Prop := TwoOutputs : two_outputs true false.
Derive Inductive Schedule two_outputs 0 1 derive "Gen" opt "true".
Definition pair_generator : GenSizedSuchThat (bool * bool) (fun '(x, y) => two_outputs x y) :=
  ltac:(typeclasses eauto).

Inductive even_rel : nat -> Prop :=
| EvenZero : even_rel 0
| EvenNext : forall n, odd_rel n -> even_rel (S n)
with odd_rel : nat -> Prop :=
| OddNext : forall n, even_rel n -> odd_rel (S n).
Derive Inductive Schedule even_rel derive "Check" opt "true".
Definition mutual_checker : DecOpt (odd_rel 1) := ltac:(typeclasses eauto).
Example mutual_accepts : decOpt (P := odd_rel 1) 5 = Some true.
Proof. reflexivity. Qed.
Example mutual_rejects : decOpt (P := odd_rel 0) 5 = Some false.
Proof. reflexivity. Qed.

Example generator_uses_helper : arbitrarySized (A := tiny) 3 = GenSized_tiny_ 3.
Proof. reflexivity. Qed.
Example enumerator_uses_helper : enumSized (A := tiny) 3 = EnumSized_tiny_ 3.
Proof. reflexivity. Qed.

Inductive parameterized (A : Type) : A -> Prop := Parameterized : forall a, parameterized A a.
Derive Inductive Schedule parameterized derive "Check" opt "true".
Definition parameterized_bool : DecOpt (parameterized bool true) := ltac:(typeclasses eauto).
Example parameterized_accepts : decOpt (P := parameterized bool true) 3 = Some true.
Proof. reflexivity. Qed.

Inductive child_relation : bool -> Prop := ChildTrue : child_relation true.
Inductive parent_relation : bool -> Prop :=
| Parent : forall b, child_relation b -> parent_relation b.
Derive Inductive Schedule parent_relation derive "Check" opt "true".
Example parent_accepts : decOpt (P := parent_relation true) 5 = Some true.
Proof. reflexivity. Qed.
Example parent_rejects : decOpt (P := parent_relation false) 5 = Some false.
Proof. reflexivity. Qed.
Goal True.
  let body := eval unfold DecOpt_parent_relation_I in DecOpt_parent_relation_I in
  lazymatch body with
  | context [DecOpt_child_relation_I] => fail "Direct call across SCCs"
  | context [@decOpt (child_relation _) _ _] => exact I
  | _ => fail "Expected a class-method call across SCCs"
  end.
Qed.
