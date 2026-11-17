From QuickChick Require Import QuickChick.

(* A custom list producer needs no producer for its elements. *)
#[local] Instance empty_lists {A : Type} : GenSized (list A) | 1 :=
  {| arbitrarySized := fun _ => returnGen nil |}.
Inductive list_container {A : Type} := ListContainer : list A -> @list_container A.
QuickChick Derive GenSized for list_container.
Definition container_without_elements {A : Type} : GenSized (@list_container A) :=
  GenSizedlist_container.
Fail Check GenSized_list_I.
Goal True.
  let body := eval unfold GenSizedlist_container in (@GenSizedlist_container nat) in
  lazymatch body with
  | context [@empty_lists _] => exact I
  | _ => fail "Expected the custom list dictionary"
  end.
Qed.

(* Inferred type arguments, permutation, repetition, and nested applications
   must preserve the complete premise, not just the parameter names. *)
Class Policy (A : Type) := { policy : bool }.
Inductive leaf {A : Type} : A -> Prop := Leaf : forall x, leaf x.
#[local] Instance leaf_check {A : Type} `{Policy A} (x : A) : DecOpt (leaf x) :=
  {| decOpt := fun _ => Some policy |}.
Inductive middle {A B : Type} : A -> B -> Prop :=
| Middle : forall x y, leaf (y, cons x nil) -> middle x y.
Inductive outer {A B : Type} : A -> B -> Prop :=
| Outer : forall x y, middle y (cons x nil) -> outer x y.
QuickChick Derive Checker for (@outer A B x y).
Definition inferred_arguments {A B : Type} `{Policy (list A * list B)} (x : A) (y : B) :
  DecOpt (outer x y) := DecOptouter x y.
Fail Definition wrong_order {A B : Type} `{Policy (list B * list A)} (x : A) (y : B) :
  DecOpt (outer x y) := ltac:(typeclasses eauto).
#[local] Instance exact_policy : Policy (list nat * list bool) := {| policy := false |}.
Example inferred_behavior : decOpt (P := outer 0 true) 4 = Some false.
Proof. reflexivity. Qed.
Inductive repeated {A : Type} : A -> Prop :=
| Repeated : forall x, middle x x -> repeated x.
QuickChick Derive Checker for (@repeated A x).
Definition repeated_argument {A : Type} `{Policy (A * list A)} (x : A) :
  DecOpt (repeated x) := ltac:(typeclasses eauto).

(* Type inputs need not be declared as inductive parameters or named binders. *)
Inductive type_index : Type -> Type := Pack : forall A, A -> type_index A.
QuickChick Derive GenSized for type_index.
Definition type_index_generic {A : Type} `{GenSized A} : GenSized (type_index A) :=
  ltac:(typeclasses eauto).
Fail Definition type_index_missing {A : Type} : GenSized (type_index A) :=
  ltac:(typeclasses eauto).
Inductive named_index : forall A : Type, Type := NamedPack : forall A, A -> named_index A.
QuickChick Derive GenSized for named_index.
Definition named_index_generic {A : Type} `{GenSized A} : GenSized (named_index A) :=
  ltac:(typeclasses eauto).
