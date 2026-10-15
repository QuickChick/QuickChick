From QuickChick Require Import QuickChick.

(* A user checker contributes its exact requirement to the caller. *)
Class Marker (A : Type) := { marker : bool; marker_tag : nat }.
Inductive child (A : Type) : A -> Prop := Child : forall x, child A x.
#[local] Instance child_checker (A : Type) `{Marker A} (x : A) : DecOpt (child A x) :=
  {| decOpt := fun _ => Some marker |}.
Inductive parent (A : Type) : A -> Prop := Parent : forall x, child A x -> parent A x.
Derive Inductive Schedule parent derive "Check" opt "true".
Definition parent_generic (A : Type) (m : Marker A) (x : A) : DecOpt (parent A x) := ltac:(typeclasses eauto).
#[local] Instance marker_bool : Marker bool := {| marker := false; marker_tag := 0 |}.
Example uses_marker : decOpt (P := parent bool true) 3 = Some false.
Proof. reflexivity. Qed.
Fail Check DecOpt_child_II.

Fail Definition parent_without_marker (A : Type) (x : A) : DecOpt (parent A x) :=
  ltac:(typeclasses eauto).

(* Two type parameters: only Marker (list B) is needed, not Marker A or B. *)
Inductive nested_parent (A B : Type) : A -> B -> Prop :=
| NestedParent : forall x y, child (list B) (cons y nil) -> nested_parent A B x y.
Derive Inductive Schedule nested_parent derive "Check" opt "true".
Definition nested_generic (A B : Type) (m : Marker (list B)) (x : A) (y : B)
  : DecOpt (nested_parent A B x y) := ltac:(typeclasses eauto).
(* The same requirement crosses two generated components, with substitution. *)
Inductive middle (A : Type) : A -> Prop := Middle : forall x, child A x -> middle A x.
Inductive outer (A B : Type) : A -> B -> Prop :=
| Outer : forall x y, middle (list B) (cons y nil) -> outer A B x y.
Derive Inductive Schedule outer derive "Check" opt "true".
Definition outer_generic (A B : Type) (m : Marker (list B)) (x : A) (y : B)
  : DecOpt (outer A B x y) := ltac:(typeclasses eauto).
Fail Definition nested_without_marker (A B : Type) (x : A) (y : B) :
  DecOpt (nested_parent A B x y) := ltac:(typeclasses eauto).
#[local] Instance marker_list_bool : Marker (list bool) :=
  {| marker := false; marker_tag := 0 |}.
Example nested_uses_marker : decOpt (P := nested_parent nat bool 0 true) 3 = Some false.
Proof. reflexivity. Qed.
Example outer_uses_marker : decOpt (P := outer nat bool 0 true) 3 = Some false.
Proof. reflexivity. Qed.

(* Mutual requirements reach a fixed point; check the actual supplied method. *)
Inductive peven (A : Type) : A -> nat -> Prop :=
| PZero : forall x, child A x -> peven A x 0
| PEven : forall x n, podd A x n -> peven A x (S n)
with podd (A : Type) : A -> nat -> Prop :=
| POdd : forall x n, peven A x n -> podd A x (S n).
Derive Inductive Schedule podd derive "Check" opt "true".
Definition mutual_generic (A : Type) (m : Marker A) (x : A) : DecOpt (podd A x 1) := ltac:(typeclasses eauto).
Example mutual_uses_marker : decOpt (P := podd bool true 1) 5 = Some false.
Proof. reflexivity. Qed.
(* Generator and enumerator requirements stay distinct. *)
Inductive box (A : Type) := Box : A -> box A.
Derive Inductive Schedule box derive "Gen" opt "false".
Definition gen_box (A : Type) (g : GenSized A) : GenSized (box A) := ltac:(typeclasses eauto).
Derive Inductive Schedule box derive "Enum" opt "false".
Definition enum_box (A : Type) (g : EnumSized A) : EnumSized (box A) := ltac:(typeclasses eauto).
(* Equality requirements are discovered from registered instances. *)
Inductive contains (A : Type) : A -> list A -> Prop :=
| Here : forall x xs, contains A x (cons x xs)
| There : forall x y xs, contains A x xs -> contains A x (cons y xs).
Derive Inductive Schedule contains derive "Check" opt "true".
Definition contains_generic (A : Type) (d : Dec_Eq A) (x : A) (xs : list A)
  : DecOpt (contains A x xs) := ltac:(typeclasses eauto).
Example contains_true : decOpt (P := contains bool true (cons false (cons true nil))) 5 = Some true.
Proof. reflexivity. Qed.
Example contains_false : decOpt (P := contains bool true (cons false nil)) 5 = Some false.
Proof. reflexivity. Qed.

(* A concrete instance must not specialize an abstract argument during lookup. *)
Inductive specialized_child (A : Type) : A -> Prop :=
| SpecializedChild : forall x, specialized_child A x.
#[local] Instance bool_child (x : bool) : DecOpt (specialized_child bool x) | 1 :=
  {| decOpt := fun _ => Some false |}.
Inductive specialized_parent (A : Type) : A -> Prop :=
| SpecializedParent : forall x, specialized_child A x -> specialized_parent A x.
Derive Inductive Schedule specialized_parent derive "Check" opt "true".
Definition unspecialized (A : Type) (x : A) : DecOpt (specialized_parent A x) :=
  ltac:(typeclasses eauto).
Example specialized_still_used : decOpt (P := specialized_child bool true) 3 = Some false.
Proof. reflexivity. Qed.
Example other_type_works : decOpt (P := specialized_parent nat 0) 3 = Some true.
Proof. reflexivity. Qed.

(* Later binder types retain their earlier index after scheduling. *)
From Coq Require Import Vectors.Vector.
Inductive indexed (A : Type) : forall n : nat, Vector.t A n -> Prop :=
| Indexed : forall n xs, indexed A n xs.
Derive Inductive Schedule indexed derive "Check" opt "true".
Definition indexed_generic (A : Type) (n : nat) (xs : Vector.t A n) :
  DecOpt (indexed A n xs) := ltac:(typeclasses eauto).

(* Generated declarations honor universe polymorphism. *)
Set Universe Polymorphism.
Inductive universe_relation@{u} (A : Type@{u}) : A -> Prop :=
| UniverseRelation : forall x, universe_relation A x.
Derive Inductive Schedule universe_relation derive "Check" opt "true".
Definition universe_generic@{u} (A : Type@{u}) (x : A) :
  DecOpt (universe_relation A x) := ltac:(typeclasses eauto).
Check DecOpt_universe_relation_II@{Set}.
Unset Universe Polymorphism.

(* Requirements may mention a fixed index inside the type argument. *)
Inductive indexed_child (A : Type) : forall n : nat, Vector.t A n -> Prop :=
| IndexedChild : forall n xs, indexed_child A n xs.
#[local] Instance indexed_child_checker (A : Type) (n : nat)
  (m : Marker (Vector.t A n)) (xs : Vector.t A n) : DecOpt (indexed_child A n xs) :=
  {| decOpt := fun _ => Some marker |}.
Inductive indexed_parent (A : Type) : forall n : nat, Vector.t A n -> Prop :=
| IndexedParent : forall n xs, indexed_child A n xs -> indexed_parent A n xs.
Set Printing Universes.
Derive Inductive Schedule indexed_parent derive "Check" opt "true".
Unset Printing Universes.
Definition indexed_parent_generic (A : Type) (n : nat)
  (m : Marker (Vector.t A n)) (xs : Vector.t A n) : DecOpt (indexed_parent A n xs) :=
  ltac:(typeclasses eauto).
#[local] Instance marker_vector : Marker (Vector.t bool 0) :=
  {| marker := false; marker_tag := 0 |}.
Example indexed_uses_marker :
  decOpt (P := indexed_parent bool 0 (Vector.nil bool)) 3 = Some false.
Proof. reflexivity. Qed.
Fail Check DecOpt_indexed_child_III.

(* A surrounding parameter with the same name must not solve a generic premise. *)
Inductive shadow_parent (A : Type) : A -> Prop :=
| ShadowParent : forall x, child A x -> shadow_parent A x.
Section ShadowedParameter.
  Context (A : Type) (outer_marker : Marker A).
  Derive Inductive Schedule shadow_parent derive "Check" opt "true".
End ShadowedParameter.
Definition shadow_generic (B : Type) (m : Marker B) (x : B) :
  DecOpt (shadow_parent B x) := ltac:(typeclasses eauto).
Example shadow_uses_marker : decOpt (P := shadow_parent bool true) 3 = Some false.
Proof. reflexivity. Qed.

(* Library instances propagate requirements through an applied type. *)
Inductive list_box (A : Type) := ListBox : list A -> list_box A.
Derive Inductive Schedule list_box derive "Gen" opt "false".
Definition list_box_generic (A : Type) (g : GenSized A) : GenSized (list_box A) :=
  ltac:(typeclasses eauto).

(* A type parameter is an input, even when multiple term arguments are outputs. *)
Inductive any_pair (A : Type) : A -> A -> Prop :=
| AnyPair : forall x y, any_pair A x y.
Derive Inductive Schedule any_pair 1 2 derive "Gen" opt "true".
Definition pair_generic (A : Type) (g : GenSized A) :
  GenSizedSuchThat (A * A) (fun '(x, y) => any_pair A x y) := ltac:(typeclasses eauto).
