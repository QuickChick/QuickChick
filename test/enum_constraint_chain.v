From QuickChick Require Import QuickChick.
From QuickChick Require Import LazyList.
(* GenSizedSuchThat NoWitness -> DecOpt HasWitness -> constrained enumeration
   of Accepts -> Enum (enum_box A) -> Enum A. *)
Inductive enum_box (A : Type) := EnumBox : A -> enum_box A.
QuickChick Derive EnumSized for enum_box.
Inductive Accepts (A : Type) : A -> enum_box A -> Prop :=
| AcceptsAny : forall x y, Accepts A x y.
#[local] Instance accepts_checker (A : Type) (x : A) (y : enum_box A) :
  DecOpt (Accepts A x y) := {| decOpt := fun _ => Some true |}.
Inductive HasWitness (A : Type) : A -> Prop :=
| Witness : forall x y, Accepts A x y -> HasWitness A x.
QuickChick Derive Checker for (@HasWitness A x).
Definition witness_generic (A : Type) `{EnumSized A} (x : A) :
  DecOpt (HasWitness A x) := ltac:(typeclasses eauto).
Fail Definition checker_without_enum (A : Type) (x : A) :
  DecOpt (HasWitness A x) := ltac:(typeclasses eauto).
Inductive NoWitness (A : Type) : A -> Prop :=
| NoWitnessIntro : forall x, ~ HasWitness A x -> NoWitness A x.
QuickChick Derive Generator for (fun x => @NoWitness A x).
Definition generator_generic (A : Type) `{GenSized A} `{EnumSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) := ltac:(typeclasses eauto).
Fail Definition generator_without_enum (A : Type) `{GenSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) := ltac:(typeclasses eauto).
Definition empty_enum : Enum bool :=
  {| enum := MkEnum (fun _ => lnil) |}.
Definition singleton_enum : Enum bool :=
  {| enum := returnEnum true |}.
(* The checker cannot tell an empty enumeration from one the size bound cut
   short, so with no witness it answers None. *)
Example empty_has_no_witness :
  @decOpt (HasWitness bool false) (@DecOptHasWitness bool false empty_enum) 3 = None.
Proof. reflexivity. Qed.
Example singleton_has_witness :
  @decOpt (HasWitness bool false) (@DecOptHasWitness bool false singleton_enum) 3 = Some true.
Proof. reflexivity. Qed.
(* Calling the instance directly must infer both class arguments. *)
Definition implicit_chain (A : Type) `{GenSized A} `{EnumSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) :=
  GenSizedSuchThatNoWitness.
