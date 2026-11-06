From QuickChick Require Import QuickChick.
From QuickChick Require Import LazyList.
(* GenSizedSuchThat NoWitness -> DecOpt HasWitness -> constrained enumeration
   of Accepts -> EnumSized (enum_box A) -> EnumSized A. *)
Inductive enum_box (A : Type) := EnumBox : A -> enum_box A.
Derive Inductive Schedule enum_box derive "Enum" opt "false".
Inductive Accepts (A : Type) : A -> enum_box A -> Prop :=
| AcceptsAny : forall x y, Accepts A x y.
#[local] Instance accepts_checker (A : Type) (x : A) (y : enum_box A) :
  DecOpt (Accepts A x y) := {| decOpt := fun _ => Some true |}.
Inductive HasWitness (A : Type) : A -> Prop :=
| Witness : forall x y, Accepts A x y -> HasWitness A x.
Derive Inductive Schedule HasWitness derive "Check" opt "true".
Definition witness_generic (A : Type) `{EnumSized A} (x : A) :
  DecOpt (HasWitness A x) := ltac:(typeclasses eauto).
Fail Definition checker_without_enum (A : Type) (x : A) :
  DecOpt (HasWitness A x) := ltac:(typeclasses eauto).
Inductive NoWitness (A : Type) : A -> Prop :=
| NoWitnessIntro : forall x, ~ HasWitness A x -> NoWitness A x.
Derive Inductive Schedule NoWitness 1 derive "Gen" opt "true".
Definition generator_generic (A : Type) `{GenSized A} `{EnumSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) := ltac:(typeclasses eauto).
Fail Definition generator_without_enum (A : Type) `{GenSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) := ltac:(typeclasses eauto).
Definition empty_enum : EnumSized bool :=
  {| enumSized := fun _ => MkEnum (fun _ => lnil) |}.
Definition singleton_enum : EnumSized bool :=
  {| enumSized := fun _ => returnEnum true |}.
Example empty_has_no_witness :
  @decOpt (HasWitness bool false) (@DecOpt_HasWitness_II_instance bool false empty_enum) 3 = Some false.
Proof. reflexivity. Qed.
Example singleton_has_witness :
  @decOpt (HasWitness bool false) (@DecOpt_HasWitness_II_instance bool false singleton_enum) 3 = Some true.
Proof. reflexivity. Qed.
(* Calling the wrapper directly must infer both class arguments. *)
Definition implicit_chain (A : Type) `{GenSized A} `{EnumSized A} :
  GenSizedSuchThat A (fun x => NoWitness A x) :=
  GenSizedSuchThat_NoWitness_IO_instance.
