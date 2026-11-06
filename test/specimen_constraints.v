From QuickChick Require Import QuickChick.

(* Translations of SpecimenTest/PolymorphicDepConstraints.lean, cases 1–3,
   at 121cf23435a17d93f1dde283daa62d2899628a8b. The generator obligations
   deliberately assume no EnumSized instance. Bound derivation time to catch
   nontermination in requirement propagation. *)
Inductive MyContains (A : Type) : A -> list A -> Prop :=
| Here : forall x xs, MyContains A x (cons x xs)
| There : forall x y xs, MyContains A x xs -> MyContains A x (cons y xs).
Inductive NotIn (A : Type) : A -> list A -> Prop :=
| MkNotIn : forall x xs, ~ MyContains A x xs -> NotIn A x xs.
Timeout 30 Derive Inductive Schedule MyContains derive "Check" opt "true".
Timeout 30 Derive Inductive Schedule NotIn 1 derive "Gen" opt "true".
Definition notin_requirements (A : Type) `{GenSized A} `{Dec_Eq A} (xs : list A) :
  GenSizedSuchThat A (fun x => NotIn A x xs) := ltac:(typeclasses eauto).
Inductive AllEq (A : Type) : A -> list A -> Prop :=
| AllEqNil : forall x, AllEq A x nil
| AllEqCons : forall x xs, AllEq A x xs -> AllEq A x (cons x xs).
Inductive HasAllEq (A : Type) : list A -> Prop :=
| MkHasAllEq : forall x xs, AllEq A x xs -> HasAllEq A (cons x xs).
Timeout 30 Derive Inductive Schedule AllEq derive "Check" opt "true".
Timeout 30 Derive Inductive Schedule HasAllEq 1 derive "Gen" opt "true".
Definition alleq_requirements (A : Type) `{GenSized A} `{Dec_Eq A} :
  GenSizedSuchThat (list A) (fun xs => HasAllEq A xs) := ltac:(typeclasses eauto).
Inductive ListHead (A : Type) : A -> list A -> Prop :=
| MkListHead : forall x xs, ListHead A x (cons x xs).
Inductive HasHead (A : Type) : list A -> Prop :=
| MkHasHead : forall xs x, ListHead A x xs -> HasHead A xs.
Timeout 30 Derive Inductive Schedule ListHead derive "Check" opt "true".
Timeout 30 Derive Inductive Schedule HasHead 1 derive "Gen" opt "true".
Definition head_requirements (A : Type) `{GenSized A} `{Dec_Eq A} :
  GenSizedSuchThat (list A) (fun xs => HasHead A xs) := ltac:(typeclasses eauto).

(* Specimen's user-supplied two-output producer must be reused. *)
Inductive Sums : nat -> nat -> nat -> Prop :=
| MkSums : forall a b n, a + b = n -> Sums a b n.
#[local] Instance custom_pair (n : nat) :
  GenSizedSuchThat (nat * nat) (fun '(a,b) => Sums a b n) :=
  {| arbitrarySizeST := fun _ => returnGen (Some (n,0)) |}.
Inductive HasSum10 : (nat * nat) -> Prop :=
| MkHasSum10 : forall x y, Sums x y 10 -> HasSum10 (x,y).
Derive Inductive Schedule HasSum10 0 derive "Gen" opt "true".
Fail Check GenSizedSuchThat_Sums_OOI.
Goal True.
  let body := eval unfold GenSizedSuchThat_HasSum10_O in GenSizedSuchThat_HasSum10_O in
  lazymatch body with
  | context [custom_pair _] => exact I
  | _ => fail "Expected the supplied pair generator"
  end.
Qed.

(* Explicit class parameters of a relation remain instance arguments. *)
Inductive InstanceRel (A : Type) `{Dec_Eq A} : A -> nat -> Prop :=
| MkInstanceRel : forall x, InstanceRel A x 0.
Derive Inductive Schedule InstanceRel 3 derive "Gen" opt "true".
Definition instance_param_generic (A : Type) `{Dec_Eq A} (x : A) :
  GenSizedSuchThat nat (fun n => InstanceRel A x n) := ltac:(typeclasses eauto).
Definition implicit_relation_dictionary (A : Type) `{Dec_Eq A} (x : A) :
  GenSizedSuchThat nat (fun n => InstanceRel A x n) :=
  GenSizedSuchThat_InstanceRel_IIIO_instance x.
