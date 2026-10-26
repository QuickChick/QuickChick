From QuickChick Require Import QuickChick.

(* The new public dispatcher accepts unsized dictionaries without adding a
   global reverse conversion instance. *)
Inductive boundary (A B : Type) := Boundary : A -> B -> boundary A B.
Arguments Boundary {A B} _ _.
QuickChick Derive (GenSized, EnumSized) for boundary.
Definition gen_boundary {A B : Type} `{Gen A} `{Gen B} : GenSized (boundary A B) :=
  GenSizedboundary.
Definition enum_boundary {A B : Type} `{Enum A} `{Enum B} : EnumSized (boundary A B) :=
  EnumSizedboundary.
Definition named_method {A B : Type} `{Gen A} `{Gen B} : nat -> G (boundary A B) :=
  arbitrarySized_impl_boundary.
Fail Definition no_reverse_generator {A : Type} `{Gen A} : GenSized A :=
  ltac:(typeclasses eauto).
Fail Definition no_reverse_enumerator {A : Type} `{Enum A} : EnumSized A :=
  ltac:(typeclasses eauto).

(* A scheduled helper can already exist when the public command is invoked. *)
Inductive collision_box (A : Type) := CollisionBox : A -> collision_box A.
Derive Inductive Schedule collision_box derive "Gen" opt "false".
QuickChick Derive GenSized for collision_box.
QuickChick Derive GenSized for collision_box.
Check GenSizedcollision_box0.

(* Output positions include implicit type arguments, which are not outputs. *)
Inductive related {A B : Type} : A -> B -> Prop := Related : forall x y, related x y.
QuickChick Derive Checker for (@related A B x y).
QuickChick Derive Generator for (fun (y : B) => @related A B x y).
Definition inferred_generator {A B : Type} `{Gen B} (x : A) :
  GenSizedSuchThat B (fun y => related x y) := GenSizedSuchThatrelated x.
Definition inferred_checker {A B : Type} (x : A) (y : B) : DecOpt (related x y) :=
  DecOptrelated x y.
QuickChick Derive Enumerator for (fun y => related x y).
Definition inferred_enumerator {A B : Type} `{Enum B} (x : A) :
  EnumSizedSuchThat B (fun y => related x y) := EnumSizedSuchThatrelated x.

(* The legacy engine remains explicitly available without importing bare Derive. *)
Inductive old_box (A : Type) := OldBox : A -> old_box A.
Arguments OldBox {A} _.
QuickChick Derive Legacy GenSized for old_box.
DeriveLegacy EnumSized for old_box.
Definition legacy_generation {A : Type} `{Gen A} : GenSized (old_box A) := GenSizedold_box.
Definition legacy_enumeration {A : Type} `{Enum A} : EnumSized (old_box A) := EnumSizedold_box.

Class Verdict (A : Type) := { verdict : bool }.
Inductive leaf_check {A : Type} : A -> Prop := LeafCheck : forall x, leaf_check x.
#[local] Instance supplied_checker {A : Type} `{Verdict A} (x : A) : DecOpt (leaf_check x) :=
  {| decOpt := fun _ => Some verdict |}.
Inductive check_parent {A B : Type} : A -> B -> Prop :=
| CheckParent : forall x y, leaf_check (cons x nil, y) -> check_parent x y.
QuickChick Derive DecOpt for (@check_parent A B x y).
Definition checker_requirement {A B : Type} `{Verdict (list A * B)} (x : A) (y : B) :
  DecOpt (check_parent x y) := DecOptcheck_parent x y.
Fail Definition checker_missing {A B : Type} (x : A) (y : B) :
  DecOpt (check_parent x y) := ltac:(typeclasses eauto).
#[local] Instance false_verdict : Verdict (list nat * bool) := {| verdict := false |}.
Example uses_supplied_checker : decOpt (P := check_parent 0 true) 4 = Some false.
Proof. reflexivity. Qed.
Fail Check DecOpt_leaf_check_II.
QuickChick Derive Checker for (check_parent x y).
Check DecOptcheck_parent0.

(* Old checker dispatch is available through both deprecated spellings. *)
Inductive old_check : bool -> Prop := OldCheck : old_check true.
QuickChick Derive Legacy DecOpt for (old_check b).
DeriveLegacy Checker for (old_check b).
Example old_checker_still_works : decOpt (P := old_check false) 3 = Some false.
Proof. reflexivity. Qed.

Inductive pair_relation {A B : Type} : A -> B -> Prop :=
| PairRelation : forall x y, pair_relation x y.
QuickChick Derive Generator for (fun p => let '(x,y) := p in @pair_relation A B x y).
Definition pair_outputs {A B : Type} `{Gen A} `{Gen B} :
  GenSizedSuchThat (A * B) (fun '(x,y) => pair_relation x y) := GenSizedSuchThatpair_relation.
QuickChick Derive Enumerator for (fun '(x,y) => @pair_relation A B x y).
Definition pair_enumeration {A B : Type} `{Enum A} `{Enum B} :
  EnumSizedSuchThat (A * B) (fun '(x,y) => pair_relation x y) := EnumSizedSuchThatpair_relation.

Set Universe Polymorphism.
Inductive public_poly@{u} (A : Type@{u}) := PublicPoly : A -> public_poly A.
QuickChick Derive GenSized for public_poly.
Check GenSizedpublic_poly@{Set}.
Unset Universe Polymorphism.

Inductive mutual_left (A : Type) :=
| MutualLeaf : A -> mutual_left A
| MutualLeft : mutual_right A -> mutual_left A
with mutual_right (A : Type) :=
| MutualRightLeaf : A -> mutual_right A
| MutualRight : mutual_left A -> mutual_right A.
QuickChick Derive (GenSized, EnumSized) for mutual_left.
Definition right_gen {A : Type} `{Gen A} : GenSized (mutual_right A) := GenSizedmutual_right.
Definition right_enum {A : Type} `{Enum A} : EnumSized (mutual_right A) := EnumSizedmutual_right.

(* Fixed and repeated inputs use the instance derived for distinct input
   variables, which matches them by unification. *)
Inductive input_guard : nat -> nat -> Prop := InputGuard : forall x, input_guard x (S x).
QuickChick Derive Checker for (input_guard 0 y).
Example fixed_input_checks : @decOpt (input_guard 0 1) _ 5 = Some true.
Proof. reflexivity. Qed.
Example fixed_input_rejects : @decOpt (input_guard 0 2) _ 5 = Some false.
Proof. reflexivity. Qed.
QuickChick Derive Checker for (input_guard x x).
Example repeated_input_rejects : @decOpt (input_guard 3 3) _ 5 = Some false.
Proof. reflexivity. Qed.

From QuickChick Require Import LazyList.

(* Outputs requested out of predicate order are served by the instance in
   predicate order, through a second instance typed as the request. *)
QuickChick Derive Generator for (fun '(y, x) => input_guard x y).
Definition reordered_gen : GenSizedSuchThat _ (fun '(y, x) => input_guard x y) := _.
QuickChick Derive Enumerator for (fun '(y, x) => input_guard x y).
Definition reordered_enum : EnumSizedSuchThat _ (fun '(y, x) => input_guard x y) := _.
Example reordered_pairs :
  List.map (option_map (fun '(y, x) => (y, x)))
    (LazyList_to_list (Enumerators.run
      (@enumSizeST _ (fun '(y, x) => input_guard x y) _ 2) 2))
  = List.map (option_map (fun '(x, y) => (y, x)))
    (LazyList_to_list (Enumerators.run
      (@enumSizeST _ (fun '(x, y) => input_guard x y) _ 2) 2)).
Proof. reflexivity. Qed.
(* The class predicate takes one tupled argument, so curried outputs are
   declared at the tupled form. *)
QuickChick Derive Enumerator for (fun y x => input_guard x y).
Definition curried_reordered : EnumSizedSuchThat _ (fun '(y, x) => input_guard x y) := _.

Example reordered_satisfies :
  List.forallb (fun o => match o with Some (y, x) => Nat.eqb y (S x) | None => true end)
    (LazyList_to_list (Enumerators.run
      (@enumSizeST _ (fun '(y, x) => input_guard x y) _ 2) 2)) = true.
Proof. reflexivity. Qed.

(* Public checker/generator wrappers carry enumeration requirements through
   two dependency levels, without inventing a generator for the checker. *)
From QuickChick Require Import LazyList.
Inductive public_enum_box (A : Type) := PublicEnumBox : A -> public_enum_box A.
QuickChick Derive EnumSized for public_enum_box.
Inductive PublicAccepts (A : Type) : A -> public_enum_box A -> Prop :=
| PublicAcceptsAny : forall x y, PublicAccepts A x y.
#[local] Instance public_accepts_checker (A : Type) (x : A) (y : public_enum_box A) :
  DecOpt (PublicAccepts A x y) := {| decOpt := fun _ => Some true |}.
Inductive PublicWitness (A : Type) : A -> Prop :=
| PublicWitnessIntro : forall x y, PublicAccepts A x y -> PublicWitness A x.
QuickChick Derive DecOpt for (PublicWitness A x).
Definition public_witness_generic {A : Type} `{Enum A} (x : A) :
  DecOpt (PublicWitness A x) := DecOptPublicWitness x.
Fail Definition public_witness_missing {A : Type} `{Gen A} (x : A) :
  DecOpt (PublicWitness A x) := ltac:(typeclasses eauto).
Inductive PublicNoWitness (A : Type) : A -> Prop :=
| PublicNoWitnessIntro : forall x, ~ PublicWitness A x -> PublicNoWitness A x.
QuickChick Derive Generator for (fun x => PublicNoWitness A x).
Definition public_chain {A : Type} `{Gen A} `{Enum A} :
  GenSizedSuchThat A (fun x => PublicNoWitness A x) := GenSizedSuchThatPublicNoWitness.
Fail Definition public_chain_missing {A : Type} `{Gen A} :
  GenSizedSuchThat A (fun x => PublicNoWitness A x) := ltac:(typeclasses eauto).
Definition public_empty_enum : Enum bool := {| enum := MkEnum (fun _ => lnil) |}.
Definition public_single_enum : Enum bool := {| enum := returnEnum true |}.
Example public_empty_has_no_witness :
  @decOpt (PublicWitness bool false) (@DecOptPublicWitness bool false public_empty_enum) 3 = Some false.
Proof. reflexivity. Qed.
Example public_single_has_witness :
  @decOpt (PublicWitness bool false) (@DecOptPublicWitness bool false public_single_enum) 3 = Some true.
Proof. reflexivity. Qed.

(* An output that occurs more than once or inside a term would have to
   satisfy an equation; the command reports it as unsupported. *)
Fail QuickChick Derive Generator for (fun x => input_guard x x).
Fail QuickChick Derive Generator for (fun x => input_guard (S x) 3).
