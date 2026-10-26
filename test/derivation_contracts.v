From QuickChick Require Import QuickChick.

(* These are public contracts to preserve when switching QuickChick Derive's engine.
   A Gen-only dictionary is enough for the current sized derivation. *)
Inductive api_box (A : Type) := ApiBox : A -> api_box A.
Arguments ApiBox {A} _.
QuickChick Derive GenSized for api_box.
Definition gen_only {A : Type} `{Gen A} : GenSized (api_box A) := GenSizedapi_box.
QuickChick Derive EnumSized for api_box.
Definition enum_only {A : Type} `{Enum A} : EnumSized (api_box A) := EnumSizedapi_box.

(* Explicit commands currently permit repeating a derivation, with fresh names. *)
QuickChick Derive GenSized for api_box.
Check GenSizedapi_box0.

(* Named defaults and aliases are used by existing consumers. *)
Inductive api_relation : bool -> Prop := ApiRelation : api_relation true.
QuickChick Derive Checker for (api_relation b).
Definition named_checker (b : bool) : DecOpt (api_relation b) := DecOptapi_relation b.
QuickChick Derive Generator for (fun b => api_relation b).
Definition named_generator : GenSizedSuchThat bool (fun b => api_relation b) :=
  GenSizedSuchThatapi_relation.
Example checker_false : decOpt (P := api_relation false) 3 = Some false.
Proof. reflexivity. Qed.
